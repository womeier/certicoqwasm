Unset Universe Checking. (* maybe https://github.com/DeepSpec/InteractionTrees/issues/254 *)

From Wasm Require Import datatypes.

From CertiCoq Require Import LambdaANF.toplevel.
Require Import Common.Common Common.compM Common.Pipeline_utils.
Require Import ExtLib.Structures.Monad.
From MetaCoq.Template Require Import bytestring MCString.
From Coq Require Import ZArith List.

Require Import MSets.MSetAVL.
Require Import FMapAVL.
Require Import POrderedType.


Require Import LambdaANF.cps LambdaANF.cps_show CodegenWASM.wasm.

Import MonadNotation.

Module S_pos := MSetAVL.Make Positive_as_OT.
Module S_string := MSetAVL.Make StringOT.

Require Import CodegenWASM.my_map.
Definition M := partial_map nat. (* string -> nat *)
(* TODO: map from standard library *)
(* Module M := FMapAVL.Make StringOT. *)

(* TODO: map var/fn ids to new ids instead of string intermediate *)
Definition var_env := M.    (* maps variable names to their id *)
Definition fname_env := M.  (* maps function names to their id *)


(* ***** UTILS and BASIC TRANSLATIONS ****** *)

(* generates list of n arguments *)
Fixpoint arg_list (n : nat) : list (immediate * value_type) :=
  match n with
  | 0 => []
  | S n' => arg_list n' ++ [(n', T_i32)]
  end.

Definition nat_to_i32 (n : nat) :=
  VAL_int32 (Wasm_int.Int32.repr (BinInt.Z.of_nat n)).

Definition translate_var_to_string (nenv : name_env) (v : cps.var) : string :=
  "$" ++ show_tree (show_var nenv v).

Definition lookup_local_var (name : string) (venv : var_env) (err : string) : error immediate :=
  match venv name with
  | Some n => Ret n
  | None => Err ("expected to find id for variable " ++ name ++ " in var mapping: " ++ err)
  end.

Definition translate_var (nenv : name_env) (venv : var_env) (v : cps.var) (err_location : string): error immediate :=
  let name := translate_var_to_string nenv v in
  lookup_local_var name venv err_location.

Definition lookup_function_var (name : string) (fenv : fname_env) (err : string): error immediate :=
  match (fenv name) with
  | Some n => Ret n
  | None => Err err
  end.

Definition translate_function_var (nenv : name_env) (fenv : fname_env) (v : cps.var) : error immediate :=
  let x := translate_var_to_string nenv v in
  lookup_function_var x fenv ("expected to find id for variable " ++ x ++ " in function mapping").


(* ***** IMPORTED FUNCTIONS ****** *)
Definition write_char_function_name := "$write_char".
Definition write_char_function_var : immediate := 0.
Definition write_int_function_name := "$write_int".
Definition write_int_function_var : immediate := 1.


(* ***** GENERATE ALLOCATOR FUNCTIONS FOR CONSTRUCTORS ****** *)

Definition global_mem_ptr : immediate := 0.

Definition constr_alloc_function_name (tg : ctor_tag) : string :=
  "$alloc_constr_" ++ string_of_nat (Pos.to_nat tg).

(* Example placement of constructors in the linear memory:
     data Bintree := Leaf | Node Bintree Value Bintree

     Leaf: --> +---+
               |T_l|
               +---+

     Node: --> +---+---+---+---+
               |T_n| L | V | R |
               +---+---+---+---+
    T_l, T_n unique constructor tags
    L, V, R pointers to linear memory
*)

Fixpoint collect_constr_tags' (e : exp) {struct e} : S_pos.t :=
  match e with
  | Efun fds e' => S_pos.union (collect_constr_tags' e')
          ((fix iter (fds : fundefs) : S_pos.t :=
            match fds with
            | Fnil => S_pos.empty
            | Fcons _ _ _ e'' fds' =>
                S_pos.union (collect_constr_tags' e'') (iter fds')
            end) fds)
  | Econstr _ tg _ e' => S_pos.add tg (collect_constr_tags' e')
  | Ecase _ arms => fold_left (fun _s a => S_pos.union _s (S_pos.add (fst a) (collect_constr_tags' (snd a)))) arms S_pos.empty
  | Eproj _ _ _ _ e' => collect_constr_tags' e'
  | Eletapp _ _ _ _ e' => collect_constr_tags' e'
  | Eprim _ _ _ e' => collect_constr_tags' e'
  | Eprim_val _ _ e' => collect_constr_tags' e'
  | Eapp _ _ _ => S_pos.empty
  | Ehalt _ => S_pos.empty
  end.

Definition collect_constr_tags (e : exp) : list ctor_tag :=
  S_pos.elements (collect_constr_tags' e).

(* generates function that takes the arguments of a constructor
  and allocates a record in the linear memory *)
Definition generate_constr_alloc_function (cenv : ctor_env) (fenv : fname_env) (c : ctor_tag) : error wasm_function :=
  let ctor_id := Pos.to_nat c in
  num_args <- (match M.get c cenv with
               | Some {| ctor_arity := n |} => Ret (N.to_nat n)
               | _ => Err "found constructor without ctor_arity set"
               end : error immediate) ;;
  let return_var := (num_args : immediate) in (* 1st local var idx after args *)
  let args := arg_list num_args in
  let body :=
         [ BI_get_global global_mem_ptr
         ; BI_set_local return_var

         ; BI_get_global global_mem_ptr
         ; BI_const (nat_to_i32 ctor_id)
         ; BI_store T_i32 None (N_of_nat 2) (N_of_nat 0) (* 0: offset, 2: 4-byte aligned, alignment irrelevant for semantics *)
         ; BI_get_global global_mem_ptr
         ; BI_const (nat_to_i32 4)
         ; BI_binop T_i32 (Binop_i BOI_add)
         ; BI_set_global global_mem_ptr
         ] ++ (* store argument pointers in memory *)
         (flat_map (fun arg =>
             [ BI_get_global global_mem_ptr
             ; BI_get_local (fst arg)
             ; BI_store T_i32 None (N_of_nat 2) (N_of_nat 0) (* 0: offset, 2: 4-byte aligned, alignment irrelevant for semantics *)
             ; BI_get_global global_mem_ptr
             ; BI_const (nat_to_i32 4)
             ; BI_binop T_i32 (Binop_i BOI_add)
             ; BI_set_global global_mem_ptr
             ]
           ) args)
         ++
         [ BI_get_local return_var  (* "ptr to beginning of memory segment" *)
         ; BI_return
         ]
  in

  let fn_name := constr_alloc_function_name c in
  fn_var <- lookup_function_var fn_name fenv ("generate constr alloc: " ++ fn_name)%bs ;;

  Ret {| name := fn_var
       ; export_name := fn_name
       ; args := args
       ; ret_type := Some T_i32
       ; locals := [(return_var, T_i32)]
       ; body := body
       |}.


(* ***** GENERATE PRETTY PRINTER FUNCTION FOR CONSTRUCTOR-S-EXPRESSIONS ****** *)

Definition constr_pp_function_name : string :=
  "$pretty_print_constructor".

Definition instr_write_string (s : string) : list basic_instruction :=
  let fix to_ascii_list s' :=
    match s' with
    | String.EmptyString => []
    | String.String b s'' => Byte.to_nat b :: to_ascii_list s''
    end in
  flat_map (fun c => [BI_const (nat_to_i32 c); BI_call write_char_function_var]) (to_ascii_list s).

(* prints constructors as S-expressions *)
Definition generate_constr_pp_function (cenv : ctor_env) (fenv : fname_env) (tags : list ctor_tag) : error wasm_function :=
  let constr_ptr := 0 in
  let tmp := 1 in
  self_fn_var <- lookup_function_var constr_pp_function_name fenv "generate constr pp fn" ;;

  let fix gen_rec_calls (calls : nat) (arity : nat) : list basic_instruction :=
    match calls with
    | 0 => if arity =? 0 then [ BI_return ] else (instr_write_string ")") ++ [ BI_return ]
    | S calls' => [ BI_get_local tmp
                  ; BI_const (nat_to_i32 4)
                  ; BI_binop T_i32 (Binop_i BOI_add)
                  ; BI_set_local tmp
                  ; BI_get_local tmp
                  ; BI_load T_i32 None (N_of_nat 2) (N_of_nat 0) (* 0: offset, 2: 4-byte aligned, alignment irrelevant for semantics *)
                  ; BI_call self_fn_var
                  ] ++ (gen_rec_calls calls' arity)
    end in

  let gen_print_constr_block (c : ctor_tag) : error (list basic_instruction) :=
    let ctor_id := Pos.to_nat c in
    let ctor_name := show_tree (show_con cenv c) in

    ctor_arity <- (match M.get c cenv with
                  | Some {| ctor_arity := n |} => Ret (N.to_nat n)
                  | _ => Err "found constructor without ctor_arity set"
                  end) ;;

    Ret [ BI_const (nat_to_i32 ctor_id)
        ; BI_get_local constr_ptr
        ; BI_load T_i32 None (N_of_nat 2) (N_of_nat 0) (* 0: offset, 2: 4-byte aligned, alignment irrelevant for semantics *)
        ; BI_relop T_i32 (Relop_i ROI_eq)
        ; BI_if (Tf nil nil)
                ((instr_write_string " ") ++ (if ctor_arity =? 0 then [ BI_nop ] else (instr_write_string "(")) ++ instr_write_string ctor_name ++
                 [ BI_get_local constr_ptr
                 ; BI_set_local tmp
                 ] ++ gen_rec_calls ctor_arity ctor_arity)

                [ BI_nop ]
        ]
  in
  blocks <- sequence (map gen_print_constr_block tags) ;;

  let body := (concat blocks) ++
              (instr_write_string " <can't print constr: ") ++ (* e.g. could be fn-pointer or env-pointer *)
              [ BI_get_local constr_ptr
              ; BI_call write_int_function_var
              ] ++ instr_write_string ">" in

  let _ := ")"  (* hack to fix syntax highlighting bug *)

  in
  Ret {| name := self_fn_var
       ; export_name := constr_pp_function_name
       ; args := [(constr_ptr, T_i32)]
       ; ret_type := None
       ; locals := [(tmp, T_i32)]
       ; body := body
       |}.


(* ***** GENERATE INDIRECTION FUNCTIONS FOR INDIRECT FUNCTION CALLS ****** *)

Record func_signature :=
  { s_name : string
  ; s_tag : fun_tag           (* TODO: look up: for type? *)
  ; s_arg_types : list value_type
  ; s_ret_type : option value_type
  }.

Definition indirection_function_name (arg_types : list value_type) (ret_type : option value_type) : string :=
  let arg_types' := fold_left (fun _s a => _s ++ type_show a ++ "_")%bs arg_types "" in
  let ret_type' := match ret_type with None => "nothing" | Some t => type_show t end
  in
  "$indirect_" ++ arg_types' ++ "ret_" ++ ret_type'.

Definition is_function_name (fenv : fname_env) (v : string) : bool :=
  match fenv v with
  | Some _ => true
  | None => false
  end.

(* it is expected that all fns should have the same type *)
Definition generate_indirection_function (fns : list func_signature) (fenv : fname_env) : error wasm_function :=
  sig_head <- match hd_error fns with Some x => Ret x | None => Err "gen ind function: got empty list" end ;;

  let arg_types := sig_head.(s_arg_types) in
  let ret_type := sig_head.(s_ret_type) in

  let args := arg_list (length arg_types) in
  let id_var := length arg_types in

  let check_id sig :=
    f_var <- lookup_function_var sig.(s_name) fenv "indirection call check_id" ;;
    Ret [ BI_get_local id_var
        ; BI_const (nat_to_i32 f_var)
        ; BI_relop T_i32 (Relop_i ROI_eq)
        ; BI_if (Tf nil nil)
                ((map (fun arg => BI_get_local (fst arg)) args) ++
                 [ BI_call f_var
                 ; BI_return
                 ])
                [ BI_nop ]
        ]
  in

  checks <- sequence (map check_id fns) ;;

  let body := concat checks ++ [ BI_unreachable ] in

  let fn_name := indirection_function_name arg_types ret_type in
  fn_var <- lookup_function_var fn_name fenv "gen indirection function";;

  Ret {| name := fn_var
       ; export_name := fn_name
       ; args := args ++ [(id_var, T_i32)]
       ; ret_type := ret_type
       ; locals := []
       ; body := body
       |}.

Definition unique_indirection_function_names (sigs : list func_signature) : list string :=
  let fix aux (selected : S_string.t) (candidates : list func_signature) : S_string.t :=
          match candidates with
          | [] => selected
          | s :: cand' => aux (S_string.add (indirection_function_name s.(s_arg_types) s.(s_ret_type)) selected) cand'
          end
    in (S_string.elements (aux S_string.empty sigs)).

(* TODO: rename *)
Fixpoint select_sigs_by_type (sigs : list func_signature) (indirection_name : string) : list func_signature :=
  match sigs with
  | [] => []
  | s :: sigs' =>
      let ind_name := indirection_function_name s.(s_arg_types) (Some T_i32) in  (* Some T_i32, see comment in translate_call function *)
                if String.eqb ind_name indirection_name (* TODO: slow, compare types directly, tg *)
                  then s :: (select_sigs_by_type sigs' indirection_name)
                  else select_sigs_by_type sigs' indirection_name
  end.


Definition generate_indirection_functions (sigs : list func_signature) (fenv : fname_env) : error (list wasm_function) :=
  let indirection_fn_names := unique_indirection_function_names sigs in
  let sigs_one_type := map (select_sigs_by_type sigs) indirection_fn_names in
  let ind_fns := map (fun fns => generate_indirection_function fns fenv) sigs_one_type in (* list (error function) *)
  sequence ind_fns.

(* TODO check usage, this should probably be used at more places than is currently the case *)
Definition translate_local_var_read (nenv : name_env) (venv : var_env) (fenv : fname_env) (v : cps.var) : error (list basic_instruction) :=
  let var_name := translate_var_to_string nenv v in
  if is_function_name fenv var_name
    then var <- lookup_function_var var_name fenv "translate local var read: obtaining function id" ;;
         Ret [ BI_const (nat_to_i32 var) ] (* passing id of function <var_name> *)

    else var <- lookup_local_var var_name venv "translate_local_var_read: normal var";;
         Ret [ BI_get_local var ].


(* ***** TRANSLATE FUNCTION CALLS ****** *)

Definition translate_call (nenv : name_env) (venv : var_env) (fenv : fname_env) (f : cps.var) (args : list cps.var) : error (list basic_instruction) :=
  params <- sequence (map (fun p => translate_var nenv venv p "translate_call params") args);;
  let instr_pass_params := map (fun par => BI_get_local par) params in
  let arg_types := map (fun _ => T_i32) args in (* TODO limitation: only T_i32, there is no type information available anymore *)
  let f_var_string := translate_var_to_string nenv f
  in
  if is_function_name fenv f_var_string
    then f_var <- lookup_function_var f_var_string fenv "direct function call";;
         Ret (instr_pass_params ++ [ BI_call f_var ])

    else f_var <- lookup_local_var f_var_string venv ("translate ind. call from var: " ++ f_var_string);;
         ind_fn_var <- lookup_function_var (indirection_function_name arg_types (Some T_i32)) fenv "translate call, ind function" ;;
         Ret ( instr_pass_params ++
               [ BI_get_local f_var (* function tag is last parameter *)
               ; BI_call ind_fn_var
               ]).


(* ***** TRANSLATE EXPRESSIONS (except fundefs) ****** *)

Fixpoint translate_exp (nenv : name_env) (cenv : ctor_env) (venv: var_env) (fenv : fname_env) (e : exp) : error (list basic_instruction) :=
   match e with
   | Efun fundefs e' => Err "unexpected nested function definition"
   | Econstr x tg ys e' =>
      following_instr <- translate_exp nenv cenv venv fenv e' ;;
      x_var <- translate_var nenv venv x "translate_exp constr";;
      instr_params_read <- sequence (map (translate_local_var_read nenv venv fenv) ys);;
      alloc_fn_var <- lookup_function_var (constr_alloc_function_name tg) fenv "translate exp: econstr" ;;

      Ret ( concat instr_params_read ++
            [ BI_call alloc_fn_var
            ; BI_set_local x_var
            ] ++ following_instr)

   | Ecase x arms =>
     let if_blocks : list (error (list basic_instruction)) :=
     (map (fun (arm : ctor_tag * exp) =>
       let (a, e') := arm in
       let ctor_id := Pos.to_nat a in
       let ctor_name := show_tree (show_con cenv a) in

       then_instr <- translate_exp nenv cenv venv fenv e';;
       x_var <- translate_var nenv venv x "translate_exp case";;

       Ret [ BI_get_local x_var
           ; BI_load T_i32 None (N_of_nat 2) (N_of_nat 0) (* 0: offset, 2: 4-byte aligned, alignment irrelevant for semantics *)
           ; BI_const (nat_to_i32 ctor_id)
           ; BI_relop T_i32 (Relop_i ROI_eq)
           ; BI_if (Tf nil nil) then_instr [ BI_nop ]
           ]
      ) arms) in

      instructions <- sequence if_blocks ;;
      Ret ((concat instructions) ++ [ BI_unreachable ])  (* result of match isn't bound, doesn't return *)

   | Eproj x tg n y e' =>
      following_instr <- translate_exp nenv cenv venv fenv e' ;;
       y_var <- translate_var nenv venv y "translate_exp proj y";;
       x_var <- translate_var nenv venv x "translate_exp proj x";;

      Ret ([ BI_get_local y_var
           ; BI_const (nat_to_i32 (4 * ((N.to_nat n) + 1))) (* skip ctor_id and previous constr arguments *)
           ; BI_binop T_i32 (Binop_i BOI_add)
           ; BI_load T_i32 None (N_of_nat 2) (N_of_nat 0) (* 0: offset, 2: 4-byte aligned, alignment irrelevant for semantics *)
           ; BI_set_local x_var
           ] ++ following_instr)

   | Eletapp x f ft ys e' =>
     following_instr <- (translate_exp nenv cenv venv fenv e' : error (list basic_instruction)) ;;
     x_var <- translate_var nenv venv x "translate_exp app";;
     instr_call <- translate_call nenv venv fenv f ys ;;

     Ret (instr_call ++
          [ BI_set_local x_var
          ] ++ following_instr)

   | Eapp f ft ys => (* wasm doesn't treat tail call in a special way at the time *)
     instr_call <- translate_call nenv venv fenv f ys ;;

     Ret (instr_call ++ [ BI_return ]) (* tail calls are not supported yet in wasm. return result in ordinary way.  *)

   | Eprim_val x p e' => Err "translating prim_val to WASM not supported yet"
   | Eprim x p ys e' => Err "translating prim to WASM not supported yet"
   | Ehalt x =>
     x_var <- translate_var nenv venv x "translate_exp halt";;
     Ret [ BI_get_local x_var; BI_return ]
   end.


(* ***** TRANSLATE FUNCTIONS ****** *)

(* unique, vars are only assign once *)
Fixpoint collect_local_variables (e : exp) {struct e} : list cps.var :=
  match e with
  | Efun _ e' => collect_local_variables e'
  | Econstr x _ _ e' => x :: collect_local_variables e'
  | Ecase _ arms => flat_map (fun a => collect_local_variables (snd a)) arms
  | Eproj x _ _ _ e' => x :: collect_local_variables e'
  | Eletapp x _ _ _ e' => x :: collect_local_variables e'
  | Eprim x _ _ e' => x :: collect_local_variables e'
  | Eprim_val x _ e' => x :: collect_local_variables e'
  | Eapp _ _ _ => []
  | Ehalt _ => []
  end.

(* locals should be unique *)
Definition create_local_variable_mapping (nenv : name_env) (fenv : fname_env) (locals : list cps.var) (initial : var_env) : var_env :=
  let fix aux (start_id : nat) (locals : list cps.var) (venv : var_env) :=
    match locals with
    | [] => initial
    | v :: l' => let mapping := aux (1 + start_id) l' venv in
                 let v_str := translate_var_to_string nenv v in
                 update mapping v_str start_id
    end in
  aux 0 locals initial.

Definition translate_function (nenv : name_env) (cenv : ctor_env) (fenv : fname_env)
                              (name : cps.var) (args : list cps.var) (body : exp) : error wasm_function :=
  let local_vars := collect_local_variables body in
  let var_env := create_local_variable_mapping nenv fenv (args ++ local_vars) empty in
  body_res <- translate_exp nenv cenv var_env fenv body ;;
  args   <- sequence (map (fun p => v <- translate_var nenv var_env p "translate_function";; Ret (v, T_i32)) args);;
  locals <- sequence (map (fun p => v <- translate_var nenv var_env p "translate_function";; Ret (v, T_i32)) local_vars);;

  let fn_name := translate_var_to_string nenv name in
  fn_var <- lookup_function_var fn_name fenv "translate function" ;;

  Ret
  {| name := fn_var
   ; export_name := fn_name
   ; args := args
   ; ret_type := Some T_i32
   ; locals := locals
   ; body := body_res
   |}.


(* ***** GENERATE FUNCTION THAT RETURNS THE MEMORY USED SO FAR ****** *)
Definition get_memory_usage_function_name := "$get_memory_usage_in_bytes".

Definition get_memory_usage_function (fenv : fname_env) : error wasm_function :=
  var <- lookup_function_var get_memory_usage_function_name fenv "mem usage fn" ;;
  Ret {| name := var
       ; export_name := get_memory_usage_function_name
       ; args := []
       ; ret_type := Some T_i32
       ; locals := []
       ; body := [ BI_get_global global_mem_ptr; BI_return ]
       |}.


(* ***** MAIN: GENERATE COMPLETE WASM_MODULE FROM lambdaANF EXP ****** *)
Definition main_function_name := "$main_function".

Definition collect_function_signatures (nenv : name_env) (e : exp) : error (list func_signature) :=
  match e with
  | Efun fds exp => (* fundefs only allowed here (uppermost level) *)
    (fix iter (fds : fundefs) : error (list func_signature) :=
        match fds with
        | Fnil => Ret []
        | Fcons x tg xs e fds' =>
            let var_name := translate_var_to_string nenv x in
            following <- iter fds' ;;
            Ret ({| s_name := var_name
                  ; s_tag := tg
                  ; s_arg_types := map (fun _ => T_i32) xs
                  ; s_ret_type := Some T_i32
                  |} :: following)
        end) fds
  | _ => Ret []
  end.

Fixpoint add_to_fname_mapping (names : list string) (start_id : nat) (initial : fname_env) : fname_env :=
  match names with
  | [] => initial
  | n :: names' => update (add_to_fname_mapping names' (1 + start_id) initial) n start_id
  end.

(* maps function names to ids (id=index in function list of module) *)
Definition create_fname_mapping (nenv : name_env) (e : exp) : error fname_env :=
  let (fname_mapping, num_fns) := (add_to_fname_mapping [write_char_function_name; write_int_function_name] 0 empty, 2) in

  let fun_names :=
    match e with
    | Efun fds exp => (* fundefs only allowed here (uppermost level) *)
      (fix iter (fds : fundefs) : list string :=
          match fds with
          | Fnil => []
          | Fcons x _ _ _ fds' => (translate_var_to_string nenv x) :: (iter fds')
          end) fds
    | _ => []
  end in
  let (fname_mapping, num_fns) := (add_to_fname_mapping fun_names num_fns fname_mapping, num_fns + length fun_names) in

  let constr_tags := collect_constr_tags e in
  let constr_alloc_fnames := map constr_alloc_function_name constr_tags in
  let (fname_mapping, num_fns) := (add_to_fname_mapping constr_alloc_fnames num_fns fname_mapping, num_fns + length constr_alloc_fnames) in

  let (fname_mapping, num_fns) := (add_to_fname_mapping [constr_pp_function_name] num_fns fname_mapping, num_fns + 1) in

  fsigs <- collect_function_signatures nenv e;;
  let indirection_fn_names := unique_indirection_function_names fsigs in
  let (fname_mapping, num_fns) := (add_to_fname_mapping indirection_fn_names num_fns fname_mapping, num_fns + length indirection_fn_names) in

  let (fname_mapping, num_fns) := (add_to_fname_mapping [get_memory_usage_function_name] num_fns fname_mapping, num_fns + 1) in

  let (fname_mapping, num_fns) := (add_to_fname_mapping [main_function_name] num_fns fname_mapping, num_fns + 1) in

  Ret fname_mapping.


Definition LambdaANF_to_WASM (nenv : name_env) (cenv : ctor_env) (e : exp) : error wasm_module :=
  fname_mapping <- create_fname_mapping nenv e ;;

  let constr_tags := collect_constr_tags e in
  constr_alloc_functions <-
    sequence (map (generate_constr_alloc_function cenv fname_mapping) constr_tags) ;;

  constr_pp_function <- generate_constr_pp_function cenv fname_mapping constr_tags ;;

  fsigs <- collect_function_signatures nenv e ;;
  indirection_functions <- generate_indirection_functions fsigs fname_mapping;;

  let main_expr := match e with
                   | Efun _ exp => exp
                   | _ => e
                   end in
  fns <-
    match e with
    | Efun fds exp => (* fundefs only allowed here (uppermost level) *)
      (fix iter (fds : fundefs) : error (list wasm_function) :=
          match fds with
          | Fnil => Ret []
          | Fcons x tg xs e fds' =>
             fn <- translate_function nenv cenv fname_mapping x xs e ;;
             following <- iter fds' ;;
             Ret (fn :: following)
          end) fds
    | _ => Ret []
  end ;;

  let main_vars := collect_local_variables main_expr in
  let main_venv := create_local_variable_mapping nenv fname_mapping main_vars empty in
  locals <- sequence (map (fun p => v <- translate_var nenv main_venv p "main locals";; Ret (v, T_i32)) main_vars);;

  main_instr <- translate_exp nenv cenv main_venv fname_mapping main_expr ;;
  main_function_var <- lookup_function_var main_function_name fname_mapping "main function";;

  mem_usage_function <- get_memory_usage_function fname_mapping;;

  let main_function := {| name := main_function_var
                        ; export_name := main_function_name
                        ; args := []
                        ; ret_type := Some T_i32
                        ; locals := locals
                        ; body := main_instr
                        |} in

  Ret {| memory := 100 * 100 (* KB, multiplication: hack to avoid extraction error *)
       ; functions := fns ++ constr_alloc_functions ++ [constr_pp_function] ++ indirection_functions ++ [mem_usage_function; main_function]
       ; global_vars := [(global_mem_ptr, T_i32, 0)]
       ; function_imports := [ ("env", write_char_function_var, write_char_function_name, [T_i32])
                             ; ("env", write_int_function_var, write_int_function_name, [T_i32])
                             ]
       ; comment := "constructors: " ++ (fold_left (fun _s p => _s ++ string_of_nat (Pos.to_nat p) ++ ", ")%bs (collect_constr_tags e) "")
       |}.
