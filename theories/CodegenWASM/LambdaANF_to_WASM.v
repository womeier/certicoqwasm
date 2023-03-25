Unset Universe Checking.

From CertiCoq Require Import LambdaANF.toplevel.
Require Import Common.Common Common.compM Common.Pipeline_utils.
Require Import ExtLib.Structures.Monad.
From MetaCoq.Template Require Import bytestring MCString.
From Coq Require Import ZArith List.

Require Import MSets.MSetAVL.
Require Import FMapAVL.
Require Import POrderedType.

From Wasm Require Import pp.


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
Fixpoint arg_list (n : nat) : list (var * type) :=
  match n with
  | 0 => []
  | S n' => arg_list n' ++ [(VNat n', I32)]
  end.

Definition translate_var_to_string (nenv : name_env) (v : cps.var) : string :=
  "$" ++ show_tree (show_var nenv v).

Definition lookup_local_var (name : string) (venv : var_env) (err : string) : error var :=
  match venv name with
  | Some n => Ret (VNat n)
  | None => Err ("expected to find id for variable " ++ name ++ " in var mapping: " ++ err)
  end.

Definition translate_var (nenv : name_env) (venv : var_env) (v : cps.var) (err_location : string): error var :=
  let name := translate_var_to_string nenv v in
  lookup_local_var name venv err_location.

Definition lookup_function_var (name : string) (fenv : fname_env) (err : string): error var :=
  match (fenv name) with
  | Some n => Ret (VNat n)
  | None => Err err
  end.

Definition translate_function_var (nenv : name_env) (fenv : fname_env) (v : cps.var) : error var :=
  let x := translate_var_to_string nenv v in
  lookup_function_var x fenv ("expected to find id for variable " ++ x ++ " in function mapping").

(* ***** IMPORTED FUNCTIONS ****** *)
Definition write_char_function_name := "$write_char".
Definition write_char_function_var := VNat 0.
Definition write_int_function_name := "$write_int".
Definition write_int_function_var := VNat 1.


(* ***** GENERATE ALLOCATOR FUNCTIONS FOR CONSTRUCTORS ****** *)

Definition global_mem_ptr := VNat 0.

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
  let ctor_name := show_tree (show_con cenv c) in
  num_args <- (match M.get c cenv with
               | Some {| ctor_arity := n |} => Ret (N.to_nat n)
               | _ => Err "found constructor without ctor_arity set"
               end) ;;
  let return_var := VNat num_args in
  let args := arg_list num_args in
  let body :=
         [ WI_comment ("constructor: " ++ ctor_name)
         ; WI_comment "save ret pointer"
         ; WI_global_get global_mem_ptr
         ; WI_local_set return_var

         ; WI_comment "store constr id"
         ; WI_global_get global_mem_ptr
         ; WI_const (VNat ctor_id) I32
         ; WI_store I32
         ; WI_global_get global_mem_ptr
         ; WI_const (VNat 4) I32
         ; WI_add I32
         ; WI_global_set global_mem_ptr
         ] ++ (* store argument pointers in memory *)
         (flat_map (fun arg =>
             [ WI_comment ("store param/var " ++ var_show (fst arg) ++ " in memory")
             ; WI_global_get global_mem_ptr
             ; WI_local_get (fst arg)
             ; WI_store I32
             ; WI_global_get global_mem_ptr
             ; WI_const (VNat 4) I32
             ; WI_add I32
             ; WI_global_set global_mem_ptr
             ]
           ) args)
         ++
         [ WI_comment "ptr to beginning of memory segment"
         ; WI_local_get return_var
         ; WI_return
         ]
  in

  let fn_name := constr_alloc_function_name c in
  fn_var <- lookup_function_var fn_name fenv ("generate constr alloc: " ++ fn_name)%bs ;;

  Ret {| name := fn_var
       ; export_name := fn_name
       ; args := args
       ; ret_type := Some I32
       ; locals := [(return_var, I32)]
       ; body := body
       |}.

(* ***** GENERATE PRETTY PRINTER FUNCTION FOR CONSTRUCTOR-S-EXPRESSIONS ****** *)

Definition constr_pp_function_name : string :=
  "$pretty_print_constructor".

Definition instr_write_string (s : string) : list wasm_instr :=
  let fix to_ascii_list s' :=
    match s' with
    | String.EmptyString => []
    | String.String b s'' => Byte.to_nat b :: to_ascii_list s''
    end in
  (WI_comment ("write: " ++ s) :: flat_map (fun c => [WI_const (VNat c) I32; WI_call write_char_function_var]) (to_ascii_list s)).

(* prints constructors as S-expressions *)
Definition generate_constr_pp_function (cenv : ctor_env) (fenv : fname_env) (tags : list ctor_tag) : error wasm_function :=
  let constr_ptr := VNat 0 in
  let tmp := VNat 1 in
  self_fn_var <- lookup_function_var constr_pp_function_name fenv "generate constr pp fn" ;;

  let fix gen_rec_calls (calls : nat) (arity : nat) : list wasm_instr :=
    match calls with
    | 0 => if arity =? 0 then [WI_return] else (instr_write_string ")") ++ [WI_return]
    | S calls' => [ WI_local_get tmp
                  ; WI_const (VNat 4) I32
                  ; WI_add I32
                  ; WI_local_set tmp
                  ; WI_local_get tmp
                  ; WI_load I32
                  ; WI_call self_fn_var
                  ] ++ (gen_rec_calls calls' arity)
    end in

  let gen_print_constr_block (c : ctor_tag) : error (list wasm_instr) :=
    let ctor_id := Pos.to_nat c in
    let ctor_name := show_tree (show_con cenv c) in

    ctor_arity <- (match M.get c cenv with
                  | Some {| ctor_arity := n |} => Ret (N.to_nat n)
                  | _ => Err "found constructor without ctor_arity set"
                  end) ;;

    Ret [ WI_comment (string_of_nat ctor_id ++ ": " ++ ctor_name)
        ; WI_const (VNat ctor_id) I32
        ; WI_local_get constr_ptr
        ; WI_load I32
        ; WI_eq I32
        ; WI_if (instr_write_string " " ++ (if ctor_arity =? 0 then [ WI_nop ] else (instr_write_string "(")) ++
                 instr_write_string ctor_name ++
                 [ WI_local_get constr_ptr
                 ; WI_local_set tmp
                 ] ++ gen_rec_calls ctor_arity ctor_arity)

                [ WI_nop ]
        ]
  in
  blocks <- sequence (map gen_print_constr_block tags) ;;

  let body := (WI_comment "printing s-exp for constructors" :: (concat blocks)) ++
              (instr_write_string " <can't print constr: ") ++ (* e.g. could be fn-pointer or env-pointer *)
              [ WI_local_get constr_ptr
              ; WI_call write_int_function_var
              ] ++ instr_write_string ">" in

  let _ := ")"  (* hack to fix syntax highlighting bug *)

  in
  Ret {| name := self_fn_var
       ; export_name := constr_pp_function_name
       ; args := [(constr_ptr, I32)]
       ; ret_type := None
       ; locals := [(tmp, I32)]
       ; body := body
       |}.

(* ***** GENERATE INDIRECTION FUNCTIONS FOR INDIRECT FUNCTION CALLS ****** *)

Record func_signature :=
  { s_name : string
  ; s_tag : fun_tag           (* TODO: look up: for type? *)
  ; s_arg_types : list type
  ; s_ret_type : option type
  }.

Definition indirection_function_name (arg_types : list type) (ret_type : option type) : string :=
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
  let id_var := VNat (length arg_types) in

  let check_id sig :=
    f_var <- lookup_function_var sig.(s_name) fenv "indirection call check_id" ;;
    Ret [ WI_local_get id_var
        ; WI_const f_var I32
        ; WI_eq I32
        ; WI_if ((map (fun arg => WI_local_get (fst arg)) args) ++
                 [ WI_call f_var
                 ; WI_return
                 ])
                [ WI_nop ]
        ]
  in

  checks <- sequence (map check_id fns) ;;

  let body := concat checks ++
              [ WI_comment "when unexpected function id"
              ; WI_unreachable
              ] in

  let fn_name := indirection_function_name arg_types ret_type in
  fn_var <- lookup_function_var fn_name fenv "gen indirection function";;

  Ret {| name := fn_var
       ; export_name := fn_name
       ; args := args ++ [(id_var, I32)]
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
      let ind_name := indirection_function_name s.(s_arg_types) (Some I32) in  (* Some I32, see comment in translate_call function *)
                if String.eqb ind_name indirection_name (* TODO: slow, compare types directly *)
                  then s :: (select_sigs_by_type sigs' indirection_name)
                  else select_sigs_by_type sigs' indirection_name
  end.


Definition generate_indirection_functions (sigs : list func_signature) (fenv : fname_env) : error (list wasm_function) :=
  let indirection_fn_names := unique_indirection_function_names sigs in
  let sigs_one_type := map (select_sigs_by_type sigs) indirection_fn_names in
  let ind_fns := map (fun fns => generate_indirection_function fns fenv) sigs_one_type in (* list (error function) *)
  sequence ind_fns.

(* TODO check usage, this should probably be used at more places than is currently the case *)
Definition translate_local_var_read (nenv : name_env) (venv : var_env) (fenv : fname_env) (v : cps.var) : error (list wasm_instr) :=
  let var_name := translate_var_to_string nenv v in
  if is_function_name fenv var_name
    then var <- lookup_function_var var_name fenv "translate local var read: obtaining function id" ;;
         Ret [ WI_comment ("passing id for function " ++ var_name)
             ; WI_const var I32
             ]
    else var <- lookup_local_var var_name venv "translate_local_var_read: normal var";;
         Ret [ WI_local_get var
             ].


(* ***** TRANSLATE FUNCTION CALLS ****** *)

Definition translate_call (nenv : name_env) (venv : var_env) (fenv : fname_env) (fsigs : list func_signature) (f : cps.var) (args : list cps.var) : error (list wasm_instr) :=
  params <- sequence (map (fun p => translate_var nenv venv p "translate_call params") args);;
  let instr_pass_params := map WI_local_get params in
  let arg_types := map (fun _ => I32) args in (* TODO limitation: only I32, there is no type information available anymore *)
  let f_var_string := translate_var_to_string nenv f
  in
  if is_function_name fenv f_var_string
    then f_var <- lookup_function_var f_var_string fenv "direct function call";;
         Ret ((WI_comment "pushing func parameters on stack") :: instr_pass_params ++
              [ WI_comment ("direct call to: " ++ f_var_string)
              ; WI_call f_var
              ])
    else f_var <- lookup_local_var f_var_string venv ("translate ind. call from var: " ++ f_var_string);;
         ind_fn_var <- lookup_function_var (indirection_function_name arg_types (Some I32)) fenv "translate call, ind function" ;;
         Ret ((WI_comment "pushing func parameters on stack") ::
               instr_pass_params ++
               [ WI_comment ("indirect call to: " ++ f_var_string)
               ; WI_local_get f_var (* function tag is last parameter *)
               ; WI_call ind_fn_var
               ]).

(* ***** TRANSLATE EXPRESSIONS (except fundefs) ****** *)

(* Definition translate_var (nenv : name_env) (venv : var_env) (v : cps.var) : error var := *)

Fixpoint translate_exp (nenv : name_env) (cenv : ctor_env) (venv: var_env) (fenv : fname_env) (fsigs : list func_signature) (e : exp) : error (list wasm_instr) :=
   match e with
   | Efun fundefs e' => Err "unexpected nested function definition"
   | Econstr x tg ys e' =>
      following_instr <- translate_exp nenv cenv venv fenv fsigs e' ;;
      x_var <- translate_var nenv venv x "translate_exp constr";;
      instr_params_read <- sequence (map (translate_local_var_read nenv venv fenv) ys);;
      alloc_fn_var <- lookup_function_var (constr_alloc_function_name tg) fenv "translate exp: econstr" ;;

      Ret (WI_comment ("econstr: " ++ show_tree (show_var nenv x)) ::
            concat instr_params_read ++
            [ WI_call alloc_fn_var
            ; WI_local_set x_var
            ] ++ following_instr)

   | Ecase x arms =>
     let if_blocks : list (error (list wasm_instr)) :=
     (map (fun (arm : ctor_tag * exp) =>
       let (a, e') := arm in
       let ctor_id := Pos.to_nat a in
       let ctor_name := show_tree (show_con cenv a) in

       then_instr <- translate_exp nenv cenv venv fenv fsigs e';;
       x_var <- translate_var nenv venv x "translate_exp case";;

       Ret [ WI_comment ("ecase: " ++ show_tree (show_var nenv x) ++ ", " ++ ctor_name)
           ; WI_local_get x_var
           ; WI_load I32
           ; WI_const (VNat ctor_id) I32
           ; WI_eq I32
           ; WI_if then_instr [ WI_nop ]
           ]
      ) arms) in

      instructions <- sequence if_blocks ;;
      Ret ((concat instructions) ++ [ WI_comment "no matching clause for case analysis" (* result of match isn't bound, doesn't return *)
                                    ; WI_unreachable
                                    ])
   | Eproj x tg n y e' =>
      following_instr <- translate_exp nenv cenv venv fenv fsigs e' ;;
       y_var <- translate_var nenv venv y "translate_exp proj y";;
       x_var <- translate_var nenv venv x "translate_exp proj x";;

      Ret ([ WI_comment "proj"
           ; WI_local_get y_var
           ; WI_const (VNat (4 * ((N.to_nat n) + 1))) I32  (* skip ctor_id and previous constr arguments *)
           ; WI_add I32
           ; WI_load I32
           ; WI_local_set x_var
           ] ++ following_instr)

   | Eletapp x f ft ys e' =>
     following_instr <- (translate_exp nenv cenv venv fenv fsigs e' : error (list wasm_instr)) ;;
     x_var <- translate_var nenv venv x "translate_exp app";;
     instr_call <- translate_call nenv venv fenv fsigs f ys ;;

     Ret ((WI_comment ("letapp: " ++ (show_tree (show_var nenv f)))) ::
          instr_call ++
          [ WI_local_set x_var
          ] ++ following_instr)

   | Eapp f ft ys => (* wasm doesn't treat tail call in a special way at the time *)
     instr_call <- translate_call nenv venv fenv fsigs f ys ;;

     Ret ((WI_comment ("app: " ++ (show_tree (show_var nenv f)))) ::
          instr_call ++
          [ WI_comment "tail calls not supported yet in wasm. return result in ordinary way."
          ; WI_return
          ])

   | Eprim_val x p e' => Err "translating prim_val to WASM not supported yet"
   | Eprim x p ys e' => Err "translating prim to WASM not supported yet"
   | Ehalt x =>
     x_var <- translate_var nenv venv x "translate_exp halt";;
     Ret [ WI_local_get x_var; WI_return ]
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

(*
Definition collect_local_variables (nenv : name_env) (e : exp) : list (var * type) :=
  map (fun p => (translate_var nenv p, I32)) (collect_local_variables' nenv e). *)

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

Definition translate_function (nenv : name_env) (cenv : ctor_env) (fenv : fname_env) (fsigs : list func_signature)
                              (name : cps.var) (args : list cps.var) (body : exp) : error wasm_function :=
  let local_vars := collect_local_variables body in
  let var_env := create_local_variable_mapping nenv fenv (args ++ local_vars) empty in
  body_res <- translate_exp nenv cenv var_env fenv fsigs body ;;
  args   <- sequence (map (fun p => v <- translate_var nenv var_env p "translate_function";; Ret (v, I32)) args);;
  locals <- sequence (map (fun p => v <- translate_var nenv var_env p "translate_function";; Ret (v, I32)) local_vars);;

  let fn_name := translate_var_to_string nenv name in
  fn_var <- lookup_function_var fn_name fenv "translate function" ;;

  Ret
  {| name := fn_var
   ; export_name := fn_name
   ; args := args
   ; ret_type := Some I32
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
       ; ret_type := Some I32
       ; locals := []
       ; body := [ WI_global_get global_mem_ptr; WI_return ]
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
                  ; s_arg_types := map (fun _ => I32) xs
                  ; s_ret_type := Some I32
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
  (* mapping function name strings to their id=index of function list in module, num_fns: starting idx for mapping additional functions TODO: stateMonad?
     - map write_char, write_int *)
  let (fname_mapping, num_fns) := (add_to_fname_mapping [write_char_function_name; write_int_function_name] 0 empty, 2) in

  (* - map function names from LambdaANF definitions *)
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

  (* - map names for constructor allocations *)
  let constr_alloc_fnames := map constr_alloc_function_name constr_tags in
  let (fname_mapping, num_fns) := (add_to_fname_mapping constr_alloc_fnames num_fns fname_mapping, num_fns + length constr_alloc_fnames) in

  (* - map name for constructor pretty print fn *)
  let (fname_mapping, num_fns) := (add_to_fname_mapping [constr_pp_function_name] num_fns fname_mapping, num_fns + 1) in

  (* - map names for indirection functions *)
  fsigs <- collect_function_signatures nenv e;;
  let indirection_fn_names := unique_indirection_function_names fsigs in
  let (fname_mapping, num_fns) := (add_to_fname_mapping indirection_fn_names num_fns fname_mapping, num_fns + length indirection_fn_names) in

  (* - map name for debug function to get memory usage *)
  let (fname_mapping, num_fns) := (add_to_fname_mapping [get_memory_usage_function_name] num_fns fname_mapping, num_fns + 1) in

  (* - map name for main function *)
  let (fname_mapping, num_fns) := (add_to_fname_mapping [main_function_name] num_fns fname_mapping, num_fns + 1) in

  Ret fname_mapping.


Definition LambdaANF_to_WASM (nenv : name_env) (cenv : ctor_env) (e : exp) : error wasm_module :=
  fname_mapping <- create_fname_mapping nenv e ;;

  let constr_tags := collect_constr_tags e in
  constr_alloc_functions <-
    sequence (map (generate_constr_alloc_function cenv fname_mapping) constr_tags) ;;

  constr_pp_function <- generate_constr_pp_function cenv fname_mapping constr_tags ;;

  fsigs <- collect_function_signatures nenv e ;; (* for translating indirect function calls *)

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
             fn <- translate_function nenv cenv fname_mapping fsigs x xs e ;;
             following <- iter fds' ;;
             Ret (fn :: following)
          end) fds
    | _ => Ret []
  end ;;

  let main_vars := collect_local_variables main_expr in
  let main_venv := create_local_variable_mapping nenv fname_mapping main_vars empty in
  locals <- sequence (map (fun p => v <- translate_var nenv main_venv p "main locals";; Ret (v, I32)) main_vars);;

  main_instr <- translate_exp nenv cenv main_venv fname_mapping fsigs main_expr ;;
  main_function_var <- lookup_function_var main_function_name fname_mapping "main function";;

  mem_usage_function <- get_memory_usage_function fname_mapping;;

  let main_function := {| name := main_function_var
                        ; export_name := main_function_name
                        ; args := []
                        ; ret_type := Some I32
                        ; locals := locals
                        ; body := main_instr
                        |} in

  Ret {| memory := VNat (100 * 100) (* KB, multiplication: hack to avoid extraction error *)
       ; functions := fns ++ constr_alloc_functions ++ [constr_pp_function] ++ indirection_functions ++ [mem_usage_function; main_function]
       ; global_vars := [(global_mem_ptr, I32, VNat 0)]
       ; function_imports := [ ("env", write_char_function_var, write_char_function_name, [I32])
                             ; ("env", write_int_function_var, write_int_function_name, [I32])
                             ]
       ; comment := "constructors: " ++ (fold_left (fun _s p => _s ++ string_of_nat (Pos.to_nat p) ++ ", ")%bs (collect_constr_tags e) "")
       |}.
