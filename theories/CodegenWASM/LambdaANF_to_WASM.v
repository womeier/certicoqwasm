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

(* currently: all? functions have return type i32 *)
(* TODO: most vars i32 for now, need i64? *)

Module S_pos := MSetAVL.Make Positive_as_OT.
Module S_string := MSetAVL.Make StringOT.

Require Import CodegenWASM.my_map.
Definition M := partial_map nat.
(* TODO: map from standard library *)
(* Module M := FMapAVL.Make StringOT. *)

(* ***** UTILS and BASIC TRANSLATIONS ****** *)

(* generates list of n arguments named $arg{i} *)
Fixpoint arg_list (n : nat) : list (var * type) :=
  match n with
  | 0 => []
  | S n' => arg_list n' ++ [(Generic ("$arg" ++ string_of_nat n'), I32)]
  end.

Definition translate_var (nenv : name_env) (v : cps.var) : var :=
  Generic ("$" ++ show_tree (show_var nenv v)).

(* ***** IMPORTED FUNCTIONS ****** *)
Definition write_char := Generic "$write_char".
Definition write_int := Generic "$write_int".

(* ***** GENERATE ALLOCATOR FUNCTIONS FOR CONSTRUCTORS ****** *)

Definition global_mem_ptr := Generic "$ptr".

Definition constr_alloc_function_name (tg : ctor_tag) : var :=
  Generic ("$alloc_constr_" ++ string_of_nat (Pos.to_nat tg)).

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
Definition generate_constr_alloc_function (cenv : ctor_env) (c : ctor_tag) : error wasm_function :=
  let ctor_id := string_of_nat (Pos.to_nat c) in
  let ctor_name := show_tree (show_con cenv c) in
  let return_var := Generic "$ret_pointer" in

  num_args <- (match M.get c cenv with
               | Some {| ctor_arity := n |} => Ret (N.to_nat n)
               | _ => Err "found constructor without ctor_arity set"
               end) ;;
  let args := arg_list num_args in
  let body :=
         [ WI_comment ("constructor: " ++ ctor_name)
         ; WI_comment "save ret pointer"
         ; WI_global_get global_mem_ptr
         ; WI_local_set return_var

         ; WI_comment "store constr id"
         ; WI_global_get global_mem_ptr
         ; WI_const (Generic (ctor_id)) I32
         ; WI_store I32
         ; WI_global_get global_mem_ptr
         ; WI_const (Generic "4") I32
         ; WI_add I32
         ; WI_global_set global_mem_ptr
         ] ++ (* store argument pointers in memory *)
         (flat_map (fun arg =>
             [ WI_comment ("store " ++ var_show (fst arg) ++ " in memory")
             ; WI_global_get global_mem_ptr
             ; WI_local_get (fst arg)
             ; WI_store I32
             ; WI_global_get global_mem_ptr
             ; WI_const (Generic "4") I32
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
  Ret {| name := constr_alloc_function_name c
       ; export := true
       ; args := arg_list num_args
       ; ret_type := Some I32
       ; locals := [(return_var, I32)]
       ; body := body
       |}.

(* ***** GENERATE PRETTY PRINTER FUNCTION FOR CONSTRUCTOR-S-EXPRESSIONS ****** *)

Definition constr_pp_function_name : var :=
  Generic "$pretty_print_constructor".

Definition instr_write_string (s : string) : list wasm_instr :=
  let fix to_ascii_list s' :=
    match s' with
    | String.EmptyString => []
    | String.String b s'' => Byte.to_nat b :: to_ascii_list s''
    end in
  (WI_comment ("write: " ++ s) :: flat_map (fun c => [WI_const (Generic (string_of_nat c)) I32; WI_call write_char]) (to_ascii_list s)).

(* prints constructors as S-expressions *)
Definition generate_constr_pp_function (cenv : ctor_env) (tags : list ctor_tag) : error wasm_function :=
  let constr_ptr := Generic "$constr_ptr" in
  let tmp := Generic "$constr_ptr_tmp" in

  let fix gen_rec_calls (calls : nat) (arity : nat) : list wasm_instr :=
    match calls with
    | 0 => if arity =? 0 then [WI_return] else (instr_write_string ")") ++ [WI_return]
    | S calls' => [ WI_local_get tmp
                  ; WI_const (Generic "4") I32
                  ; WI_add I32
                  ; WI_local_set tmp
                  ; WI_local_get tmp
                  ; WI_load I32
                  ; WI_call constr_pp_function_name
                  ] ++ (gen_rec_calls calls' arity)
    end in

  let gen_print_constr_block (c : ctor_tag) : error (list wasm_instr) :=
    let ctor_id := string_of_nat (Pos.to_nat c) in
    let ctor_name := show_tree (show_con cenv c) in

    ctor_arity <- (match M.get c cenv with
                  | Some {| ctor_arity := n |} => Ret (N.to_nat n)
                  | _ => Err "found constructor without ctor_arity set"
                  end) ;;

    Ret [ WI_comment (ctor_id ++ ": " ++ ctor_name)
        ; WI_const (Generic ctor_id) I32
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
              ; WI_call write_int
              ] ++ instr_write_string ">"
  in
  Ret {| name := constr_pp_function_name
       ; export := true
       ; args := [(constr_ptr, I32)]
       ; ret_type := None
       ; locals := [(tmp, I32)]
       ; body := body
       |}.

(* ***** GENERATE INDIRECTION FUNCTIONS FOR INDIRECT FUNCTION CALLS ****** *)

Record func_signature :=
  { s_name : var
  ; s_id : nat                (* unique function id, used for indirection *)
  ; s_tag : fun_tag           (* TODO: look up: for type? *)
  ; s_arg_types : list type
  ; s_ret_type : option type
  }.

Definition indirection_function_name (arg_types : list type) (ret_type : option type) : string := (* injective *)
  let arg_types' := fold_left (fun _s a => _s ++ type_show a ++ "_")%bs arg_types "" in
  let ret_type' := match ret_type with None => "nothing" | Some t => type_show t end
  in
  "$indirect_" ++ arg_types' ++ "ret_" ++ ret_type'.

Definition indirection_function_var (arg_types : list type) (ret_type : option type) : var :=
  Generic (indirection_function_name arg_types ret_type).

Fixpoint var_references_function (nenv : name_env) (fsigs : list func_signature) (v : var) : option func_signature :=
  match fsigs with
  | [] => None  (* standard variable *)
  | sig :: names' => if var_eqb v sig.(s_name)
                   then Some sig
                   else var_references_function nenv names' v
  end.

(* it is expected that all fns should have the same type *)
Definition generate_indirection_function (fns : list func_signature) : option wasm_function :=
  sig_head <- hd_error fns ;;

  let arg_types := sig_head.(s_arg_types) in
  let ret_type := sig_head.(s_ret_type) in

  let id_var := Generic "$id" in
  let args := arg_list (length arg_types) in

  let check_id sig := [ WI_local_get id_var
                      ; WI_const (Generic (string_of_nat (sig.(s_id)))) I32
                      ; WI_eq I32
                      ; WI_if ((map (fun arg => WI_local_get (fst arg)) args) ++
                               [ WI_call sig.(s_name)
                               ; WI_return
                               ])
                              [ WI_nop ]
                      ] in

  let body := (flat_map check_id fns) ++
              [ WI_comment "when unexpected function id"
              ; WI_unreachable
              ]

  in
  Some {| name := indirection_function_var arg_types ret_type
        ; export := true
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
                if String.eqb ind_name indirection_name
                  then s :: (select_sigs_by_type sigs' indirection_name)
                  else select_sigs_by_type sigs' indirection_name
  end.


Definition generate_indirection_functions (sigs : list func_signature): list wasm_function :=
  let indirection_fn_names := unique_indirection_function_names sigs in
  let sigs_one_type := map (select_sigs_by_type sigs) indirection_fn_names in
  flat_map (fun fns => (match generate_indirection_function fns with
                        | None => []
                        | Some f => [f]
                        end)) sigs_one_type.

(* TODO check usage, this should probably be used at more places than is currently the case *)
Definition translate_local_var_read (nenv : name_env) (fsigs : list func_signature) (v : var) : list wasm_instr :=
  match var_references_function nenv fsigs v with
  | None => [ WI_local_get v ]
  | Some sig => [ WI_comment ("passing tag for function " ++ var_show sig.(s_name))
                ; WI_const (Generic (string_of_nat (sig.(s_id)))) I32
                ]
  end.


(* ***** TRANSLATE FUNCTION CALLS ****** *)

Definition translate_call (nenv : name_env) (fsigs : list func_signature) (f : var) (args : list cps.var) : list wasm_instr :=
  let instr_pass_params := WI_comment "pushing func parameters on stack" ::
                           map (fun a => WI_local_get (translate_var nenv a)) args in
  let arg_types := map (fun _ => I32) args (* TODO limitation: only I32, there is no type information available anymore *)
  in
  match var_references_function nenv fsigs f with
  | Some _ => instr_pass_params ++ [ WI_call f ] (* direct call *)
  | None => instr_pass_params ++
            [ WI_comment ("indirect call to: " ++ var_show f) (* indirect call *)
            ; WI_local_get f (* function tag is last parameter *)
            ; WI_call (indirection_function_var arg_types (Some I32))  (* currently: indirection function names end *)
            ]                                                          (* with "ret_i32" even for ones without return type TODO*)
  end.


(* ***** TRANSLATE EXPRESSIONS (except fundefs) ****** *)

(* the return value of an instruction is pushed on the stack *)
Fixpoint translate_exp (nenv : name_env) (cenv : ctor_env) (fsigs : list func_signature) (e : exp) : error (list wasm_instr) :=
   match e with
   | Efun fundefs e' => Err "unexpected nested function definition"
   | Econstr x tg ys e' =>
      following_instr <- translate_exp nenv cenv fsigs e' ;;

      Ret (WI_comment ("econstr: " ++ show_tree (show_var nenv x)) ::
            (flat_map (fun y => translate_local_var_read nenv fsigs (translate_var nenv y)) ys) ++
            [ WI_call (constr_alloc_function_name tg)
            ; WI_local_set (translate_var nenv x)
            ] ++ following_instr)

   | Ecase x arms =>
     let if_blocks : list (error (list wasm_instr)) :=
     (map (fun (arm : ctor_tag * exp) =>
       let (a, e') := arm in
       let ctor_id := string_of_nat (Pos.to_nat a) in
       let ctor_name := show_tree (show_con cenv a) in

       then_instr <- translate_exp nenv cenv fsigs e';;

       Ret [ WI_comment ("ecase: " ++ show_tree (show_var nenv x) ++ ", " ++ ctor_name)
           ; WI_local_get (translate_var nenv x)
           ; WI_load I32
           ; WI_const (Generic (ctor_id)) I32
           ; WI_eq I32
           ; WI_if then_instr [ WI_nop ]
           ]
      ) arms) in

      instructions <- sequence if_blocks ;;
      Ret ((concat instructions) ++ [ WI_comment "no matching clause for case analysis" (* result of match isn't bound, doesn't return *)
                                    ; WI_unreachable
                                    ])
   | Eproj x tg n y e' =>
      following_instr <- translate_exp nenv cenv fsigs e' ;;

      Ret ([ WI_comment "proj"
           ; WI_local_get (translate_var nenv y)
           ; WI_const (Generic (string_of_nat (4 * ((N.to_nat n) + 1)))) I32  (* skip ctor_id and previous constr arguments *)
           ; WI_add I32
           ; WI_load I32
           ; WI_local_set (translate_var nenv x)
           ] ++ following_instr)

   | Eletapp x f ft ys e' =>
     following_instr <- (translate_exp nenv cenv fsigs e' : error (list wasm_instr)) ;;

     Ret ((WI_comment ("letapp, ftag: " ++ (show_tree (show_var nenv f)) ++ ", " ++ (show_tree (show_ftag true ft)))%bs) ::
          (translate_call nenv fsigs (translate_var nenv f) ys) ++
          [ WI_local_set (translate_var nenv x)
          ] ++ following_instr)

   | Eapp f ft ys => (* wasm doesn't treat tail call in a special way at the time *)

     Ret ((WI_comment ("app, ftag: " ++ (show_tree (show_ftag true ft)))) ::
          (translate_call nenv fsigs (translate_var nenv f) ys) ++
          [ WI_comment "tail calls not supported yet in wasm. return result in ordinary way."
          ; WI_return
          ])

   | Eprim_val x p e' => Err "translating prim_val to WASM not supported yet"
   | Eprim x p ys e' => Err "translating prim to WASM not supported yet"
   | Ehalt x => Ret [ WI_local_get (translate_var nenv x); WI_return ]
   end.


(* ***** TRANSLATE FUNCTIONS ****** *)

(* TODO: unique? *)
Fixpoint collect_local_variables' (nenv : name_env) (e : exp) {struct e} : list cps.var :=
  match e with
  | Efun _ e' => collect_local_variables' nenv e'
  | Econstr x _ _ e' => x :: collect_local_variables' nenv e'
  | Ecase _ arms => flat_map (fun a => collect_local_variables' nenv (snd a)) arms
  | Eproj x _ _ _ e' => x :: collect_local_variables' nenv e'
  | Eletapp x _ _ _ e' => x :: collect_local_variables' nenv e'
  | Eprim x _ _ e' => x :: collect_local_variables' nenv e'
  | Eprim_val x _ e' => x :: collect_local_variables' nenv e'
  | Eapp _ _ _ => []
  | Ehalt _ => []
  end.

Definition collect_local_variables (nenv : name_env) (e : exp) : list (var * type) :=
  map (fun p => (translate_var nenv p, I32)) (collect_local_variables' nenv e).


Definition translate_function (nenv : name_env) (cenv : ctor_env) (fsigs : list func_signature)
                              (name : cps.var) (args : list cps.var) (body : exp) : error wasm_function :=
  body_res <- translate_exp nenv cenv fsigs body ;;
  Ret
  {| name := translate_var nenv name
   ; export := true
   ; args := map (fun p => (translate_var nenv p, I32)) args
   ; ret_type := Some I32
   ; locals := collect_local_variables nenv body
   ; body := body_res
   |}.


(* ***** MAIN: GENERATE COMPLETE WASM_MODULE FROM lambdaANF EXP ****** *)

(* maps function names to nats for indirect calls -> signature.s_id *)
Fixpoint create_function_name_mapping' (names : list string) (counter : nat) (m : M) : M :=
  match names with
  | [] => empty
  | n :: names' => update (create_function_name_mapping' names' (1 + counter) m) n counter
  end.

Definition LambdaANF_to_WASM (nenv : name_env) (cenv : ctor_env) (e : exp) : error wasm_module :=
  let fun_names :=
    match e with
    | Efun fds exp => (* fundefs only allowed here (uppermost level) *)
      (fix iter (fds : fundefs) : list string :=
          match fds with
          | Fnil => []
          | Fcons x _ _ _ fds' => (var_show (translate_var nenv x)) :: (iter fds')
          end) fds
    | _ => []
  end in

  let mapping := create_function_name_mapping' fun_names 0 empty in
  let option2error o : error nat := match o with | None => Err "function name mapping failed" | Some i => Ret i end in

  fsigs <- (* for translating indirect function calls *)
    (match e with
    | Efun fds exp => (* fundefs only allowed here (uppermost level) *)
      (fix iter (fds : fundefs) : error (list func_signature) :=
          match fds with
          | Fnil => Ret []
          | Fcons x tg xs e fds' =>
              let var := translate_var nenv x in
              s_id <- option2error (mapping (var_show var)) ;;
              following <- iter fds' ;;
              Ret ({| s_name := translate_var nenv x
                    ; s_id := s_id
                    ; s_tag := tg
                    ; s_arg_types := map (fun _ => I32) xs
                    ; s_ret_type := Some I32
                    |} :: following)
          end) fds
    | _ => Err "found unexpected fundef"
  end : error (list func_signature)) ;;

  let (fns, main_expr) :=
    match e with
    | Efun fds exp => (* fundefs only allowed here (uppermost level) *)
      ((fix iter (fds : fundefs) : list wasm_function :=
          match fds with
          | Fnil => []
          | Fcons x tg xs e fds' =>
              match translate_function nenv cenv fsigs x xs e with
              | Ret fn => fn :: (iter fds')
              (* TODO : pass on error*)
              | Err _ => []
              end
          end) fds, exp)
    | _ => ([], e)
  end in

  let indirection_functions := generate_indirection_functions fsigs in

  main_instr <- translate_exp nenv cenv fsigs main_expr ;;
  let main_function := {| name := Generic "$main_function"
                        ; export := true
                        ; args := []
                        ; ret_type := Some I32
                        ; locals := collect_local_variables nenv main_expr
                        ; body := main_instr
                        |} in

  let constr_tags := collect_constr_tags e in

  constr_alloc_functions <-
    sequence (map (generate_constr_alloc_function cenv) constr_tags) ;;

  constr_pp_function <- generate_constr_pp_function cenv constr_tags ;;

  Ret {| memory := Generic "10_000" (* KB*)
       ; functions := constr_alloc_functions ++ indirection_functions ++ fns ++ [constr_pp_function; main_function]
       ; global_vars := [(global_mem_ptr, I32, Generic "0")]
       ; function_imports := [ ("env", write_char, [I32])
                             ; ("env", write_int, [I32])
                             ]
       ; comment := "constructors: " ++ (fold_left (fun _s p => _s ++ string_of_nat (Pos.to_nat p) ++ ", ")%bs (collect_constr_tags e) "")
       |}.
