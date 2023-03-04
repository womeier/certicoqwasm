From Coq Require Import ZArith List.
From CertiCoq Require Import LambdaANF.toplevel.
Require Import Common.Common Common.compM Common.Pipeline_utils.
Require Import ExtLib.Structures.Monad.
From MetaCoq.Template Require Import bytestring MCString.

Require Import MSets.MSetAVL.
Require Import POrderedType.

Require Import LambdaANF.cps LambdaANF.cps_show CodegenWASM.wasm.

Import MonadNotation.

(* TODO: most vars i32 for now, need i64? *)
(* TODO: move to separate file *)

(*
(* Expressions [exp] of the LambdaANF language. *)
Inductive exp : Type :=
| Econstr: var -> ctor_tag -> list var -> exp -> exp
| Ecase: var -> list (ctor_tag * exp) -> exp
| Eproj: var -> ctor_tag -> N -> var -> exp -> exp
| Eletapp: var -> var -> fun_tag -> list var -> exp -> exp
| Efun: fundefs -> exp -> exp
| Eapp: var -> fun_tag -> list var -> exp
| Eprim_val : var -> primitive -> exp -> exp
| Eprim: var -> prim -> list var -> exp -> exp (* where prim is id *)
| Ehalt : var -> exp
with fundefs : Type :=
| Fcons: var -> fun_tag -> list var -> exp -> fundefs -> fundefs
| Fnil: fundefs.

*)

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

(* Enumerate items starting from 0. *)
(* TODO: move to utils file *)
Definition enumerate_nat {A : Type} (xs : list A) : list (nat * A) :=
  let fix aux (n : nat) (xs : list A) :=
          match xs with
          | nil => nil
          | x :: xs => (n, x) :: aux (S n) xs
          end
    in aux 0 xs.

Fixpoint zip {A B : Type} (l1 : list A) (l2 : list B) : option (list (A * B)) :=
  match l1, l2 with
  | [], [] => Some []
  | x::l1', y::l2' => l <- zip l1' l2' ;; Some ((x, y) :: l)
  | _, _ => None
  end.

Record func_signature :=
  { s_name : var
  ; s_tag : fun_tag
  ; s_args : list (var * type)
  ; s_ret_type : option type
  }.

Definition indirect_call_redirect_function_name (arg_types : list type) (ret_type : option type) : var :=
  let arg_types' := fold_left (fun _s a => _s ++ type_show a ++ "_") arg_types "" in
  let ret_type' := match ret_type with None => "nothing" | Some t => type_show t end
  in
  Generic ("$indirect_" ++ arg_types' ++ "ret_" ++ ret_type').

Definition constr_alloc_function_name (tg : ctor_tag) : var := 
  Generic ("$alloc_constr_" ++ string_of_nat (Pos.to_nat tg)).

Definition global_mem_ptr := Generic "$ptr".

Definition translate_var (nenv : name_env) (v : cps.var) : var :=
  Generic ("$" ++ show_tree (show_var nenv v)).

Fixpoint var_references_function (nenv : name_env) (fsigs : list func_signature) (v : var) : option func_signature :=
  match fsigs with
  | [] => None  (* standard variable *)
  | sig :: names' => if var_eqb v sig.(s_name)
                   then Some sig
                   else var_references_function nenv names' v
  end.

Definition translate_call (nenv : name_env) (fsigs : list func_signature) (f : var) (args : list cps.var) (ret : bool) : wasm_instr :=
  let instr_pass_params := WI_comment "pushing func parameters on stack" ::
                           map (fun a => WI_local_get (translate_var nenv a)) args in
  let arg_types := map (fun _ => I32) args (* TODO limitation: only I32, there is no type information available anymore *)
  in
  match var_references_function nenv fsigs f with
  | Some _ => WI_block (instr_pass_params ++
                        [ WI_call f
                        ]) (* direct call *)
  | None => WI_block (instr_pass_params ++
                      [ WI_comment ("indirect call to: " ++ var_show f) (* indirect call *)
                      ; WI_local_get f (* function tag is last parameter *) 
                      ; WI_call (indirect_call_redirect_function_name arg_types (if ret then Some I32 else None))
                      ])
  end.

(* all fns should have the same type *)
Definition generate_redirect_function (fns : list func_signature) : option wasm_function :=
  sig_head <- hd_error fns ;;

  let arg_types := map snd sig_head.(s_args) in
  let ret_type := sig_head.(s_ret_type) in

  let tag_var := Generic "$tag" in
  let args := (map (fun t => (Generic ("$arg" ++ string_of_nat (fst t)), I32)) (enumerate_nat arg_types)) in

  let check_tag := (fun sig => WI_block [ WI_local_get tag_var
                                        ; WI_const (Generic (string_of_nat (Pos.to_nat sig.(s_tag)))) I32
                                        ; WI_eq I32
                                        ; WI_if (WI_block (List.app (map (fun arg => WI_local_get (fst arg)) args) [WI_call sig.(s_name)]))
                                                WI_nop
                                        ]) in

  let body := WI_block ((map check_tag fns) ++ [ WI_comment "when unexpected function tag"; WI_unreachable ])
                     
  in
  Some {| name := indirect_call_redirect_function_name arg_types ret_type
        ; export := true
        ; args := List.app args [(tag_var, I32)]
        ; ret_type := ret_type
        ; locals := []
        ; body := body
        |}.

Definition unique_types (sigs : list func_signature) : list (list type * option type) := 
  map (fun s => (map snd s.(s_args), s.(s_ret_type))) sigs.
(*  let fix aux (selected : list func_signature) (candidates : list func_signature) :=
          match candidates with
          | [] => selected
          | s :: xs => (n, x) :: aux (S n) xs
          end
    in aux [] sigs.*)

Fixpoint select_sigs_by_type (sigs : list func_signature) (t : list type * option type) : list func_signature :=
  match sigs with
  | [] => []
  | s :: sigs' => if (andb (match s.(s_ret_type), (snd t) with
                            | None, None => true
                            | Some t1, Some t2 => type_eqb t1 t2
                            | _, _ => false
                            end)
                            (match (zip (fst t) (map snd s.(s_args))) with
                            | None => false
                            | Some l => forallb type_eqb_uncurried l
                            end))
                  then s :: (select_sigs_by_type sigs' t)
                  else select_sigs_by_type sigs' t
  end.


Definition generate_redirect_functions (sigs : list func_signature): list wasm_function :=
  let types := unique_types sigs in
  let sigs_one_type := map (select_sigs_by_type sigs) types in
  flat_map (fun fns => (match generate_redirect_function fns with
                        | None => []
                        | Some f => [f]
                        end)) sigs_one_type.

(* TODO check usage*)
Definition translate_local_var_read (nenv : name_env) (fsigs : list func_signature) (v : var) : wasm_instr :=
  match var_references_function nenv fsigs v with
  | None => WI_local_get v
  | Some sig => WI_block [ WI_comment ("passing tag for function " ++ var_show sig.(s_name))
                         ; WI_const (Generic (string_of_nat (Pos.to_nat sig.(s_tag)))) I32
                         ]
  end.

(* translate all expressions (except fundefs)

  the return value of an instruction is pushed on the stack
*)
Fixpoint translate_exp (nenv : name_env) (cenv : ctor_env) (fsigs : list func_signature) (e : exp) : error wasm_instr :=
   match e with
   | Efun fundefs e' => Err "unexpected nested function definition"
   | Econstr x tg ys e' => 
      following_instr <- translate_exp nenv cenv fsigs e' ;;
                         Ret (WI_block
                                (WI_comment ("econstr: " ++ show_tree (show_var nenv x)) ::
                                (map (fun y => translate_local_var_read nenv fsigs (translate_var nenv y)) ys) ++
                                [ WI_call (constr_alloc_function_name tg)
                                ; WI_local_set (translate_var nenv x)
                                ; following_instr
                                ]))
   | Ecase x arms =>
     let if_blocks : list (error wasm_instr) :=
     (map (fun (arm : ctor_tag * exp) =>
       let (a, e') := arm in
       let ctor_id := string_of_nat (Pos.to_nat a) in
       let ctor_name := show_tree (show_con cenv a) in

       then_instr <- translate_exp nenv cenv fsigs e';;

       Ret (WI_block
                [ WI_comment ("ecase: " ++ show_tree (show_var nenv x) ++ ", " ++ ctor_name)
                ; WI_local_get (translate_var nenv x)
                ; WI_load I32
                ; WI_const (Generic (ctor_id)) I32
                ; WI_eq I32
                ; WI_if then_instr WI_nop
                ])
      ) arms) in 

      instructions <- sequence if_blocks ;;
      Ret (WI_block (instructions ++ [ WI_comment "no matching clause for case analysis" (* result of match isn't bound, doesn't return *)
                                     ; WI_unreachable
                                     ]))
   | Eproj x tg n y e' => 
      following_instr <- translate_exp nenv cenv fsigs e' ;;
      
      Ret (WI_block [ WI_comment "proj"
                    ; WI_local_get (translate_var nenv y)
                    ; WI_const (Generic (string_of_nat (4 * ((N.to_nat n) + 1)))) I32  (* skip ctor_id and previous constr arguments *)
                    ; WI_add I32
                    ; WI_load I32
                    ; WI_local_set (translate_var nenv x)
                    ; WI_comment ""
                    ; following_instr
                    ])
   | Eletapp x f ft ys e' => 
     following_instr <- translate_exp nenv cenv fsigs e' ;;

     Ret (WI_block ((WI_comment ("letapp, ftag: " ++ (show_tree (show_var nenv f)) ++ ", " ++ (show_tree (show_ftag true ft)))) ::
                    [ translate_call nenv fsigs (translate_var nenv f) ys true  (* true: function returns *)
                    ; WI_local_set (translate_var nenv x)
                    ; following_instr
                    ]))

   | Eapp f ft ys => (* wasm doesn't treat tail call in a special way at the time *)

     Ret (WI_block ((WI_comment ("app, ftag: " ++ (show_tree (show_ftag true ft)))) ::
                    [ translate_call nenv fsigs (translate_var nenv f) ys false (* false: function doesn't return *)
                    ; WI_comment "tail calls not supported yet in wasm. won't return"
                    ; WI_unreachable
                    ]))

   | Eprim_val x p e' => Err "translating prim_val to WASM not supported yet"
   | Eprim x p ys e' => Err "translating prim to WASM not supported yet"
   | Ehalt x => Ret (WI_block [ WI_local_get (translate_var nenv x); WI_return ])
   end.

Fixpoint collect_local_variables' (nenv : name_env) (e : exp) {struct e} : list cps.var :=
  match e with
  | Efun _ e' => collect_local_variables' nenv e'
  | Econstr x _ _ e' => x :: collect_local_variables' nenv e'
  | Ecase _ arms => List.concat (map (fun a => collect_local_variables' nenv (snd a)) arms)
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

Module S := Make Positive_as_OT.

Fixpoint collect_constr_tags' (e : exp) {struct e} : S.t :=
  match e with
  | Efun fds e' => S.union (collect_constr_tags' e')
          ((fix iter (fds : fundefs) : S.t :=
            match fds with
            | Fnil => S.empty
            | Fcons _ _ _ e'' fds' =>
                S.union (collect_constr_tags' e'') (iter fds')
            end) fds)
  | Econstr _ tg _ e' => S.add tg (collect_constr_tags' e')
  | Ecase _ arms => fold_left (fun _s a => S.union _s (S.add (fst a) (collect_constr_tags' (snd a)))) arms S.empty
  | Eproj _ _ _ _ e' => collect_constr_tags' e'
  | Eletapp _ _ _ _ e' => collect_constr_tags' e'
  | Eprim _ _ _ e' => collect_constr_tags' e'
  | Eprim_val _ _ e' => collect_constr_tags' e'
  | Eapp _ _ _ => S.empty
  | Ehalt _ => S.empty
  end.

Definition collect_constr_tags (e : exp) : list ctor_tag :=
  S.elements (collect_constr_tags' e).

(* cenv : Map[ctor_tag -> rec]:

{ ctor_name     : name    (* the name of the constructor *)
; ctor_ind_name : name    (* the name of its inductive type *)
; ctor_ind_tag  : ind_tag (* ind_tag of corresponding inductive type *)
; ctor_arity    : N       (* the arity of the constructor *)
; ctor_ordinal  : N       (* the [ctor_tag]s ordinal in inductive defn starting at zero *)
}.

*)

(* generates argument list for constructor with arity n*)
Fixpoint arg_list (n : nat) : list (var * type) :=
  match n with
  | 0 => []
  | S n' => arg_list n' ++ [(Generic ("$arg" ++ string_of_nat n'), I32)]
  end.

Definition generate_constr_alloc_function (cenv : ctor_env) (c : ctor_tag) : wasm_function :=
  let ctor_id := string_of_nat (Pos.to_nat c) in
  let ctor_name := show_tree (show_con cenv c) in
  let return_var := Generic "$ret_pointer" in
(*  let info :=
    (match M.get c cenv with
     | Some {| ctor_name := nNamed name
             ; ctor_ind_name := nNamed ind_name
             |} => "ind type: " ++ ind_name ++ ", constr name: " ++ name
     | _ => "error: didn't find information of constructor"
     end) in *)

  let args := arg_list
    (match M.get c cenv with 
     | Some {| ctor_arity := n |} => N.to_nat n
     | _ => 42 (*TODO: handle error*)
     end) in

  {| name := constr_alloc_function_name c
   ; export := true
   ; args := args
   ; ret_type := Some I32
   ; locals := [(return_var, I32)]
   ; body := WI_block
    ([ WI_comment ("constructor: " ++ ctor_name)
     ; WI_comment "save ret pointer"
     ; WI_global_get global_mem_ptr
     ; WI_local_set return_var

     ; WI_comment "store const id"
     ; WI_global_get global_mem_ptr
     ; WI_const (Generic (ctor_id)) I32
     ; WI_store I32
     ; WI_global_get global_mem_ptr
     ; WI_const (Generic "4") I32
     ; WI_add I32
     ; WI_global_set global_mem_ptr
     ] ++ (* store argument pointers in memory *)
       concat (map (fun arg =>
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
     ])
   |}.
(* generates for constr e a function that takes the arguments
  and allocates a record in the linear memory
*)

Definition LambdaANF_to_WASM (nenv : name_env) (cenv : ctor_env) (e : exp) : error wasm_module := 
  let fsigs := (* for translating indirect function calls *)
    match e with
    | Efun fds exp => (* fundefs only allowed here (uppermost level) *)
      (fix iter (fds : fundefs) :=
          match fds with
          | Fnil => []
          | Fcons x tg xs e fds' => 
              {| s_name := translate_var nenv x
               ; s_tag := tg
               ; s_args := map (fun a => (translate_var nenv a, I32)) xs
               ; s_ret_type := Some I32 (* TODO *)
               |} :: (iter fds')
          end) fds
    | _ => []
  end in

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

  let constr_alloc_functions :=
    map (generate_constr_alloc_function cenv) (collect_constr_tags e) in

  let indirect_call_redirect_functions := generate_redirect_functions fsigs in

  main_instr <- translate_exp nenv cenv fsigs main_expr ;;
  let main_function := {| name := Generic "$main_function"
                        ; export := true
                        ; args := []
                        ; ret_type := Some I32
                        ; locals := collect_local_variables nenv main_expr
                        ; body := main_instr
                        |} in
  Ret {| memory := Generic "100"
       ; functions := constr_alloc_functions ++ indirect_call_redirect_functions ++ fns ++ [main_function]
       ; global_vars := [(global_mem_ptr, I32, Generic "0")]
       ; comment := "constructors: " ++ (fold_left (fun _s p => _s ++ string_of_nat (Pos.to_nat p) ++ ", ") (collect_constr_tags e) "")
       |}.

Definition LambdaANF_to_WASM_Wrapper (prims : list (kername * string * bool * nat * positive)) (args : nat) (t : toplevel.LambdaANF_FullTerm) : error wasm_module * string :=
  let '(_, pr_env, cenv, ctag, itag, nenv, fenv, _, prog) := t in
  (LambdaANF_to_WASM nenv cenv prog, "").

Definition compile_LambdaANF_to_WASM (prims : list (kername * string * bool * nat * positive)) : CertiCoqTrans toplevel.LambdaANF_FullTerm wasm_module :=
  fun s =>
    debug_msg "Translating from LambdaANF to WASM" ;;
    opts <- get_options ;;
    let args := c_args opts in
    LiftErrorLogCertiCoqTrans "CodegenWASM" (LambdaANF_to_WASM_Wrapper prims args) s.
