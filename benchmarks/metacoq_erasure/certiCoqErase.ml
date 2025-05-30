open Ast_quoter
open Tm_util
open Pp
open Universes0
open BasicAst
open Ast0
external certicoq_erase : ExtractedASTBaseQuoter.quoted_program -> unit = "certicoq_erase"

let msg_info s =
  let s = Caml_bytestring.caml_string_of_bytestring s in
  Feedback.msg_info (str s)
  
let _ = Callback.register "coq_msg_info" msg_info

let msg_debug s = 
  Feedback.msg_debug (str (Caml_bytestring.caml_string_of_bytestring s))
  
let _ = Callback.register "coq_msg_debug" msg_debug

(** The ML value representation of an erased quoted program does not directly match 
  the one expected by CertiCoq erase function as singleton inductive types are unboxed, 
  we use Obj.t surgery to transform the value. 
  
  This involves the transformation of universes sets, constraints sets and the representation
  of universe values.
  *)

let fix_set u =
  (* The representation of a proof object *)
  let proof_obj = Obj.magic 1 in
  let block = Obj.new_block 0 2 in
  Obj.set_field block 0 (Obj.magic u);
  Obj.set_field block 1 proof_obj;
  block

let fix_universe u =
  let open Universe in
  let proof_obj = Obj.magic 1 in
  let fix_ues ues : Obj.t = 
    let block = Obj.new_block 0 2 in
    Obj.set_field block 0 (Obj.magic ues);
    Obj.set_field block 1 proof_obj;
    block
  in
  let fix_neues neues : Obj.t = 
    let ues = fix_ues neues in
    let block = Obj.new_block 0 2 in
    Obj.set_field block 0 ues;
    Obj.set_field block 1 proof_obj;
    block
  in
  match u with 
  | Coq_lProp -> Coq_lProp
  | Coq_lSProp -> Coq_lSProp
  | Coq_lType neues -> Coq_lType (Obj.magic (fix_neues neues))

let fix_term (p : Ast0.term) : Ast0.term =
  let open List in
  let rec aux p = 
  match p with
  | Coq_tRel _ | Coq_tVar _ | Coq_tConst _ | Coq_tInd _ | Coq_tConstruct _ | Coq_tInt _ | Coq_tFloat _ | tString _ -> p
  | Coq_tEvar (k, l) -> Coq_tEvar (k, map aux l)
  | Coq_tSort u -> Coq_tSort (fix_universe u)
  | Coq_tCast (t, k, t') -> Coq_tCast (aux t, k, aux t')
  | Coq_tProd (na, t, t') -> Coq_tProd (na, aux t, aux t')
  | Coq_tLambda (na, t, t') -> Coq_tLambda (na, aux t, aux t')
  | Coq_tLetIn (na, t, b, t') -> Coq_tLetIn (na, aux t, aux b, aux t')
  | Coq_tApp (t, l) -> Coq_tApp (aux t, map aux l)
  | Coq_tCase (ci, p, c, brs) -> Coq_tCase (ci, aux_pred p, aux c, map aux_branch brs)
  | Coq_tProj (p, t) -> Coq_tProj (p, aux t)
  | Coq_tFix (mfix, i) -> Coq_tFix (map aux_def mfix, i)
  | Coq_tCoFix (mfix, i) -> Coq_tCoFix (map aux_def mfix, i)
  and aux_pred { puinst = puinst; pparams = pparams; pcontext = pcontext; preturn = preturn } =
    { puinst; pparams = map aux pparams; pcontext; preturn = aux preturn }
  and aux_branch { bcontext = bcontext; bbody = bbody } =
    { bcontext; bbody = aux bbody }
  and aux_def { dname = dname; dtype = dtype; dbody = dbody; rarg = rarg } =
    { dname; dtype = aux dtype; dbody = aux dbody; rarg }
  in aux p

let fix_rel_context ctx =
  let open BasicAst in 
  let fix_decl {decl_name; decl_body; decl_type} =
    {decl_name; decl_body = Option.map fix_term decl_body; decl_type = fix_term decl_type}
  in
  List.map fix_decl ctx
  
let fix_universes_decl = function
  | Monomorphic_ctx -> Monomorphic_ctx
  | Polymorphic_ctx (names, set) -> Polymorphic_ctx (names, Obj.magic (fix_set set))
  
let fix_universes (levels, cstrs) = 
  (Obj.magic (fix_set levels), Obj.magic (fix_set cstrs))

let fix_projection p =
  let open Ast0.Env in
  { proj_name = proj_name p; proj_relevance = proj_relevance p; proj_type = fix_term (proj_type p) }

let fix_declarations decls = 
  let open Ast0.Env in
  let fix_constructor {cstr_name; cstr_args; cstr_indices; cstr_type; cstr_arity} = 
    {cstr_name; cstr_args = fix_rel_context cstr_args; 
     cstr_indices = List.map fix_term cstr_indices; 
     cstr_type = fix_term cstr_type; 
     cstr_arity}
  in
  let fix_ind_body {ind_name; ind_indices; ind_sort; ind_type; ind_kelim; ind_ctors; ind_projs; ind_relevance} =
    {ind_name; ind_indices = fix_rel_context ind_indices; ind_sort = fix_universe ind_sort;
     ind_type = fix_term ind_type; ind_kelim; 
     ind_ctors = List.map fix_constructor ind_ctors; 
     ind_projs = List.map fix_projection ind_projs; 
     ind_relevance}
  in
  let fix_decl (kn, decl) =
    let decl' = match decl with
    | Ast0.Env.ConstantDecl {cst_type; cst_body; cst_universes; cst_relevance} ->
      Ast0.Env.ConstantDecl { cst_type = fix_term cst_type; cst_body = Option.map fix_term cst_body; 
      cst_universes = fix_universes_decl cst_universes; cst_relevance }
    | Ast0.Env.InductiveDecl { ind_finite; ind_npars; ind_params; ind_bodies; ind_universes; ind_variance} ->
      Ast0.Env.InductiveDecl { ind_finite; ind_npars; ind_params = fix_rel_context ind_params; 
      ind_bodies = List.map fix_ind_body ind_bodies; 
      ind_universes = fix_universes_decl ind_universes; 
      ind_variance}
    in (kn, decl')
  in
  List.map fix_decl decls

let fix_quoted_program (p : Ast0.Env.program) = 
  let ({ Ast0.Env.universes = universes; declarations = declarations; retroknowledge = retroknowledge }, term) = p in
  let term = fix_term term in
  let universes = fix_universes universes in
  let declarations = fix_declarations declarations in
  { Ast0.Env.universes = universes; declarations; retroknowledge }, term

let erase ~bypass env evm c =
  debug (fun () -> str"Quoting");
  let prog = time (str"Quoting") (quote_term_rec ~bypass ~with_universes:false env) evm (EConstr.to_constr evm c) in
  let prog = fix_quoted_program prog in
  time (str"Erasure") certicoq_erase prog
