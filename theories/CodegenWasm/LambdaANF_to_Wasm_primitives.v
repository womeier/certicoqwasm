From Wasm Require Import datatypes operations.
From CertiCoq Require Import LambdaANF.toplevel LambdaANF.cps_util.

From CertiCoq Require Import Common.Common Common.compM Common.Pipeline_utils.
Require Import ExtLib.Structures.Monad.
From MetaCoq.Utils Require Import bytestring MCString.
From Coq Require Import ZArith BinNat List Lia.

Require Import MSets.MSetAVL.
From Coq Require Import FMapAVL.
Require Import POrderedType.

Require Import LambdaANF.cps LambdaANF.cps_show.
From CertiCoq.CodegenWasm Require Import LambdaANF_to_Wasm_common.
Import MonadNotation.


(* **** TRANSLATE PRIMITIVE VALUES **** *)

Definition translate_primitive_value (p : AstCommon.primitive) : error Wasm_int.Int64.int :=
  match projT1 p as tag return prim_value tag -> error Wasm_int.Int64.T with
  | AstCommon.primInt => fun i => Ret (Wasm_int.Int64.repr (Uint63.to_Z i))
  | AstCommon.primFloat => fun f => Err "Extraction of floats to Wasm not yet supported"
  end (projT2 p).
  
(* **** TRANSLATE PRIMITIVE OPERATIONS **** *)

Definition primInt63ModPath : Kernames.modpath :=
  Kernames.MPfile [ "PrimInt63"%bs ; "Int63"%bs ; "Cyclic"%bs ; "Numbers"%bs ; "Coq"%bs ].

Definition primInt63Add        : Kernames.kername := (primInt63ModPath, "add"%bs).
Definition primInt63Addc       : Kernames.kername := (primInt63ModPath, "addc"%bs).
Definition primInt63Addcarryc  : Kernames.kername := (primInt63ModPath, "addcarryc"%bs).
Definition primInt63Sub        : Kernames.kername := (primInt63ModPath, "sub"%bs).
Definition primInt63Subc       : Kernames.kername := (primInt63ModPath, "subc"%bs).
Definition primInt63Subcarryc  : Kernames.kername := (primInt63ModPath, "subcarryc"%bs).
Definition primInt63Mul        : Kernames.kername := (primInt63ModPath, "mul"%bs).
Definition primInt63Mulc       : Kernames.kername := (primInt63ModPath, "mulc"%bs).
Definition primInt63Div        : Kernames.kername := (primInt63ModPath, "div"%bs).
Definition primInt63Mod        : Kernames.kername := (primInt63ModPath, "mod"%bs).
Definition primInt63Land       : Kernames.kername := (primInt63ModPath, "land"%bs).
Definition primInt63Lor        : Kernames.kername := (primInt63ModPath, "lor"%bs).
Definition primInt63Lxor       : Kernames.kername := (primInt63ModPath, "lxor"%bs).
Definition primInt63Lsl        : Kernames.kername := (primInt63ModPath, "lsl"%bs).
Definition primInt63Lsr        : Kernames.kername := (primInt63ModPath, "lsr"%bs).
Definition primInt63Compare    : Kernames.kername := (primInt63ModPath, "compare"%bs).
Definition primInt63Eqb        : Kernames.kername := (primInt63ModPath, "eqb"%bs).
Definition primInt63Ltb        : Kernames.kername := (primInt63ModPath, "ltb"%bs).
Definition primInt63Leb        : Kernames.kername := (primInt63ModPath, "leb"%bs).
Definition primInt63Head0      : Kernames.kername := (primInt63ModPath, "head0"%bs).
Definition primInt63Tail0      : Kernames.kername := (primInt63ModPath, "tail0"%bs).
Definition primInt63Addmuldiv  : Kernames.kername := (primInt63ModPath, "addmuldiv"%bs).
Definition primInt63Diveucl    : Kernames.kername := (primInt63ModPath, "diveucl"%bs).
Definition primInt63Diveucl_21 : Kernames.kername := (primInt63ModPath, "diveucl_21"%bs).

Definition maxuint31 := VAL_int64 (Wasm_int.Int64.repr 2147483647%Z).
Definition maxuint63 := VAL_int64 (Wasm_int.Int64.repr 9223372036854775807%Z).

Definition load_local_i64 (i : localidx) : list basic_instruction :=
  [ BI_local_get i ; BI_load T_i64 None 2%N 0%N ].

Definition increment_global_mem_ptr i :=
  [ BI_global_get global_mem_ptr
  ; BI_const_num (nat_to_value i)
  ; BI_binop T_i32 (Binop_i BOI_add)
  ; BI_global_set global_mem_ptr
  ].

Definition apply_binop_and_store_i64 (op : list basic_instruction) x y :=
  BI_global_get global_mem_ptr :: (* Address to store the result of the operation *)
  load_local_i64 x ++            (* Load the arguments onto the stack *)
  load_local_i64 y ++
  op ++
  [ BI_store T_i64 None 2%N 0%N (* Store the result *)
  ; BI_global_get global_mem_ptr (* Put the address where the result was stored on the stack *)
  ] ++
  increment_global_mem_ptr 8.

Definition make_carry (ord : nat) (gidx : globalidx) : list basic_instruction:=
  [ BI_global_get global_mem_ptr
  ; BI_global_get gidx
  ; BI_store T_i64 None 2%N 0%N
  ; BI_global_get global_mem_ptr
  ; BI_const_num (nat_to_value 8)
  ; BI_binop T_i32 (Binop_i BOI_add)
  ; BI_global_set constr_alloc_ptr
  ; BI_global_get constr_alloc_ptr
  ; BI_const_num (nat_to_value ord)
  ; BI_store T_i32 None 2%N 0%N
  ; BI_global_get global_mem_ptr
  ; BI_const_num (nat_to_value 12)
  ; BI_binop T_i32 (Binop_i BOI_add)
  ; BI_global_get global_mem_ptr
  ; BI_store T_i32 None 2%N 0%N
  ; BI_global_get constr_alloc_ptr
  ] ++ increment_global_mem_ptr 16.


Definition apply_carry_operation x y  (ord1 ord2 : nat) (ops relops : list basic_instruction) : list basic_instruction :=
    load_local_i64 x ++
    load_local_i64 y ++
    ops ++
    [ BI_const_num maxuint63
    ; BI_binop T_i64 (Binop_i BOI_and)
    ; BI_global_set glob_tmp1
    ] ++
    relops ++
    [ BI_if (BT_valtype (Some (T_num T_i32)))
        (make_carry ord1 glob_tmp1)
        (make_carry ord2 glob_tmp1)
    ].

(* Assumptions for constructing a prod value:
   - The 1st argument is stored in global gidx1, 2nd argument in global gidx2
   - ordinal(pair) = 0 *)
Definition make_product (gidx1 gidx2 : N) : list basic_instruction :=
  [ BI_global_get global_mem_ptr
  ; BI_global_get gidx1
  ; BI_store T_i64 None 2%N 0%N
  ; BI_global_get global_mem_ptr
  ; BI_const_num (nat_to_value 8)
  ; BI_binop T_i32 (Binop_i BOI_add)
  ; BI_global_get gidx2
  ; BI_store T_i64 None 2%N 0%N
  ; BI_global_get global_mem_ptr
  ; BI_const_num (nat_to_value 16)
  ; BI_binop T_i32 (Binop_i BOI_add)
  ; BI_global_set constr_alloc_ptr
  ; BI_global_get constr_alloc_ptr
  ; BI_const_num (nat_to_value 0)
  ; BI_store T_i32 None 2%N 0%N

  ; BI_global_get global_mem_ptr
  ; BI_const_num (nat_to_value 20)
  ; BI_binop T_i32 (Binop_i BOI_add)
  ; BI_global_get global_mem_ptr
  ; BI_store T_i32 None 2%N 0%N

  ; BI_global_get global_mem_ptr
  ; BI_const_num (nat_to_value 24)
  ; BI_binop T_i32 (Binop_i BOI_add)
  ; BI_global_get global_mem_ptr
  ; BI_const_num (nat_to_value 8)
  ; BI_binop T_i32 (Binop_i BOI_add)
  ; BI_store T_i32 None 2%N 0%N

  ; BI_global_get constr_alloc_ptr
  ] ++ increment_global_mem_ptr 28.

(* Assumptions about constructor environment for primitive operations that return bools:
   1. ordinal(true) = 0
   2. ordinal(false) = 1 *)
Definition make_boolean_valued_comparison x y relop : list basic_instruction :=
  load_local_i64 x ++            (* Load the arguments onto the stack *)
  load_local_i64 y ++
  [ BI_relop T_i64 (Relop_i relop)
  ; BI_if (BT_valtype (Some (T_num T_i32)))
      [ BI_const_num (nat_to_value 1) ] (* 2 * ordinal(true) + 1 *)
      [ BI_const_num (nat_to_value 3) ] (* 2 * ordinal(false) + 1 *)
  ].

Definition translate_primitive_binary_op op_name x y : error (list basic_instruction) :=
  if Kername.eqb op_name primInt63Add then
    Ret (apply_binop_and_store_i64 [ BI_binop T_i64 (Binop_i BOI_add) ; BI_const_num maxuint63 ; BI_binop T_i64 (Binop_i BOI_and) ] x y)
  else if Kername.eqb op_name primInt63Sub then
    Ret (apply_binop_and_store_i64 [ BI_binop T_i64 (Binop_i BOI_sub) ; BI_const_num maxuint63 ; BI_binop T_i64 (Binop_i BOI_and) ] x y)
  else if Kername.eqb op_name primInt63Mul then
    Ret (apply_binop_and_store_i64 [ BI_binop T_i64 (Binop_i BOI_mul) ; BI_const_num maxuint63 ; BI_binop T_i64 (Binop_i BOI_and) ] x y)
  else if Kername.eqb op_name primInt63Div then
    Ret (BI_global_get global_mem_ptr ::
         load_local_i64 y ++
         [ BI_testop T_i64 TO_eqz
         ; BI_if (BT_valtype (Some (T_num T_i64)))
             [ BI_const_num (nat_to_value64 0) ]
             (load_local_i64 x ++ load_local_i64 y ++ [ BI_binop T_i64 (Binop_i (BOI_div SX_U)) ])
         ; BI_store T_i64 None 2%N 0%N
         ; BI_global_get global_mem_ptr
         ] ++ increment_global_mem_ptr 8)
  else if Kername.eqb op_name primInt63Mod then
    Ret(BI_global_get global_mem_ptr ::
        load_local_i64 y ++
        [ BI_testop T_i64 TO_eqz
        ; BI_if (BT_valtype (Some (T_num T_i64)))
            (load_local_i64 x)
            (load_local_i64 x ++ load_local_i64 y ++ [ BI_binop T_i64 (Binop_i (BOI_rem SX_U)) ])
        ; BI_store T_i64 None 2%N 0%N
        ; BI_global_get global_mem_ptr
        ] ++ increment_global_mem_ptr 8)
  else if Kername.eqb op_name primInt63Land then
    Ret (apply_binop_and_store_i64 [ BI_binop T_i64 (Binop_i BOI_and) ] x y)
  else if Kername.eqb op_name primInt63Lor then
    Ret (apply_binop_and_store_i64 [ BI_binop T_i64 (Binop_i BOI_or) ] x y)
  else if Kername.eqb op_name primInt63Lxor then
    Ret (apply_binop_and_store_i64 [ BI_binop T_i64 (Binop_i BOI_xor) ] x y)
  else if Kername.eqb op_name primInt63Lsl then
    Ret (BI_global_get global_mem_ptr ::
         load_local_i64 y ++
         [ BI_const_num (nat_to_value64 63)
         ; BI_relop T_i64 (Relop_i (ROI_lt SX_U))
         ; BI_if (BT_valtype (Some (T_num T_i64)))
             (load_local_i64 x ++
              load_local_i64 y ++
              [ BI_binop T_i64 (Binop_i BOI_shl) ; BI_const_num maxuint63 ; BI_binop T_i64 (Binop_i BOI_and) ])
             [ BI_const_num (nat_to_value64 0) ]
         ; BI_store T_i64 None 2%N 0%N
         ; BI_global_get global_mem_ptr
         ] ++ increment_global_mem_ptr 8)

  else if Kername.eqb op_name primInt63Lsr then
    Ret (BI_global_get global_mem_ptr ::
         load_local_i64 y ++
         [ BI_const_num (nat_to_value64 63)
         ; BI_relop T_i64 (Relop_i (ROI_lt SX_U))
         ; BI_if (BT_valtype (Some (T_num T_i64)))
             (load_local_i64 x ++ load_local_i64 y ++ [ BI_binop T_i64 (Binop_i (BOI_shr SX_U)) ])
             [ BI_const_num (nat_to_value64 0) ]
         ; BI_store T_i64 None 2%N 0%N
         ; BI_global_get global_mem_ptr
         ] ++ increment_global_mem_ptr 8)

  else if Kername.eqb op_name primInt63Eqb then
    Ret (make_boolean_valued_comparison x y ROI_eq)

  else if Kername.eqb op_name primInt63Ltb then
    Ret (make_boolean_valued_comparison x y (ROI_lt SX_U))

  else if Kername.eqb op_name primInt63Leb then
    Ret (make_boolean_valued_comparison x y (ROI_le SX_U))

  (* Assumptions about constructor environment for compare:
       1. ordinal(Eq) = 0
       2. ordinal(Lt) = 1
       3. ordinal(Gt) = 2 *)
  else if Kername.eqb op_name primInt63Compare then
    Ret ([ BI_local_get x
         ; BI_load T_i64 None 2%N 0%N
         ; BI_local_get y
         ; BI_load T_i64 None 2%N 0%N
         ; BI_relop T_i64 (Relop_i (ROI_lt SX_U))
         ; BI_if (BT_valtype (Some (T_num T_i32)))
             [ BI_const_num (nat_to_value 3) ] (* 2 * ordinal(Lt) + 1 *)
             (load_local_i64 x ++
              load_local_i64 y ++
              [ BI_relop T_i64 (Relop_i ROI_eq)
              ; BI_if (BT_valtype (Some (T_num T_i32)))
                  [ BI_const_num (nat_to_value 1) ] (* 2 * ordinal(Eq) *)
                  [ BI_const_num (nat_to_value 5) ] (* 2 * ordinal(Gt) *)
              ])
         ])

       (* Assumptions for constructing a carry value:
          - The argument is stored in global with index gidx
          - ordinal(C0) = 0
          - ordinal(C1) = 1 *)
  else if Kername.eqb op_name primInt63Addc then
    Ret (apply_carry_operation x y 1 0
           [ BI_binop T_i64 (Binop_i BOI_add) ]
           ([ BI_global_get glob_tmp1 ] ++
              load_local_i64 x ++
              [ BI_relop T_i64 (Relop_i (ROI_lt SX_U))]))

  else if Kername.eqb op_name primInt63Addcarryc then
    Ret (apply_carry_operation x y 1 0
           [ BI_binop T_i64 (Binop_i BOI_add)
             ; BI_const_num (nat_to_value64 1)
             ; BI_binop T_i64 (Binop_i BOI_add) ]
           ([ BI_global_get glob_tmp1 ] ++
              load_local_i64 x ++
              [ BI_relop T_i64 (Relop_i (ROI_le SX_U))]))

  else if Kername.eqb op_name primInt63Subc then
    Ret (apply_carry_operation x y 0 1
           [ BI_binop T_i64 (Binop_i BOI_sub) ]
           (load_local_i64 y ++
              load_local_i64 x ++
              [ BI_relop T_i64 (Relop_i (ROI_le SX_U))]))

  else if Kername.eqb op_name primInt63Subcarryc then
    Ret (apply_carry_operation x y 0 1
           [ BI_binop T_i64 (Binop_i BOI_sub)
           ; BI_const_num (nat_to_value64 1)
           ; BI_binop T_i64 (Binop_i BOI_sub) ]
           (load_local_i64 y ++
              load_local_i64 x ++
              [ BI_relop T_i64 (Relop_i (ROI_lt SX_U))]))

  else if Kername.eqb op_name primInt63Mulc then
    Ret (load_local_i64 x ++
         [ BI_const_num (nat_to_value64 62) ; BI_binop T_i64 (Binop_i (BOI_shr SX_U)) ; BI_testop T_i64 TO_eqz ] ++
         load_local_i64 y ++
         [ BI_const_num (nat_to_value64 62) ; BI_binop T_i64 (Binop_i (BOI_shr SX_U)) ; BI_testop T_i64 TO_eqz ] ++
         [ BI_binop T_i32 (Binop_i BOI_or)
         ; BI_if (BT_valtype None)
             (load_local_i64 y ++ [ BI_global_set glob_tmp3 ])
             (load_local_i64 y ++
              [ BI_const_num (VAL_int64 (Wasm_int.Int64.repr 4611686018427387904%Z))
              ; BI_binop T_i64 (Binop_i BOI_xor)
              ; BI_global_set glob_tmp3
              ])
         ] ++
         (* glob_tmp1 <- let hx = x >> 31 *)
         load_local_i64 x ++
         [ BI_const_num (nat_to_value64 31) ; BI_binop T_i64 (Binop_i (BOI_shr SX_U)) ; BI_global_set glob_tmp1 ] ++
         (* glob_tmp2 <- let lx = x & ((1 << 31) - 1) *)
         load_local_i64 x ++
         [ BI_const_num maxuint31 ; BI_binop T_i64 (Binop_i BOI_and) ; BI_global_set glob_tmp2 ] ++
         (* glob_tmp4 <- let hy =  y >> 31 *)
         [ BI_global_get glob_tmp3 ; BI_const_num (nat_to_value64 31) ; BI_binop T_i64 (Binop_i (BOI_shr SX_U)) ; BI_global_set glob_tmp4 ] ++
         (* glob_tmp3 <- let ly = y & ((1 << 31) - 1) *)
         [ BI_global_get glob_tmp3 ; BI_const_num maxuint31 ; BI_binop T_i64 (Binop_i BOI_and) ; BI_global_set glob_tmp3 ] ++
         [ BI_global_get glob_tmp1 ; BI_global_get glob_tmp4 ; BI_binop T_i64 (Binop_i BOI_mul) ] ++
         [ BI_global_get glob_tmp1 ; BI_global_get glob_tmp3 ; BI_binop T_i64 (Binop_i BOI_mul) ] ++
         [ BI_global_get glob_tmp2 ; BI_global_get glob_tmp4 ; BI_binop T_i64 (Binop_i BOI_mul) ] ++
         [ BI_global_get glob_tmp2 ; BI_global_get glob_tmp3 ; BI_binop T_i64 (Binop_i BOI_mul) ] ++
         (* glob_tmp4 <- let lxy = lx * ly
            glob_tmp3 <- let lxhy = lx * hy
            glob_tmp2 <- let hxly = hx * ly
            glob_tmp1 <- let hxy  = hx * hy *)
         [ BI_global_set glob_tmp4
         ; BI_global_set glob_tmp3
         ; BI_global_set glob_tmp2
         ; BI_global_set glob_tmp1
         ]  ++
         (* glob_tmp4 <- let l = lxy | (hxy << 62) = glob_tmp4 | (glob_tmp1 << 62) *)
         [ BI_global_get glob_tmp4
         ; BI_global_get glob_tmp1
         ; BI_const_num (nat_to_value64 62)
         ; BI_binop T_i64 (Binop_i BOI_shl)
         ; BI_const_num maxuint63
         ; BI_binop T_i64 (Binop_i BOI_and)
         ; BI_binop T_i64 (Binop_i BOI_or)
         ; BI_global_set glob_tmp4
         ] ++
         (* glob_tmp1 <- let h = hxy >> 1 = glob_tmp1 >> 1 *)
         [ BI_global_get glob_tmp1
         ; BI_const_num (nat_to_value64 1)
         ; BI_binop T_i64 (Binop_i (BOI_shr SX_U))
         ; BI_global_set glob_tmp1
         ] ++
         (* glob_tmp3 <- let hl = hxly + lxhy = glob_tmp2 + glob_tmp3 *)
         [ BI_global_get glob_tmp2
         ; BI_global_get glob_tmp3
         ; BI_binop T_i64 (Binop_i BOI_add)
         ; BI_const_num maxuint63
         ; BI_binop T_i64 (Binop_i BOI_and)
         ; BI_global_set glob_tmp3
         ] ++
         (* glob_tmp1 <- let h = if hl < hxly then h + (1 << 31) else h *)
         [ BI_global_get glob_tmp3
         ; BI_global_get glob_tmp2
         ; BI_relop T_i64 (Relop_i (ROI_lt SX_U))
         ; BI_if (BT_valtype None)
             [ BI_global_get glob_tmp1
             ; BI_const_num (VAL_int64 (Wasm_int.Int64.repr 2147483648%Z))
             ; BI_binop T_i64 (Binop_i BOI_add)
             ; BI_global_set glob_tmp1
             ]
             [ ]
         ] ++
         (* glob_tmp2 <- let hl' = hl << 31 *)
         [ BI_global_get glob_tmp3
         ; BI_const_num (nat_to_value64 31)
         ; BI_binop T_i64 (Binop_i BOI_shl)
         ; BI_const_num maxuint63
         ; BI_binop T_i64 (Binop_i BOI_and)
         ; BI_global_set glob_tmp2
         ] ++
         (* glob_tmp4 <- let l = l + hl' *)
         [ BI_global_get glob_tmp4
         ; BI_global_get glob_tmp2
         ; BI_binop T_i64 (Binop_i BOI_add)
         ; BI_const_num maxuint63
         ; BI_binop T_i64 (Binop_i BOI_and)
         ; BI_global_set glob_tmp4
         ] ++
         (* glob_tmp1 <- let h = if l < hl' then h + 1 else h *)
         [ BI_global_get glob_tmp4
         ; BI_global_get glob_tmp2
         ; BI_relop T_i64 (Relop_i (ROI_lt SX_U))
         ; BI_if (BT_valtype None)
             [ BI_global_get glob_tmp1
             ; BI_const_num (nat_to_value64 1)
             ; BI_binop T_i64 (Binop_i BOI_add)
             ; BI_global_set glob_tmp1
             ]
             [ ]
         ] ++
         (* glob_tmp1 <- let h = h + (hl >> 32) *)
         [ BI_global_get glob_tmp1
         ; BI_global_get glob_tmp3
         ; BI_const_num (nat_to_value64 32)
         ; BI_binop T_i64 (Binop_i (BOI_shr SX_U))
         ; BI_binop T_i64 (Binop_i BOI_add)
         ; BI_const_num maxuint63
         ; BI_binop T_i64 (Binop_i BOI_and)
         ; BI_global_set glob_tmp1
         ] ++
         load_local_i64 x ++
         [ BI_const_num (nat_to_value64 62)
         ; BI_binop T_i64 (Binop_i (BOI_shr SX_U))
         ; BI_testop T_i64 TO_eqz
         ] ++
         load_local_i64 y ++
         [ BI_const_num (nat_to_value64 62)
         ; BI_binop T_i64 (Binop_i (BOI_shr SX_U))
         ; BI_testop T_i64 TO_eqz
         ; BI_binop T_i32 (Binop_i BOI_or)
         ; BI_if (BT_valtype None)
             [ ]
             [ (* glob_tmp2 <- let l' := l + (x << 62) *)
             BI_global_get glob_tmp4
             ; BI_local_get x
             ; BI_load T_i64 None 2%N 0%N
             ; BI_const_num (nat_to_value64 62)
             ; BI_binop T_i64 (Binop_i BOI_shl)
             ; BI_binop T_i64 (Binop_i BOI_add)
             ; BI_const_num maxuint63
             ; BI_binop T_i64 (Binop_i BOI_and)
             ; BI_global_set glob_tmp2
             (* glob_tmp1 <- let h := if l' < l then h + 1 else h *)
             ; BI_global_get glob_tmp2
             ; BI_global_get glob_tmp4
             ; BI_relop T_i64 (Relop_i (ROI_lt SX_U))
             ; BI_if (BT_valtype None)
                 [ BI_global_get glob_tmp1
                 ; BI_const_num (nat_to_value64 1)
                 ; BI_binop T_i64 (Binop_i BOI_add)
                 ; BI_global_set glob_tmp1
                 ]
                 [ ]
             (* return (h + (x >> 1), l') *)
             ; BI_global_get glob_tmp1
             ; BI_local_get x
             ; BI_load T_i64 None 2%N 0%N
             ; BI_const_num (nat_to_value64 1)
             ; BI_binop T_i64 (Binop_i (BOI_shr SX_U))
             ; BI_binop T_i64 (Binop_i BOI_add)
             ; BI_const_num maxuint63
             ; BI_binop T_i64 (Binop_i BOI_and)
             ; BI_global_set glob_tmp1
             ; BI_global_get glob_tmp2
             ; BI_global_set glob_tmp4
             ]
         ] ++ make_product glob_tmp1 glob_tmp4)

  else if Kername.eqb op_name primInt63Diveucl then
    Ret ([ BI_local_get x
         ; BI_load T_i64 None 2%N 0%N
         ; BI_testop T_i64 TO_eqz
         ; BI_if (BT_valtype None)
             [ BI_const_num (nat_to_value64 0)
             ; BI_global_set glob_tmp1
             ; BI_const_num (nat_to_value64 0)
             ; BI_global_set glob_tmp2
             ]
             [ BI_local_get y
             ; BI_load T_i64 None 2%N 0%N
             ; BI_testop T_i64 TO_eqz
             ; BI_if (BT_valtype None)
                 [ BI_const_num (nat_to_value64 0)
                 ; BI_global_set glob_tmp1
                 ; BI_local_get x
                 ; BI_load T_i64 None 2%N 0%N
                 ; BI_global_set glob_tmp2
                 ]
                 (load_local_i64 x ++
                  load_local_i64 y ++
                  [ BI_binop T_i64 (Binop_i (BOI_div SX_U)) ; BI_global_set glob_tmp1 ] ++
                  load_local_i64 x ++
                  load_local_i64 y ++
                  [ BI_binop T_i64 (Binop_i (BOI_rem SX_U)) ; BI_global_set glob_tmp2 ])
             ]
         ] ++ make_product glob_tmp1 glob_tmp2)
  else
    Err ("Unknown primitive arithmetic operator: " ++ (Kernames.string_of_kername op_name))%bs.

Definition translate_primitive_unary_op op_name x : error (list basic_instruction) :=
  if Kername.eqb op_name primInt63Head0 then
    (* head0 x computes the leading number of zeros in x
           OBS: need to subtract 1 since we're dealing with 63-bit integers *)
    Ret (BI_global_get global_mem_ptr ::
         load_local_i64 x ++
         [ BI_unop T_i64 (Unop_i UOI_clz)
         ; BI_const_num (nat_to_value64 1)
         ; BI_binop T_i64 (Binop_i BOI_sub)
         ; BI_store T_i64 None 2%N 0%N
         ; BI_global_get global_mem_ptr
         ] ++ increment_global_mem_ptr 8)

  else if Kername.eqb op_name primInt63Tail0 then
    (* tail0 x computes the trailing number of zeros in x
           OBS: if x is 0, then result is 63 (can't just use wasm ctz op) ) *)
    Ret (BI_global_get global_mem_ptr ::
         load_local_i64 x ++
         [ BI_testop T_i64 TO_eqz
         ; BI_if (BT_valtype (Some (T_num T_i64)))
             [ BI_const_num (nat_to_value64 63) ]
             (load_local_i64 x ++ [ BI_unop T_i64 (Unop_i UOI_ctz) ])
         ; BI_store T_i64 None 2%N 0%N
         ; BI_global_get global_mem_ptr
         ] ++ increment_global_mem_ptr 8)
  else
    Err ("Unknown primitive unary operator: " ++ (Kernames.string_of_kername op_name))%bs.

Definition div21_loop_body :=
  [ BI_global_get glob_tmp1
  ; BI_const_num (nat_to_value64 1)
  ; BI_binop T_i64 (Binop_i BOI_shl)
  ; BI_global_get glob_tmp2
  ; BI_const_num (nat_to_value64 62)
  ; BI_binop T_i64 (Binop_i (BOI_shr SX_U))
  ; BI_binop T_i64 (Binop_i BOI_or)
  ; BI_global_set glob_tmp1

  ; BI_global_get glob_tmp2
  ; BI_const_num (nat_to_value64 1)
  ; BI_binop T_i64 (Binop_i BOI_shl)
  ; BI_const_num maxuint63
  ; BI_binop T_i64 (Binop_i (BOI_rem SX_U))
  ; BI_global_set glob_tmp2

  ; BI_global_get glob_tmp3
  ; BI_const_num (nat_to_value64 1)
  ; BI_binop T_i64 (Binop_i BOI_shl)
  ; BI_const_num maxuint63
  ; BI_binop T_i64 (Binop_i BOI_and)
  ; BI_global_set glob_tmp3

  ; BI_global_get glob_tmp1
  ; BI_global_get glob_tmp4
  ; BI_relop T_i64 (Relop_i (ROI_ge SX_U))
  ; BI_if (BT_valtype None)
      [ BI_global_get glob_tmp3
      ; BI_const_num (nat_to_value64 1)
      ; BI_binop T_i64 (Binop_i BOI_or)
      ; BI_global_set glob_tmp3
      ; BI_global_get glob_tmp1
      ; BI_global_get glob_tmp4
      ; BI_binop T_i64 (Binop_i BOI_sub)
      ; BI_global_set glob_tmp1
      ]
      [ ]
  ].

Definition translate_primitive_ternary_op op_name x y z : error (list basic_instruction) :=
  if Kername.eqb op_name primInt63Diveucl_21 then
    Ret (load_local_i64 z ++
         [ BI_const_num maxuint63
         ; BI_binop T_i64 (Binop_i BOI_and)
         ; BI_global_set glob_tmp4
         ] ++
         load_local_i64 x ++
         [ BI_const_num maxuint63
         ; BI_binop T_i64 (Binop_i BOI_and)
         ; BI_global_set glob_tmp1
         ] ++
         [ BI_global_get glob_tmp4
         ; BI_global_get glob_tmp1
         ; BI_relop T_i64 (Relop_i (ROI_le SX_U))
         ; BI_if (BT_valtype (Some (T_num T_i32)))
             ([ BI_const_num (nat_to_value64 0) ; BI_global_set glob_tmp1 ] ++ make_product glob_tmp1 glob_tmp1)
             (load_local_i64 y ++
              [ BI_global_set glob_tmp2
              ; BI_const_num (nat_to_value64 0)
              ; BI_global_set glob_tmp3
              ] ++ (List.flat_map (fun x => x) (List.repeat div21_loop_body 63)) ++
              [ BI_global_get glob_tmp1
              ; BI_const_num maxuint63
              ; BI_binop T_i64 (Binop_i BOI_and)
              ; BI_global_set glob_tmp1
              ] ++ (make_product glob_tmp3 glob_tmp1))
         ])

  else if Kername.eqb op_name primInt63Addmuldiv then
    Ret (BI_global_get global_mem_ptr ::
         load_local_i64 x ++
         [ BI_const_num (nat_to_value64 63)
         ; BI_relop T_i64 (Relop_i (ROI_gt SX_U))
         ; BI_if (BT_valtype (Some (T_num T_i64)))
             [ BI_const_num (nat_to_value64 0) ]
             (* Compute x << z on the stack *)
             (load_local_i64 y ++
              load_local_i64 x ++
              [ BI_binop T_i64 (Binop_i BOI_shl)
              ; BI_const_num maxuint63
              ; BI_binop T_i64 (Binop_i BOI_and)
              ] ++
              (* Put y on the stack *)
              load_local_i64 z ++
              (* Compute 63 - z on the stack *)
              [ BI_const_num (nat_to_value64 63) ] ++
              load_local_i64 x ++
              [ BI_binop T_i64 (Binop_i BOI_sub)
              (* Compute y >> (63 - z) on the stack *)
              ; BI_binop T_i64 (Binop_i (BOI_shr SX_U))
              (* Finally, compute (x << z) | (y >> (63 - z)) on the stack *)
              ; BI_binop T_i64 (Binop_i BOI_or)
              ])
         ; BI_store T_i64 None 2%N 0%N
         ; BI_global_get global_mem_ptr
         ] ++ increment_global_mem_ptr 8)
  else
    Err ("Unknown primitive arithmetic operator: " ++ (Kernames.string_of_kername op_name))%bs.

