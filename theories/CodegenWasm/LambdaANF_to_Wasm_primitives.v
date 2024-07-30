From Coq Require Import POrderedType ZArith BinNat List Lia Uint63.
From Wasm Require Import datatypes operations numerics.
Import Wasm_int.

Require Import compcert.lib.Coqlib.

From CertiCoq Require Import
  LambdaANF.toplevel LambdaANF.cps_util LambdaANF.cps LambdaANF.cps_show
  Common.Common Common.compM Common.Pipeline_utils.

Require Import ExtLib.Structures.Monad.
From MetaCoq Require Import Common.Kernames Utils.bytestring Utils.MCString.

Import MonadNotation SigTNotations.

Notation uint63 := Uint63.int.

Notation Z_to_i64 z := (Int64.repr z).
Notation Z_to_VAL_i64 z := (VAL_int64 (Int64.repr z)).

Local Coercion Z_to_i64_co z := Z_to_i64 z.  (* : Z >-> Wasm_int.Int64.int. *)
Local Coercion Z_to_i64val_co z := Z_to_VAL_i64 z. (* : Z >-> value_num.  *)

Notation "'primInt' x" := (AstCommon.primInt ; x) (at level 0).

Opaque Uint63.to_Z.


(* **** TRANSLATE PRIMITIVE VALUES **** *)

Definition translate_primitive_value (p : AstCommon.primitive) : error Wasm_int.Int64.int :=
  match projT1 p as tag return prim_value tag -> error Wasm_int.Int64.T with
  | AstCommon.primInt => fun i => Ret (Wasm_int.Int64.repr (Uint63.to_Z i))
  | AstCommon.primFloat => fun f => Err "Extraction of floats to Wasm not yet supported"
  end (projT2 p).

(* **** TRANSLATE PRIMITIVE OPERATIONS **** *)

Definition primInt63ModPath : Kernames.modpath :=
  Kernames.MPfile [ "PrimInt63"%bs ; "Int63"%bs ; "Cyclic"%bs ; "Numbers"%bs ; "Coq"%bs ].

Inductive primop :=
| PrimInt63add
| PrimInt63sub
| PrimInt63mul
| PrimInt63div
| PrimInt63mod
| PrimInt63lsl
| PrimInt63lsr
| PrimInt63land
| PrimInt63lor
| PrimInt63lxor
| PrimInt63eqb
| PrimInt63ltb
| PrimInt63leb
| PrimInt63compare
| PrimInt63addc
| PrimInt63addcarryc
| PrimInt63subc
| PrimInt63subcarryc
| PrimInt63mulc
| PrimInt63head0
| PrimInt63tail0
| PrimInt63diveucl
| PrimInt63diveucl_21
| PrimInt63addmuldiv.

Definition primop_map : KernameMap.t primop :=
  KernameMap.add (primInt63ModPath, "add") PrimInt63add
    (KernameMap.add (primInt63ModPath, "sub") PrimInt63sub
    (KernameMap.add (primInt63ModPath, "mul") PrimInt63mul
    (KernameMap.add (primInt63ModPath, "div") PrimInt63div
    (KernameMap.add (primInt63ModPath, "mod") PrimInt63mod
    (KernameMap.add (primInt63ModPath, "lsl") PrimInt63lsl
    (KernameMap.add (primInt63ModPath, "lsr") PrimInt63lsr
    (KernameMap.add (primInt63ModPath, "land") PrimInt63land
    (KernameMap.add (primInt63ModPath, "lor") PrimInt63lor
    (KernameMap.add (primInt63ModPath, "lxor") PrimInt63lxor
    (KernameMap.add (primInt63ModPath, "eqb") PrimInt63eqb
    (KernameMap.add (primInt63ModPath, "ltb") PrimInt63ltb
    (KernameMap.add (primInt63ModPath, "leb") PrimInt63leb
    (KernameMap.add (primInt63ModPath, "compare") PrimInt63compare
    (KernameMap.add (primInt63ModPath, "addc") PrimInt63addc
    (KernameMap.add (primInt63ModPath, "addcarryc") PrimInt63addcarryc
    (KernameMap.add (primInt63ModPath, "subc") PrimInt63subc
    (KernameMap.add (primInt63ModPath, "subcarryc") PrimInt63subcarryc
    (KernameMap.add (primInt63ModPath, "mulc") PrimInt63mulc
    (KernameMap.add (primInt63ModPath, "head0") PrimInt63head0
    (KernameMap.add (primInt63ModPath, "tail0") PrimInt63tail0
    (KernameMap.add (primInt63ModPath, "diveucl") PrimInt63diveucl
    (KernameMap.add (primInt63ModPath, "diveucl_21") PrimInt63diveucl_21
    (KernameMap.add (primInt63ModPath, "addmuldiv") PrimInt63addmuldiv
    (KernameMap.empty primop)))))))))))))))))))))))).

Section Primitives.

Variables global_mem_ptr glob_tmp1 glob_tmp2 glob_tmp3 glob_tmp4 : globalidx.

Variables true_tag false_tag eq_tag lt_tag gt_tag c0_tag c1_tag pair_tag : ctor_tag.

Notation nat_to_i32val n := (VAL_int32 (Wasm_int.Int32.repr (BinInt.Z.of_nat n))).

Definition maxuint31 := 2147483647%Z.
Definition maxuint63 := 9223372036854775807%Z.

Definition load_local_i64 (i : localidx) : list basic_instruction :=
  [ BI_local_get i ; BI_load T_i64 None 2%N 0%N ].

Definition increment_global_mem_ptr i :=
  [ BI_global_get global_mem_ptr
  ; BI_const_num (nat_to_i32val i)
  ; BI_binop T_i32 (Binop_i BOI_add)
  ; BI_global_set global_mem_ptr
  ].

Definition bitmask_instrs := [ BI_const_num maxuint63 ; BI_binop T_i64 (Binop_i BOI_and) ].

Definition apply_binop_and_store_i64 (op : binop_i) (x y : localidx) (apply_bitmask : bool) : list basic_instruction :=
  BI_global_get global_mem_ptr :: (* Address to store the result of the operation *)
  load_local_i64 x ++             (* Load the arguments onto the stack *)
  load_local_i64 y ++
  [ BI_binop T_i64 (Binop_i op) ] ++
  (if apply_bitmask then bitmask_instrs else []) ++
  [ BI_store T_i64 None 2%N 0%N   (* Store the result *)
  ; BI_global_get global_mem_ptr  (* Put the address where the result was stored on the stack *)
  ] ++
  increment_global_mem_ptr 8.

Definition make_carry (ord : nat) (gidx : globalidx) : list basic_instruction:=
  [ BI_global_get global_mem_ptr
  ; BI_global_get gidx
  ; BI_store T_i64 None 2%N 0%N
  ; BI_global_get global_mem_ptr
  ; BI_const_num (nat_to_i32val ord)
  ; BI_store T_i32 None 2%N 8%N
  ; BI_global_get global_mem_ptr
  ; BI_global_get global_mem_ptr
  ; BI_store T_i32 None 2%N 12%N
  ; BI_global_get global_mem_ptr
  ; BI_const_num (nat_to_i32val 8)
  ; BI_binop T_i32 (Binop_i BOI_add)
  ] ++ increment_global_mem_ptr 16.

Definition apply_exact_add_operation (x y : localidx) (addone : bool) : list basic_instruction :=
    load_local_i64 x ++ load_local_i64 y ++
    [ BI_binop T_i64 (Binop_i BOI_add) ] ++
    (if addone then
       [ BI_const_num 1%Z ; BI_binop T_i64 (Binop_i BOI_add) ]
     else []) ++
    bitmask_instrs ++
    [BI_global_set glob_tmp1 ;BI_global_get glob_tmp1 ] ++
    load_local_i64 x ++
    [ BI_relop T_i64 (Relop_i ((if addone then ROI_le else ROI_lt) SX_U))
    ; BI_if (BT_valtype (Some (T_num T_i32))) (make_carry 1 glob_tmp1) (make_carry 0 glob_tmp1)
    ].

Definition apply_exact_sub_operation (x y : localidx) (subone : bool) : list basic_instruction :=
    load_local_i64 x ++ load_local_i64 y ++
    [ BI_binop T_i64 (Binop_i BOI_sub) ] ++
    (if subone then
       [ BI_const_num 1%Z ; BI_binop T_i64 (Binop_i BOI_sub) ]
     else []) ++
    bitmask_instrs ++
    [ BI_global_set glob_tmp1 ] ++
    load_local_i64 y ++
    load_local_i64 x ++
    [ BI_relop T_i64 (Relop_i ((if subone then ROI_lt else ROI_le) SX_U))
    ; BI_if (BT_valtype (Some (T_num T_i32))) (make_carry 0 glob_tmp1) (make_carry 1 glob_tmp1)
    ].

(* Assumptions for constructing a prod value:
   - The 1st argument is stored in global gidx1, 2nd argument in global gidx2
   - ordinal(pair) = 0 *)
Definition make_product (gidx1 gidx2 : N) : list basic_instruction :=
  [ BI_global_get global_mem_ptr
  ; BI_global_get gidx1
  ; BI_store T_i64 None 2%N 0%N
  ; BI_global_get global_mem_ptr
  ; BI_global_get gidx2
  ; BI_store T_i64 None 2%N 8%N
  ; BI_global_get global_mem_ptr
  ; BI_const_num (nat_to_i32val 0)
  ; BI_store T_i32 None 2%N 16%N
  ; BI_global_get global_mem_ptr
  ; BI_global_get global_mem_ptr
  ; BI_store T_i32 None 2%N 20%N
  ; BI_global_get global_mem_ptr
  ; BI_global_get global_mem_ptr
  ; BI_const_num (nat_to_i32val 8)
  ; BI_binop T_i32 (Binop_i BOI_add)
  ; BI_store T_i32 None 2%N 24%N
  ; BI_global_get global_mem_ptr
  ; BI_const_num (nat_to_i32val 16)
  ; BI_binop T_i32 (Binop_i BOI_add)
  ] ++ increment_global_mem_ptr 28.

(* Assumptions about constructor environment for primitive operations that return bools:
   1. ordinal(true) = 0
   2. ordinal(false) = 1 *)
Definition make_boolean_valued_comparison x y relop : list basic_instruction :=
  load_local_i64 x ++            (* Load the arguments onto the stack *)
  load_local_i64 y ++
  [ BI_relop T_i64 (Relop_i relop)
  ; BI_if (BT_valtype (Some (T_num T_i32)))
      [ BI_const_num (nat_to_i32val 1) ] (* 2 * ordinal(true) + 1 *)
      [ BI_const_num (nat_to_i32val 3) ] (* 2 * ordinal(false) + 1 *)
  ].


Definition compare_instrs x y : list basic_instruction :=
  [ BI_local_get x
    ; BI_load T_i64 None 2%N 0%N
    ; BI_local_get y
    ; BI_load T_i64 None 2%N 0%N
    ; BI_relop T_i64 (Relop_i (ROI_lt SX_U))
    ; BI_if (BT_valtype (Some (T_num T_i32)))
        [ BI_const_num (nat_to_i32val 3) ] (* 2 * ordinal(Lt) + 1 *)
        (load_local_i64 x ++
           load_local_i64 y ++
           [ BI_relop T_i64 (Relop_i ROI_eq)
             ; BI_if (BT_valtype (Some (T_num T_i32)))
                 [ BI_const_num (nat_to_i32val 1) ] (* 2 * ordinal(Eq) + 1 *)
                 [ BI_const_num (nat_to_i32val 5) ] (* 2 * ordinal(Gt) + 1*)
           ])
  ].

Definition div_instrs (x y : localidx) : list basic_instruction :=
  BI_global_get global_mem_ptr ::
    load_local_i64 y ++
    [ BI_testop T_i64 TO_eqz
    ; BI_if (BT_valtype (Some (T_num T_i64)))
        [ BI_const_num 0%Z ]
        (load_local_i64 x ++ load_local_i64 y ++ [ BI_binop T_i64 (Binop_i (BOI_div SX_U)) ])
    ; BI_store T_i64 None 2%N 0%N
    ; BI_global_get global_mem_ptr
    ] ++ increment_global_mem_ptr 8.


Definition mod_instrs (x y : localidx) : list basic_instruction :=
  BI_global_get global_mem_ptr ::
    load_local_i64 y ++
    [ BI_testop T_i64 TO_eqz
    ; BI_if (BT_valtype (Some (T_num T_i64)))
        (load_local_i64 x)
        (load_local_i64 x ++ load_local_i64 y ++ [ BI_binop T_i64 (Binop_i (BOI_rem SX_U)) ])
    ; BI_store T_i64 None 2%N 0%N
    ; BI_global_get global_mem_ptr
    ] ++ increment_global_mem_ptr 8.

Definition shift_instrs (x y : localidx) shiftop (mask : bool) : list basic_instruction :=
  BI_global_get global_mem_ptr ::
    load_local_i64 y ++
    [ BI_const_num 63%Z
    ; BI_relop T_i64 (Relop_i (ROI_lt SX_U))
    ; BI_if (BT_valtype (Some (T_num T_i64)))
        (load_local_i64 x ++
           load_local_i64 y ++
           BI_binop T_i64 (Binop_i shiftop) ::
           (if mask then bitmask_instrs else []))
        [ BI_const_num 0%Z ]
    ; BI_store T_i64 None 2%N 0%N
    ; BI_global_get global_mem_ptr
    ] ++ increment_global_mem_ptr 8.

Definition mulc_instrs (x y : localidx) : list basic_instruction :=
  load_local_i64 x ++
    [ BI_const_num 62%Z ; BI_binop T_i64 (Binop_i (BOI_shr SX_U)) ; BI_testop T_i64 TO_eqz ] ++
    load_local_i64 y ++
    [ BI_const_num 62%Z ; BI_binop T_i64 (Binop_i (BOI_shr SX_U)) ; BI_testop T_i64 TO_eqz ] ++
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
    [ BI_const_num 31%Z ; BI_binop T_i64 (Binop_i (BOI_shr SX_U)) ; BI_global_set glob_tmp1 ] ++
    (* glob_tmp2 <- let lx = x & ((1 << 31) - 1) *)
    load_local_i64 x ++
    [ BI_const_num maxuint31 ; BI_binop T_i64 (Binop_i BOI_and) ; BI_global_set glob_tmp2 ] ++
    (* glob_tmp4 <- let hy =  y >> 31 *)
    [ BI_global_get glob_tmp3 ; BI_const_num 31%Z ; BI_binop T_i64 (Binop_i (BOI_shr SX_U)) ; BI_global_set glob_tmp4 ] ++
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
      ; BI_const_num 62%Z
      ; BI_binop T_i64 (Binop_i BOI_shl)
      ; BI_const_num maxuint63
      ; BI_binop T_i64 (Binop_i BOI_and)
      ; BI_binop T_i64 (Binop_i BOI_or)
      ; BI_global_set glob_tmp4
    ] ++
    (* glob_tmp1 <- let h = hxy >> 1 = glob_tmp1 >> 1 *)
    [ BI_global_get glob_tmp1
      ; BI_const_num 1%Z
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
      ; BI_const_num 31%Z
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
            ; BI_const_num 1%Z
            ; BI_binop T_i64 (Binop_i BOI_add)
            ; BI_global_set glob_tmp1
          ]
          [ ]
    ] ++
    (* glob_tmp1 <- let h = h + (hl >> 32) *)
    [ BI_global_get glob_tmp1
      ; BI_global_get glob_tmp3
      ; BI_const_num 32%Z
      ; BI_binop T_i64 (Binop_i (BOI_shr SX_U))
      ; BI_binop T_i64 (Binop_i BOI_add)
      ; BI_const_num maxuint63
      ; BI_binop T_i64 (Binop_i BOI_and)
      ; BI_global_set glob_tmp1
    ] ++
    load_local_i64 x ++
    [ BI_const_num 62%Z
      ; BI_binop T_i64 (Binop_i (BOI_shr SX_U))
      ; BI_testop T_i64 TO_eqz
    ] ++
    load_local_i64 y ++
    [ BI_const_num 62%Z
      ; BI_binop T_i64 (Binop_i (BOI_shr SX_U))
      ; BI_testop T_i64 TO_eqz
      ; BI_binop T_i32 (Binop_i BOI_or)
      ; BI_if (BT_valtype None)
          [ ]
          [ (* glob_tmp2 <- let l' := l + (x << 62) *)
            BI_global_get glob_tmp4
            ; BI_local_get x
            ; BI_load T_i64 None 2%N 0%N
            ; BI_const_num 62%Z
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
                  ; BI_const_num 1%Z
                  ; BI_binop T_i64 (Binop_i BOI_add)
                  ; BI_global_set glob_tmp1
                ]
                [ ]
                (* return (h + (x >> 1), l') *)
            ; BI_global_get glob_tmp1
            ; BI_local_get x
            ; BI_load T_i64 None 2%N 0%N
            ; BI_const_num 1%Z
            ; BI_binop T_i64 (Binop_i (BOI_shr SX_U))
            ; BI_binop T_i64 (Binop_i BOI_add)
            ; BI_const_num maxuint63
            ; BI_binop T_i64 (Binop_i BOI_and)
            ; BI_global_set glob_tmp1
            ; BI_global_get glob_tmp2
            ; BI_global_set glob_tmp4
          ]
    ] ++ make_product glob_tmp1 glob_tmp4.

Definition diveucl_instrs (x y : localidx) : list basic_instruction :=
  [ BI_local_get x
    ; BI_load T_i64 None 2%N 0%N
    ; BI_testop T_i64 TO_eqz
    ; BI_if (BT_valtype None)
        [ BI_const_num (VAL_int64 (Z_to_i64 0))
          ; BI_global_set glob_tmp1
          ; BI_const_num 0%Z
          ; BI_global_set glob_tmp2
        ]
        [ BI_local_get y
          ; BI_load T_i64 None 2%N 0%N
          ; BI_testop T_i64 TO_eqz
          ; BI_if (BT_valtype None)
              [ BI_const_num (VAL_int64 (Z_to_i64 0))
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
  ] ++ make_product glob_tmp1 glob_tmp2.

Definition translate_primitive_binary_op op (x y : localidx) : error (list basic_instruction) :=
  match op with
  | PrimInt63add       => Ret (apply_binop_and_store_i64 BOI_add x y true)
  | PrimInt63sub       => Ret (apply_binop_and_store_i64 BOI_sub x y true)
  | PrimInt63mul       => Ret (apply_binop_and_store_i64 BOI_mul x y true)
  | PrimInt63div       => Ret (div_instrs x y)
  | PrimInt63mod       => Ret (mod_instrs x y)
  | PrimInt63lsl       => Ret (shift_instrs x y BOI_shl true)
  | PrimInt63lsr       => Ret (shift_instrs x y (BOI_shr SX_U) false)
  | PrimInt63land      => Ret (apply_binop_and_store_i64 BOI_and x y false)
  | PrimInt63lor       => Ret (apply_binop_and_store_i64 BOI_or x y false)
  | PrimInt63lxor      => Ret (apply_binop_and_store_i64 BOI_xor x y false)
  | PrimInt63eqb       => Ret (make_boolean_valued_comparison x y ROI_eq)
  | PrimInt63ltb       => Ret (make_boolean_valued_comparison x y (ROI_lt SX_U))
  | PrimInt63leb       => Ret (make_boolean_valued_comparison x y (ROI_le SX_U))
  | PrimInt63compare   => Ret (compare_instrs x y)
  | PrimInt63addc      => Ret (apply_exact_add_operation x y false)
  | PrimInt63addcarryc => Ret (apply_exact_add_operation x y true)
  | PrimInt63subc      => Ret (apply_exact_sub_operation x y false)
  | PrimInt63subcarryc => Ret (apply_exact_sub_operation x y true)
  | PrimInt63mulc      => Ret (mulc_instrs x y)
  | PrimInt63diveucl   => Ret (diveucl_instrs x y)
  | _ => Err "Unknown primitive binary operator"
  end.

(* head0 x computes the leading number of zeros in x
   OBS: need to subtract 1 since we're dealing with 63-bit integers *)
Definition head0_instrs (x : localidx) : list basic_instruction :=
  BI_global_get global_mem_ptr ::
    load_local_i64 x ++
    [ BI_unop T_i64 (Unop_i UOI_clz)
      ; BI_const_num 1%Z
      ; BI_binop T_i64 (Binop_i BOI_sub)
      ; BI_store T_i64 None 2%N 0%N
      ; BI_global_get global_mem_ptr
    ] ++ increment_global_mem_ptr 8.

(* tail0 x computes the trailing number of zeros in x
   OBS: if x is 0, then result is 63 (can't just use wasm ctz op) ) *)
Definition tail0_instrs (x : localidx) : list basic_instruction :=
  BI_global_get global_mem_ptr ::
    load_local_i64 x ++
    [ BI_testop T_i64 TO_eqz
      ; BI_if (BT_valtype (Some (T_num T_i64)))
          [ BI_const_num 63%Z ]
          (load_local_i64 x ++ [ BI_unop T_i64 (Unop_i UOI_ctz) ])
      ; BI_store T_i64 None 2%N 0%N
      ; BI_global_get global_mem_ptr
    ] ++ increment_global_mem_ptr 8.

Definition translate_primitive_unary_op op (x : localidx) : error (list basic_instruction) :=
  match op with
  | PrimInt63head0 => Ret (head0_instrs x)
  | PrimInt63tail0 => Ret (tail0_instrs x)
  | _ => Err "Unknown primitive unary operator"
  end.

Definition diveucl_21_loop_body :=
  [ BI_global_get glob_tmp1
  ; BI_const_num 1%Z
  ; BI_binop T_i64 (Binop_i BOI_shl)
  ; BI_global_get glob_tmp2
  ; BI_const_num 62%Z
  ; BI_binop T_i64 (Binop_i (BOI_shr SX_U))
  ; BI_binop T_i64 (Binop_i BOI_or)
  ; BI_global_set glob_tmp1

  ; BI_global_get glob_tmp2
  ; BI_const_num 1%Z
  ; BI_binop T_i64 (Binop_i BOI_shl)
  ; BI_const_num maxuint63
  ; BI_binop T_i64 (Binop_i (BOI_rem SX_U))
  ; BI_global_set glob_tmp2

  ; BI_global_get glob_tmp3
  ; BI_const_num 1%Z
  ; BI_binop T_i64 (Binop_i BOI_shl)
  ; BI_const_num maxuint63
  ; BI_binop T_i64 (Binop_i BOI_and)
  ; BI_global_set glob_tmp3

  ; BI_global_get glob_tmp1
  ; BI_global_get glob_tmp4
  ; BI_relop T_i64 (Relop_i (ROI_ge SX_U))
  ; BI_if (BT_valtype None)
      [ BI_global_get glob_tmp3
      ; BI_const_num 1%Z
      ; BI_binop T_i64 (Binop_i BOI_or)
      ; BI_global_set glob_tmp3
      ; BI_global_get glob_tmp1
      ; BI_global_get glob_tmp4
      ; BI_binop T_i64 (Binop_i BOI_sub)
      ; BI_global_set glob_tmp1
      ]
      [ ]
  ].

Definition diveucl_21_instrs (xh xl y : localidx) : list basic_instruction :=
  load_local_i64 y ++ [ BI_global_set glob_tmp4 ] ++
    load_local_i64 xh ++ [ BI_global_set glob_tmp1 ] ++
    [ BI_global_get glob_tmp4
      ; BI_global_get glob_tmp1
      ; BI_relop T_i64 (Relop_i (ROI_le SX_U))
      ; BI_if (BT_valtype (Some (T_num T_i32)))
          ([ BI_const_num 0%Z ; BI_global_set glob_tmp1 ] ++ make_product glob_tmp1 glob_tmp1)
          (load_local_i64 xl ++
             [ BI_global_set glob_tmp2
               ; BI_const_num 0%Z
               ; BI_global_set glob_tmp3
             ] ++ (List.flat_map (fun x => x) (List.repeat diveucl_21_loop_body 63)) ++
             [ BI_global_get glob_tmp1
               ; BI_const_num maxuint63
               ; BI_binop T_i64 (Binop_i BOI_and)
               ; BI_global_set glob_tmp1
             ] ++ (make_product glob_tmp3 glob_tmp1))
    ].


Definition addmuldiv_instrs p x y :=
  BI_global_get global_mem_ptr ::
    load_local_i64 p ++
    [ BI_const_num 63%Z
      ; BI_relop T_i64 (Relop_i (ROI_gt SX_U))
      ; BI_if (BT_valtype (Some (T_num T_i64)))
          [ BI_const_num 0%Z ]
          (* Compute x << p on the stack *)
          (load_local_i64 x ++
             load_local_i64 p ++
             [ BI_binop T_i64 (Binop_i BOI_shl)
               ; BI_const_num maxuint63
               ; BI_binop T_i64 (Binop_i BOI_and)
             ] ++
             (* Put y on the stack *)
             load_local_i64 y ++
             (* Compute 63 - p on the stack *)
             [ BI_const_num 63%Z ] ++
             load_local_i64 p ++
             [ BI_binop T_i64 (Binop_i BOI_sub)
             (* Compute y >> (63 - p) on the stack *)
             ; BI_binop T_i64 (Binop_i (BOI_shr SX_U))
             (* Finally, compute (x << p) | (y >> (63 - p)) on the stack *)
             ; BI_binop T_i64 (Binop_i BOI_or)
             ])
      ; BI_store T_i64 None 2%N 0%N
      ; BI_global_get global_mem_ptr
    ] ++ increment_global_mem_ptr 8.

Definition translate_primitive_ternary_op op (x y z : localidx) : error (list basic_instruction) :=
  match op with
  | PrimInt63diveucl_21 => Ret (diveucl_21_instrs x y z)
  | PrimInt63addmuldiv  => Ret (addmuldiv_instrs x y z)
  | _ => Err "Unknown primitive ternary operator"
  end.

(* Transparent apply_binop_and_store_i64 div_instrs mod_instrs shift_instrs make_boolean_valued_comparison compare_instrs apply_exact_add_operation apply_exact_sub_operation make_carry diveucl_instrs mulc_instrs load_local_i64 increment_global_mem_ptr bitmask_instrs nat_to_i32val. *)

Definition LambdaANF_primInt_arith_fun (f : uint63 -> uint63 -> uint63) (x y : uint63) := Vprim (primInt (f x y)).

Definition LambdaANF_primInt_bool_fun (f : uint63 -> uint63 -> bool) x y :=
  if f x y then
    Vconstr true_tag []
  else
    Vconstr false_tag [].

Definition LambdaANF_primInt_compare_fun (f : uint63 -> uint63 -> comparison) x y :=
  match f x y with
  | Datatypes.Eq => Vconstr eq_tag []
  | Datatypes.Lt => Vconstr lt_tag []
  | Datatypes.Gt => Vconstr gt_tag []
  end.

Definition LambdaANF_primInt_carry_fun (f : uint63 -> uint63 -> carry uint63) x y :=
  match f x y with
  | C0 z => Vconstr c0_tag [ Vprim (primInt z) ]
  | C1 z => Vconstr c1_tag [ Vprim (primInt z) ]
  end.

Definition LambdaANF_primInt_prod_fun (f : uint63 -> uint63 -> prod uint63 uint63) x y :=
  let p := f x y in
  Vconstr pair_tag [ Vprim (primInt (fst p)) ; Vprim (primInt (snd p)) ].

Definition LambdaANF_primInt_unop_fun (f : uint63 -> uint63) x := Vprim (primInt (f x)).

Definition LambdaANF_primInt_diveucl_21 xh xl y :=
  let (q, r) := diveucl_21 xh xl y in
  Vconstr pair_tag [ Vprim (primInt q) ; Vprim (primInt r) ].

Definition LambdaANF_primInt_addmuldiv p x y := Vprim (primInt (addmuldiv p x y)).

Definition apply_LambdaANF_primInt_operator op (vs : list val) : option val :=
  match vs with
  | [ Vprim (primInt x) ] =>
      match op with
      | PrimInt63head0 => Some (LambdaANF_primInt_unop_fun Uint63.head0 x)
      | PrimInt63tail0 => Some (LambdaANF_primInt_unop_fun Uint63.tail0 x)
      | _ => None
      end
  | [ Vprim ( (primInt x) ) ; Vprim ( (primInt y) ) ] =>
      match op with
      | PrimInt63add => Some (LambdaANF_primInt_arith_fun Uint63.add x y)
      | PrimInt63sub => Some (LambdaANF_primInt_arith_fun Uint63.sub x y)
      | PrimInt63mul => Some (LambdaANF_primInt_arith_fun Uint63.mul x y)
      | PrimInt63div => Some (LambdaANF_primInt_arith_fun Uint63.div x y)
      | PrimInt63mod => Some (LambdaANF_primInt_arith_fun Uint63.mod x y)
      | PrimInt63lsl => Some (LambdaANF_primInt_arith_fun Uint63.lsl x y)
      | PrimInt63lsr => Some (LambdaANF_primInt_arith_fun Uint63.lsr x y)
      | PrimInt63land => Some (LambdaANF_primInt_arith_fun Uint63.land x y)
      | PrimInt63lor => Some (LambdaANF_primInt_arith_fun Uint63.lor x y)
      | PrimInt63lxor => Some (LambdaANF_primInt_arith_fun Uint63.lxor x y)
      | PrimInt63eqb => Some (LambdaANF_primInt_bool_fun Uint63.eqb x y)
      | PrimInt63ltb => Some (LambdaANF_primInt_bool_fun Uint63.ltb x y)
      | PrimInt63leb => Some (LambdaANF_primInt_bool_fun Uint63.leb x y)
      | PrimInt63compare => Some (LambdaANF_primInt_compare_fun Uint63.compare x y)
      | PrimInt63addc => Some (LambdaANF_primInt_carry_fun Uint63.addc x y)
      | PrimInt63addcarryc => Some (LambdaANF_primInt_carry_fun Uint63.addcarryc x y)
      | PrimInt63subc => Some (LambdaANF_primInt_carry_fun Uint63.subc x y)
      | PrimInt63subcarryc => Some (LambdaANF_primInt_carry_fun Uint63.subcarryc x y)
      | PrimInt63mulc => Some (LambdaANF_primInt_prod_fun Uint63.mulc x y)
      | PrimInt63diveucl => Some (LambdaANF_primInt_prod_fun Uint63.diveucl x y)
      | _ => None
      end
  | [ Vprim (primInt x) ; Vprim (primInt y) ; Vprim (primInt z) ] =>
      match op with
      | PrimInt63diveucl_21 => Some (LambdaANF_primInt_diveucl_21 x y z)
      | PrimInt63addmuldiv => Some (LambdaANF_primInt_addmuldiv x y z)
      | _ => None
      end
  | _ => None
  end.


Lemma uint63_mod_modulus_id :
  forall (x : uint63), Int64.Z_mod_modulus (to_Z x) = to_Z x.
Proof.
  intros.
  rewrite Int64.Z_mod_modulus_id. reflexivity.
  assert (0 <= to_Z x < wB)%Z by now apply to_Z_bounded.
  assert (wB < Int64.modulus)%Z. unfold Int64.modulus, Int64.half_modulus, two_power_nat. cbn. lia. lia.
Qed.

Corollary uint63_unsigned_id : forall (x : uint63), Int64.unsigned (to_Z x) = to_Z x.
Proof. intros; simpl; now rewrite uint63_mod_modulus_id. Qed.

Lemma Z_bitmask_modulo_equivalent :
  forall (n : Z), Z.land n maxuint63 = Z.modulo n wB.
Proof.
  intros; now (replace maxuint63 with (Z.ones 63); [rewrite Z.land_ones|cbn]).
Qed.

Lemma int64_bitmask_modulo :
  forall (x : Z),  Int64.iand x maxuint63 = Z.modulo x wB.
Proof.
  intros.
  unfold Int64.iand, Int64.and. simpl.
  rewrite Int64.Z_mod_modulus_eq.
  rewrite Int64.modulus_twice_half_modulus.
  replace (Z.land (x mod (2 * Int64.half_modulus)) 9223372036854775807) with (Z.modulo (x mod (2 * Int64.half_modulus)) Int64.half_modulus) by now rewrite Z_bitmask_modulo_equivalent.
  now rewrite Zaux.Zmod_mod_mult.
Qed.

Lemma uint63_eq_int64_eq :
  forall x y, to_Z x = to_Z y -> Int64.eq (to_Z x) (to_Z y) = true.
Proof.
  intros; unfold Int64.eq; rewrite H; now rewrite zeq_true.
Qed.

Lemma uint63_neq_int64_neq :
  forall x y, to_Z x <> to_Z y -> Int64.eq (to_Z x) (to_Z y) = false.
Proof.
  intros; unfold Int64.eq; do 2 rewrite uint63_unsigned_id; now rewrite zeq_false.
Qed.

Lemma to_Z_neq_uint63_eqb_false :
  forall x y, to_Z x <> to_Z y -> (x =? y)%uint63 = false.
Proof.
  intros; rewrite eqb_false_spec; intro Hcontra; now rewrite Hcontra in H.
Qed.

Local Ltac solve_arith_op d1 d2 spec :=
  intros; unfold d1, d2; (repeat rewrite uint63_unsigned_id); (try rewrite int64_bitmask_modulo); now rewrite spec.

Lemma uint63_add_i64_add : forall x y, Int64.iand (Int64.iadd (to_Z x) (to_Z y)) maxuint63 = to_Z (x + y).
Proof. solve_arith_op Int64.iadd Int64.add add_spec. Qed.

Lemma uint63_sub_i64_sub : forall x y, Int64.iand (Int64.isub (to_Z x) (to_Z y)) maxuint63 = to_Z (x - y).
Proof. solve_arith_op Int64.isub Int64.sub sub_spec. Qed.

Lemma uint63_mul_i64_mul : forall x y, Int64.iand (Int64.imul (to_Z x) (to_Z y)) maxuint63 = to_Z (x * y).
Proof. solve_arith_op Int64.imul Int64.mul mul_spec. Qed.

Local Ltac solve_div_mod d1 d2 spec :=
  intros; unfold d1, d2;
  repeat rewrite uint63_unsigned_id;
  rewrite spec;
  now (replace Int64.zero with (Int64.repr (to_Z 0)); [rewrite uint63_neq_int64_neq|rewrite to_Z_0]).

Lemma uint63_div_i64_div : forall x y,
    to_Z y <> to_Z 0 -> Int64.idiv_u (to_Z x) (to_Z y) = Some (Int64.repr (to_Z (x / y))).
Proof. solve_div_mod Int64.idiv_u Int64.divu div_spec. Qed.

Lemma uint63_div0 : forall x y,
    to_Z y = to_Z 0 -> to_Z (x / y) = to_Z 0.
Proof.
  intros; rewrite div_spec, H, to_Z_0; unfold Z.div, Z.div_eucl; now destruct (to_Z x).
Qed.

Lemma uint63_mod_i64_mod : forall x y,
    to_Z y <> to_Z 0 -> Int64.irem_u (to_Z x) (to_Z y) = Some (Int64.repr (to_Z (x mod y))).
Proof. solve_div_mod Int64.irem_u Int64.modu mod_spec. Qed.

Lemma uint63_mod0 : forall x y,
    to_Z y = to_Z 0 -> to_Z (x mod y) = to_Z x.
Proof.
  intros; rewrite mod_spec, H, to_Z_0; unfold Z.modulo, Z.div_eucl; now destruct (to_Z x).
Qed.

Lemma uint63_land_i64_and : forall x y, Int64.iand (to_Z x) (to_Z y) = to_Z (x land y).
Proof. solve_arith_op Int64.iand Int64.and land_spec'. Qed.

Lemma uint63_lor_i64_or : forall x y, Int64.ior (to_Z x) (to_Z y) = to_Z (x lor y).
Proof. solve_arith_op Int64.ior Int64.or lor_spec'. Qed.

Lemma uint63_lxor_i64_xor : forall x y, Int64.ixor (to_Z x) (to_Z y) = to_Z (x lxor y).
Proof. solve_arith_op Int64.ixor Int64.xor lxor_spec'. Qed.

End Primitives.
