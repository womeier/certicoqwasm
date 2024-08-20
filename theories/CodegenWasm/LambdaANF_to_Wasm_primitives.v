From Coq Require Import POrderedType ZArith BinNat List Lia Uint63 Program.
From Wasm Require Import datatypes operations numerics host opsem properties common.
Import Wasm_int.

Require Import compcert.lib.Coqlib.

From CertiCoq Require Import
  LambdaANF.toplevel LambdaANF.cps_util LambdaANF.cps LambdaANF.cps_show
  Common.Common Common.compM Common.Pipeline_utils.

Require Import ExtLib.Structures.Monad.
From MetaCoq Require Import Common.Kernames Utils.bytestring Utils.MCString.

Import ssreflect MonadNotation SigTNotations.

Notation "'primInt' x" := (AstCommon.primInt ; x) (at level 0).

(* Define convenience wrappers as notations to allow easy unfolding during proofs *)
Notation uint63 := Uint63.int.
Notation Z_to_i64 z := (Int64.repr z).
Notation Z_to_VAL_i64 z := (VAL_int64 (Int64.repr z)).
Notation nat_to_VAL_i32 n := (VAL_int32 (Wasm_int.Int32.repr (BinInt.Z.of_nat n))).
Notation N_to_VAL_i32 n := (VAL_int32 (Wasm_int.Int32.repr (BinInt.Z.of_N n))).

Local Coercion Z_to_i64_co z := Z_to_i64 z.
Local Coercion Z_to_i64val_co z := Z_to_VAL_i64 z.

(* Avoid unfolding during proofs *)
Opaque Uint63.to_Z.

Section TRANSLATION.

Variables global_mem_ptr glob_tmp1 glob_tmp2 glob_tmp3 glob_tmp4 : globalidx.

Definition maxuint31 := 2147483647%Z.
Definition maxuint63 := 9223372036854775807%Z.


(* Ordinals of constructors *)
Definition true_ord  := 0%N.
Definition false_ord := 1%N.

Definition Eq_ord    := 0%N.
Definition Lt_ord    := 1%N.
Definition Gt_ord    := 2%N.

Definition C0_ord    := 0%N.
Definition C1_ord    := 1%N.

Definition pair_ord  := 0%N.


(* **** TRANSLATE PRIMITIVE VALUES **** *)

Definition translate_primitive_value (p : AstCommon.primitive) : error Wasm_int.Int64.int :=
  match projT1 p as tag return prim_value tag -> error Wasm_int.Int64.T with
  | AstCommon.primInt => fun i => Ret (Wasm_int.Int64.repr (Uint63.to_Z i))
  | AstCommon.primFloat => fun f => Err "Extraction of floats to Wasm not yet supported"
  end (projT2 p).

(* **** TRANSLATE PRIMITIVE OPERATIONS **** *)

(* Path of the PrimInt63 module in the kernel: Coq.Numbers.Cyclic.Int63.PrimInt63 *)
Definition primInt63ModPath : Kernames.modpath :=
  Kernames.MPfile [ "PrimInt63"%bs ; "Int63"%bs ; "Cyclic"%bs ; "Numbers"%bs ; "Coq"%bs ].

(* Supported operators defined as data type to avoid pattern matching on kernel name (bytestrings) *)
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

Definition load_local_i64 (i : localidx) : list basic_instruction :=
  [ BI_local_get i ; BI_load T_i64 None 2%N 0%N ].

Definition increment_global_mem_ptr i :=
  [ BI_global_get global_mem_ptr
  ; BI_const_num (N_to_VAL_i32 i)
  ; BI_binop T_i32 (Binop_i BOI_add)
  ; BI_global_set global_mem_ptr
  ].

Definition bitmask_instrs := [ BI_const_num maxuint63 ; BI_binop T_i64 (Binop_i BOI_and) ].

Definition apply_binop_and_store_i64 (op : binop_i) (x y : localidx) (apply_bitmask : bool) : list basic_instruction :=
  BI_global_get global_mem_ptr ::                   (* Address to store the result of the operation *)
  load_local_i64 x ++                               (* Load the arguments onto the stack *)
  load_local_i64 y ++
  [ BI_binop T_i64 (Binop_i op) ] ++
  (if apply_bitmask then bitmask_instrs else []) ++ (* apply bitmask to zero MSB if necessary *)
  [ BI_store T_i64 None 2%N 0%N                     (* Store the result *)
  ; BI_global_get global_mem_ptr                    (* Put the result address on the stack *)
  ] ++
  increment_global_mem_ptr 8%N.

(* Assume argument is stored in global gidx *)
Definition make_carry (ord : N) (gidx : globalidx) : list basic_instruction:=
  [ BI_global_get global_mem_ptr
  ; BI_global_get gidx
  ; BI_store T_i64 None 2%N 0%N
  ; BI_global_get global_mem_ptr
  ; BI_const_num (N_to_VAL_i32 ord)
  ; BI_store T_i32 None 2%N 8%N
  ; BI_global_get global_mem_ptr
  ; BI_global_get global_mem_ptr
  ; BI_store T_i32 None 2%N 12%N
  ; BI_global_get global_mem_ptr
  ; BI_const_num (nat_to_VAL_i32 8)
  ; BI_binop T_i32 (Binop_i BOI_add)
  ] ++ increment_global_mem_ptr 16%N.

Definition apply_add_carry_operation (x y : localidx) (addone : bool) : list basic_instruction :=
    load_local_i64 x ++ load_local_i64 y ++
    [ BI_binop T_i64 (Binop_i BOI_add) ] ++
    (if addone then
       [ BI_const_num 1%Z ; BI_binop T_i64 (Binop_i BOI_add) ]
     else []) ++
    bitmask_instrs ++
    [BI_global_set glob_tmp1 ;BI_global_get glob_tmp1 ] ++
    load_local_i64 x ++
    [ BI_relop T_i64 (Relop_i ((if addone then ROI_le else ROI_lt) SX_U))
    ; BI_if (BT_valtype (Some (T_num T_i32))) (make_carry C1_ord glob_tmp1) (make_carry C0_ord glob_tmp1)
    ].

Definition apply_sub_carry_operation (x y : localidx) (subone : bool) : list basic_instruction :=
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
    ; BI_if (BT_valtype (Some (T_num T_i32))) (make_carry C0_ord glob_tmp1) (make_carry C1_ord glob_tmp1)
    ].

(* Assume 1st element is stored in global gidx1, 2nd element in global gidx2 *)
Definition make_product (gidx1 gidx2 : N) : list basic_instruction :=
  [ BI_global_get global_mem_ptr
  ; BI_global_get gidx1
  ; BI_store T_i64 None 2%N 0%N
  ; BI_global_get global_mem_ptr
  ; BI_global_get gidx2
  ; BI_store T_i64 None 2%N 8%N
  ; BI_global_get global_mem_ptr
  ; BI_const_num (N_to_VAL_i32 pair_ord)
  ; BI_store T_i32 None 2%N 16%N
  ; BI_global_get global_mem_ptr
  ; BI_global_get global_mem_ptr
  ; BI_store T_i32 None 2%N 20%N
  ; BI_global_get global_mem_ptr
  ; BI_global_get global_mem_ptr
  ; BI_const_num (nat_to_VAL_i32 8)
  ; BI_binop T_i32 (Binop_i BOI_add)
  ; BI_store T_i32 None 2%N 24%N
  ; BI_global_get global_mem_ptr
  ; BI_const_num (nat_to_VAL_i32 16)
  ; BI_binop T_i32 (Binop_i BOI_add)
  ] ++ increment_global_mem_ptr 28%N.

Definition make_boolean_valued_comparison x y relop : list basic_instruction :=
  load_local_i64 x ++            (* Load the arguments onto the stack *)
  load_local_i64 y ++
  [ BI_relop T_i64 (Relop_i relop)
  ; BI_if (BT_valtype (Some (T_num T_i32)))
      [ BI_const_num (N_to_VAL_i32 (2 * true_ord + 1)) ]
      [ BI_const_num (N_to_VAL_i32 (2 * false_ord + 1)) ]
  ].


Definition compare_instrs x y : list basic_instruction :=
  [ BI_local_get x
    ; BI_load T_i64 None 2%N 0%N
    ; BI_local_get y
    ; BI_load T_i64 None 2%N 0%N
    ; BI_relop T_i64 (Relop_i (ROI_lt SX_U))
    ; BI_if (BT_valtype (Some (T_num T_i32)))
        [ BI_const_num (N_to_VAL_i32 (2 * Lt_ord + 1)) ]
        (load_local_i64 x ++
           load_local_i64 y ++
           [ BI_relop T_i64 (Relop_i ROI_eq)
           ; BI_if (BT_valtype (Some (T_num T_i32)))
               [ BI_const_num (N_to_VAL_i32 (2 * Eq_ord + 1)) ]
               [ BI_const_num (N_to_VAL_i32 (2 * Gt_ord + 1)) ]
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
    ] ++ increment_global_mem_ptr 8%N.


Definition mod_instrs (x y : localidx) : list basic_instruction :=
  BI_global_get global_mem_ptr ::
    load_local_i64 y ++
    [ BI_testop T_i64 TO_eqz
    ; BI_if (BT_valtype (Some (T_num T_i64)))
        (load_local_i64 x)
        (load_local_i64 x ++ load_local_i64 y ++ [ BI_binop T_i64 (Binop_i (BOI_rem SX_U)) ])
    ; BI_store T_i64 None 2%N 0%N
    ; BI_global_get global_mem_ptr
    ] ++ increment_global_mem_ptr 8%N.

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
    ] ++ increment_global_mem_ptr 8%N.

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
  | PrimInt63addc      => Ret (apply_add_carry_operation x y false)
  | PrimInt63addcarryc => Ret (apply_add_carry_operation x y true)
  | PrimInt63subc      => Ret (apply_sub_carry_operation x y false)
  | PrimInt63subcarryc => Ret (apply_sub_carry_operation x y true)
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
    ] ++ increment_global_mem_ptr 8%N.

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
    ] ++ increment_global_mem_ptr 8%N.

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
    ] ++ increment_global_mem_ptr 8%N.

Definition translate_primitive_ternary_op op (x y z : localidx) : error (list basic_instruction) :=
  match op with
  | PrimInt63diveucl_21 => Ret (diveucl_21_instrs x y z)
  | PrimInt63addmuldiv  => Ret (addmuldiv_instrs x y z)
  | _ => Err "Unknown primitive ternary operator"
  end.

End TRANSLATION.

Section WRAPPERS.

(* **** Define LambdaANF wrapper functions for Coq's 63 bit integer operators  **** *)

(* LambdaANF constructor values 'Vconstr t vs' hold the tag 't' of the constructor and a list of values 'vs'.
   The tag is NOT the same as the ordinal used in the translation section above,
   and the tag of a specific constructor is NOT guaranteed to always be the same,
   it depends on the program being extracted.

   For the proof, we define 'wrapper' functions for the primitive operators,
   and for primitive operators that return a constructor value, the wrapper function is parameterized over the tags
   since we don't know the concrete values of the tags.

   For convenience, we define the tags as section variables.
 *)
Variables true_tag false_tag eq_tag lt_tag gt_tag c0_tag c1_tag pair_tag : ctor_tag.

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

(* Define a partial function for applying a primitive operator.
   The result is only defined if the operator is supported and the arguments
   match the type of the Coq operator.
   E.g 'add' has the type 'uint63 -> uint63 -> uint63' so the arguments must be
   2 primitive integer values and the return value is a primitive integer. *)
Definition apply_LambdaANF_primInt_operator op (vs : list val) : option val :=
  match vs with
  | [ Vprim (primInt x) ] =>
      match op with
      | PrimInt63head0 => Some (LambdaANF_primInt_unop_fun Uint63.head0 x)
      | PrimInt63tail0 => Some (LambdaANF_primInt_unop_fun Uint63.tail0 x)
      | _ => None
      end
  | [ Vprim (primInt x) ; Vprim (primInt y) ] =>
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

End WRAPPERS.

Ltac dep_destruct_primint v p x :=
  try dependent destruction v; try discriminate; dependent destruction p; dependent destruction x; try discriminate.

Section CORRECTNESS.

Context `{ho : host}.

(* Arguments to primitive operations can only be primInts
   (Eventually adapt for floats) *)
Lemma apply_primop_only_defined_on_primInts :
  forall op vs v true_tag false_tag eq_tag lt_tag gt_tag c0_tag c1_tag pair_tag,
    apply_LambdaANF_primInt_operator true_tag false_tag eq_tag lt_tag gt_tag c0_tag c1_tag pair_tag op vs = Some v ->
    forall v',
      List.In v' vs -> exists n, v' = Vprim (primInt n).
Proof.
  intros.
  unfold apply_LambdaANF_primInt_operator in H.
  destruct vs=>//. destruct vs; destruct v0=>//; destruct p =>//; destruct x =>//.
  destruct H0=>//. now exists p.
  destruct vs; destruct v1=>//; destruct p0 =>//; destruct x =>//.
  destruct H0. now exists p. destruct H0. now exists p0. destruct H0.
  destruct vs; destruct v0=>//; destruct p1 =>//; destruct x =>//.
  destruct H0. now exists p. destruct H0. now exists p0. destruct H0. now exists p1. destruct H0.
Qed.

(* Well-formedness of the primitive function (and constructor) environment:
   Applying a (supported) primitive operator evaluates to a (LambdaANF) value,
   and the constructor environment contains all constructors that may be returned,
   and the constructors have the expected ordinals (i.e. the ones used in the translation section).
 *)
Definition prim_funs_env_wellformed (cenv : ctor_env) (penv : prim_env) (prim_funs : M.t (list val -> option val)) : Prop :=
  forall p op_name s b n op f vs v,
    M.get p penv = Some (op_name, s, b, n) ->       (* penv = primitive function environment obtained from previous pipeline stage *)
    KernameMap.find op_name primop_map = Some op -> (* primop_map = environment of supported primitive operations *)
    M.get p prim_funs = Some f ->                   (* from lambdaANF operational semantics *)
    f vs = Some v ->
    exists true_tag false_tag it_bool eq_tag lt_tag gt_tag it_comparison c0_tag c1_tag it_carry pair_tag it_prod,
      (* This links operational semantics to primitive operators in penv *)
      apply_LambdaANF_primInt_operator true_tag false_tag eq_tag lt_tag gt_tag c0_tag c1_tag pair_tag op vs = Some v
      (* Constructor tags (bools, comparison, carry and prod) used by prim ops *)
      /\ M.get true_tag cenv = Some (Build_ctor_ty_info (Common.BasicAst.nNamed "true") (Common.BasicAst.nNamed "bool") it_bool 0%N true_ord)
      /\ M.get false_tag cenv = Some (Build_ctor_ty_info (Common.BasicAst.nNamed "false") (Common.BasicAst.nNamed "bool") it_bool 0%N false_ord)
      /\ M.get eq_tag cenv = Some (Build_ctor_ty_info (Common.BasicAst.nNamed "Eq") (Common.BasicAst.nNamed "comparison") it_comparison 0%N Eq_ord)
      /\ M.get lt_tag cenv = Some (Build_ctor_ty_info (Common.BasicAst.nNamed "Lt") (Common.BasicAst.nNamed "comparison") it_comparison 0%N Lt_ord)
      /\ M.get gt_tag cenv = Some (Build_ctor_ty_info (Common.BasicAst.nNamed "Gt") (Common.BasicAst.nNamed "comparison") it_comparison 0%N Gt_ord)
      /\ M.get c0_tag cenv = Some (Build_ctor_ty_info (Common.BasicAst.nNamed "C0") (Common.BasicAst.nNamed "carry") it_carry 1%N C0_ord)
      /\ M.get c1_tag cenv = Some (Build_ctor_ty_info (Common.BasicAst.nNamed "C1") (Common.BasicAst.nNamed "carry") it_carry 1%N C1_ord)
      /\ M.get pair_tag cenv = Some (Build_ctor_ty_info (Common.BasicAst.nNamed "pair") (Common.BasicAst.nNamed "prod") it_prod 1%N pair_ord).

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
  replace (Z.land (x mod (2 * Int64.half_modulus)) 9223372036854775807)
    with (Z.modulo (x mod (2 * Int64.half_modulus)) Int64.half_modulus) by now rewrite Z_bitmask_modulo_equivalent.
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

Lemma uint63_lt_int64_lt :
  forall x y, (to_Z x < to_Z y)%Z -> Int64.ltu (to_Z x) (to_Z y) = true.
Proof. intros; unfold Int64.ltu; repeat rewrite uint63_unsigned_id; now rewrite zlt_true. Qed.

Lemma uint63_nlt_int64_nlt :
  forall x y, ~ (to_Z x < to_Z y)%Z -> Int64.ltu (to_Z x) (to_Z y) = false.
Proof. intros; unfold Int64.ltu; do 2 rewrite uint63_unsigned_id; now rewrite zlt_false. Qed.

Lemma to_Z_nlt_uint63_ltb_false :
  forall x y, ~ (to_Z x < to_Z y)%Z -> (x <? y)%uint63 = false.
Proof. intros; have H' := reflect_iff _ _ (ltbP x y); now destruct (x <? y)%uint63. Qed.

Lemma uint63_le_int64_le :
  forall x y, (to_Z x <= to_Z y)%Z -> negb (Int64.ltu (to_Z y) (to_Z x)) = true.
Proof. intros; unfold Int64.ltu; repeat rewrite uint63_unsigned_id; rewrite zlt_false; auto; lia. Qed.

Lemma uint63_nle_int64_nle :
  forall x y, ~ (to_Z x <= to_Z y)%Z -> negb (Int64.ltu (to_Z y) (to_Z x)) = false.
Proof. intros; unfold Int64.ltu; do 2 rewrite uint63_unsigned_id; rewrite zlt_true; auto; lia. Qed.

Lemma to_Z_nle_uint63_leb_false :
  forall x y, ~ (to_Z x <= to_Z y)%Z -> (x <=? y)%uint63 = false.
Proof. intros; have H' := reflect_iff _ _ (lebP x y); now destruct (x <=? y)%uint63. Qed.

Local Ltac solve_arith_op d1 d2 spec :=
  intros; unfold d1, d2; (repeat rewrite uint63_unsigned_id); (try rewrite int64_bitmask_modulo); now rewrite spec.

(* Helper lemmas to show that the Wasm arithmetic is correct w.r.t. 63 bit arithmetic.
   Helps prove that E.g. the instructions

   i64.const x
   i64.const y
   i64.add
   i64.const (2^63 - 1)
   i64.and

   reduce to

   i64.const ((x + y) mod 2^63)
 *)
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
  intros; rewrite div_spec H to_Z_0; unfold Z.div, Z.div_eucl; now destruct (to_Z x).
Qed.

Lemma uint63_mod_i64_mod : forall x y,
    to_Z y <> to_Z 0 -> Int64.irem_u (to_Z x) (to_Z y) = Some (Int64.repr (to_Z (x mod y))).
Proof. solve_div_mod Int64.irem_u Int64.modu mod_spec. Qed.

Lemma uint63_mod0 : forall x y,
    to_Z y = to_Z 0 -> to_Z (x mod y) = to_Z x.
Proof.
  intros; rewrite mod_spec H to_Z_0; unfold Z.modulo, Z.div_eucl; now destruct (to_Z x).
Qed.

Lemma uint63_land_i64_and : forall x y, Int64.iand (to_Z x) (to_Z y) = to_Z (x land y).
Proof. solve_arith_op Int64.iand Int64.and land_spec'. Qed.

Lemma uint63_lor_i64_or : forall x y, Int64.ior (to_Z x) (to_Z y) = to_Z (x lor y).
Proof. solve_arith_op Int64.ior Int64.or lor_spec'. Qed.

Lemma uint63_lxor_i64_xor : forall x y, Int64.ixor (to_Z x) (to_Z y) = to_Z (x lxor y).
Proof. solve_arith_op Int64.ixor Int64.xor lxor_spec'. Qed.


Lemma lsl_bits_high : forall x y,
    (to_Z 63 <= to_Z y)%Z ->
    forall i, bit (x << y) i = false.
Proof.
  intros.
  destruct (digits <=? i)%uint63 eqn:Hi.
  now apply bit_M.
  rewrite bit_lsl; unfold digits in *.
  assert (to_Z i < to_Z 63)%Z as Hi1 by
      now destruct (reflect_dec _ _ (lebP 63 i)) as [H'|H']; [rewrite (reflect_iff _ _ (lebP 63 i)) in H'|].
  assert (to_Z i < to_Z y)%Z as Hi2 by now replace (to_Z 63) with 63%Z in *; [lia|cbn].
  now replace (i <? y)%uint63 with true; [cbn|rewrite (reflect_iff _ _ (ltbP i y)) in Hi2].
Qed.

Lemma uint63_bits_inj_0 i : (forall j, bit i j = false) -> i = 0%uint63.
Proof.
  intros.
  assert (forall n, bit i n = bit 0 n) by now intros; rewrite bit_0; apply H.
  now apply bit_ext.
Qed.

Lemma uint63_lsl63 : forall x y,
    (to_Z 63 <= to_Z y)%Z ->
    to_Z (x << y) = to_Z 0.
Proof.
  intros;
  now replace (x << y)%uint63 with 0%uint63;[reflexivity|rewrite (uint63_bits_inj_0 _ (lsl_bits_high x y H))].
Qed.

Lemma uint63_lsl_i64_shl : forall x y,
    (to_Z y < to_Z 63)%Z -> Int64.iand (Int64.ishl (to_Z x) (to_Z y)) maxuint63 = to_Z (x << y).
Proof.
  intros.
  have H' := to_Z_bounded y.
  unfold Int64.ishl, Int64.shl, Int64.wordsize, Integers.Wordsize_64.wordsize.
  replace (to_Z 63) with 63%Z in H by now cbn.
  do 2 rewrite uint63_unsigned_id.
  replace (Int64.unsigned (Z_to_i64 (to_Z y mod 64%nat))) with (to_Z y). 2: now rewrite Z.mod_small; [rewrite uint63_unsigned_id|].
  rewrite Z.shiftl_mul_pow2. 2: lia.
  now rewrite lsl_spec; rewrite int64_bitmask_modulo.
Qed.

Lemma uint63_lsr63 : forall x y,
    (to_Z 63 <= to_Z y)%Z ->
    to_Z (x >> y) = to_Z 0.
Proof.
  intros;
  rewrite (reflect_iff _ _ (lebP 63 y)) in H;
  now replace (x >> y)%uint63 with 0%uint63; [reflexivity|rewrite lsr_M_r].
Qed.

Lemma uint63_lsr_i64_shr : forall x y,
    (to_Z y < to_Z 63)%Z -> Int64.ishr_u (to_Z x) (to_Z y) = to_Z (x >> y).
Proof.
  intros.
  have H' := to_Z_bounded y.
  unfold Int64.ishr_u, Int64.shru, Int64.wordsize, Integers.Wordsize_64.wordsize.
  replace (to_Z 63) with 63%Z in H by now cbn.
  do 2 rewrite uint63_unsigned_id.
  replace (Int64.unsigned (Z_to_i64 (to_Z y mod 64%nat))) with (to_Z y). 2: now rewrite Z.mod_small; [rewrite uint63_unsigned_id|].
  rewrite Z.shiftr_div_pow2. 2: lia.
  now rewrite lsr_spec.
Qed.

Definition local_holds_address_to_i64 (sr : store_record) (fr : frame) (l : localidx) addr val (m : meminst) bs : Prop :=
    lookup_N fr.(f_locs) l = Some (VAL_num (VAL_int32 addr))
    /\ load m (N_of_uint i32m addr) 0%N (N.to_nat (tnum_length T_i64)) = Some bs
    /\ wasm_deserialise bs T_i64 = (VAL_int64 val).

End CORRECTNESS.
