From Coq Require Import POrderedType ZArith BinNat List Lia Uint63 Program Relations.Relations Relations.Relation_Operators.

From Wasm Require Import datatypes operations numerics host opsem properties common.
Import Wasm_int.

Require Import compcert.lib.Coqlib.

From CertiCoq Require Import
  LambdaANF.toplevel LambdaANF.cps_util LambdaANF.cps LambdaANF.cps_show
  Common.Common Common.compM Common.Pipeline_utils.

Require Import ExtLib.Structures.Monad.
From MetaCoq Require Import Common.Kernames Utils.bytestring Utils.MCString.

Import eqtype ssrbool eqtype seq ListNotations ssreflect MonadNotation SigTNotations.

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

Variables glob_mem_ptr glob_tmp1 glob_tmp2 glob_tmp3 glob_tmp4 loop_counter : globalidx.

Definition maxuint31 := 2147483647%Z.
Definition maxuint63 := 9223372036854775807%Z.


(* Ordinals of constructors *)
Definition true_ord  := 1%N.
Definition false_ord := 0%N.

Definition Eq_ord    := 0%N.
Definition Lt_ord    := 1%N.
Definition Gt_ord    := 2%N.

Definition C0_ord    := 0%N.
Definition C1_ord    := 1%N.

Definition pair_ord  := 0%N.


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
  [ BI_local_get i ; BI_load T_i64 None {| memarg_offset:=0%N; memarg_align:=2%N |} ].

Definition increment_glob_mem_ptr i :=
  [ BI_global_get glob_mem_ptr
  ; BI_const_num (N_to_VAL_i32 i)
  ; BI_binop T_i32 (Binop_i BOI_add)
  ; BI_global_set glob_mem_ptr
  ].

Definition bitmask_instrs := [ BI_const_num maxuint63 ; BI_binop T_i64 (Binop_i BOI_and) ].

Definition apply_binop_and_store_i64 (op : binop_i) (x y : localidx) (apply_bitmask : bool) : list basic_instruction :=
  BI_global_get glob_mem_ptr ::                   (* Address to store the result of the operation *)
  load_local_i64 x ++                               (* Load the arguments onto the stack *)
  load_local_i64 y ++
  [ BI_binop T_i64 (Binop_i op) ] ++
  (if apply_bitmask then bitmask_instrs else []) ++ (* apply bitmask to zero MSB if necessary *)
  [ BI_store T_i64 None {| memarg_offset:=0%N; memarg_align:=2%N |} (* Store the result *)
  ; BI_global_get glob_mem_ptr                    (* Put the result address on the stack *)
  ] ++
  increment_glob_mem_ptr 8%N.

(* Assume argument is stored in global gidx *)
Definition make_carry (ord : N) (gidx : globalidx) : list basic_instruction:=
  [ BI_global_get glob_mem_ptr
  ; BI_global_get gidx
  ; BI_store T_i64 None {| memarg_offset:=0%N; memarg_align:=2%N |}
  ; BI_global_get glob_mem_ptr
  ; BI_const_num (N_to_VAL_i32 ord)
  ; BI_store T_i32 None {| memarg_offset:=8%N; memarg_align:=2%N |}
  ; BI_global_get glob_mem_ptr
  ; BI_global_get glob_mem_ptr
  ; BI_store T_i32 None {| memarg_offset:=12%N; memarg_align:=2%N |}
  ; BI_global_get glob_mem_ptr
  ; BI_const_num (nat_to_VAL_i32 8)
  ; BI_binop T_i32 (Binop_i BOI_add)
  ] ++ increment_glob_mem_ptr 16%N.

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
  [ BI_global_get glob_mem_ptr
  ; BI_global_get gidx1
  ; BI_store T_i64 None {| memarg_offset:=0%N; memarg_align:=2%N |}
  ; BI_global_get glob_mem_ptr
  ; BI_global_get gidx2
  ; BI_store T_i64 None {| memarg_offset:=8%N; memarg_align:=2%N |}
  ; BI_global_get glob_mem_ptr
  ; BI_const_num (N_to_VAL_i32 pair_ord)
  ; BI_store T_i32 None {| memarg_offset:=16%N; memarg_align:=2%N |}
  ; BI_global_get glob_mem_ptr
  ; BI_global_get glob_mem_ptr
  ; BI_store T_i32 None {| memarg_offset:=20%N; memarg_align:=2%N |}
  ; BI_global_get glob_mem_ptr
  ; BI_global_get glob_mem_ptr
  ; BI_const_num (nat_to_VAL_i32 8)
  ; BI_binop T_i32 (Binop_i BOI_add)
  ; BI_store T_i32 None {| memarg_offset:=24%N; memarg_align:=2%N |}
  ; BI_global_get glob_mem_ptr
  ; BI_const_num (nat_to_VAL_i32 16)
  ; BI_binop T_i32 (Binop_i BOI_add)
  ] ++ increment_glob_mem_ptr 28%N.

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
  ; BI_load T_i64 None {| memarg_offset:=0%N; memarg_align:=2%N |}
  ; BI_local_get y
  ; BI_load T_i64 None {| memarg_offset:=0%N; memarg_align:=2%N |}
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
  BI_global_get glob_mem_ptr ::
    load_local_i64 y ++
    [ BI_testop T_i64 TO_eqz
    ; BI_if (BT_valtype (Some (T_num T_i64)))
        [ BI_const_num 0%Z ]
        (load_local_i64 x ++ load_local_i64 y ++ [ BI_binop T_i64 (Binop_i (BOI_div SX_U)) ])
    ; BI_store T_i64 None {| memarg_offset:=0%N; memarg_align:=2%N |}
    ; BI_global_get glob_mem_ptr
    ] ++ increment_glob_mem_ptr 8%N.


Definition mod_instrs (x y : localidx) : list basic_instruction :=
  BI_global_get glob_mem_ptr ::
    load_local_i64 y ++
    [ BI_testop T_i64 TO_eqz
    ; BI_if (BT_valtype (Some (T_num T_i64)))
        (load_local_i64 x)
        (load_local_i64 x ++ load_local_i64 y ++ [ BI_binop T_i64 (Binop_i (BOI_rem SX_U)) ])
    ; BI_store T_i64 None {| memarg_offset:=0%N; memarg_align:=2%N |}
    ; BI_global_get glob_mem_ptr
    ] ++ increment_glob_mem_ptr 8%N.

Definition shift_instrs (x y : localidx) shiftop (mask : bool) : list basic_instruction :=
  BI_global_get glob_mem_ptr ::
    load_local_i64 y ++
    [ BI_const_num 63%Z
    ; BI_relop T_i64 (Relop_i (ROI_lt SX_U))
    ; BI_if (BT_valtype (Some (T_num T_i64)))
        (load_local_i64 x ++
         load_local_i64 y ++
         BI_binop T_i64 (Binop_i shiftop) ::
         (if mask then bitmask_instrs else []))
        [ BI_const_num 0%Z ]
    ; BI_store T_i64 None {| memarg_offset:=0%N; memarg_align:=2%N |}
    ; BI_global_get glob_mem_ptr
    ] ++ increment_glob_mem_ptr 8%N.

Definition low32 := [ BI_const_num 4294967295%Z ; BI_binop T_i64 (Binop_i BOI_and) ].
Definition high32 := [ BI_const_num 32%Z ; BI_binop T_i64 (Binop_i (BOI_shr SX_U)) ].

Definition mulc_instrs (x y : localidx) : list basic_instruction :=
  (* Compute cross products *)
  (* glob_tmp1 = xlow * ylow *)
  load_local_i64 x ++ low32 ++
  load_local_i64 y ++ low32 ++
  [ BI_binop T_i64 (Binop_i BOI_mul) ; BI_global_set glob_tmp1 ] ++
  (* glob_tmp2 = xhigh * ylow *)
  load_local_i64 x ++ high32 ++
  load_local_i64 y ++ low32 ++
  [ BI_binop T_i64 (Binop_i BOI_mul) ; BI_global_set glob_tmp2 ] ++
  (* glob_tmp3 = xlow * yhigh *)
  load_local_i64 x ++ low32 ++
  load_local_i64 y ++ high32 ++
  [ BI_binop T_i64 (Binop_i BOI_mul) ; BI_global_set glob_tmp3 ] ++
  (* glob_tmp4 = xhigh * yhigh *)
  load_local_i64 x ++ high32 ++
  load_local_i64 y ++ high32 ++
  [ BI_binop T_i64 (Binop_i BOI_mul) ; BI_global_set glob_tmp4 ] ++
  (* Add the cross products together *)
  [ BI_global_get glob_tmp1 ] ++ high32 ++ (* (xlow * ylow) >> 32 *)
  [ BI_global_get glob_tmp2 ] ++ low32 ++ (* (xhigh * ylow) & 0xFFFFFFFF *)
  [ BI_binop T_i64 (Binop_i BOI_add)
  ; BI_global_get glob_tmp3
  ; BI_binop T_i64 (Binop_i BOI_add)
  (* We don't need xlow * yhigh, so we can store the intermediate cross in glob_tmp3  *)
  ; BI_global_set glob_tmp3
  ] ++
  [ BI_global_get glob_tmp2 ] ++ high32 ++
  [ BI_global_get glob_tmp3 ] ++ high32 ++
  [ BI_binop T_i64 (Binop_i BOI_add) ] ++
  [ BI_global_get glob_tmp4
  ; BI_binop T_i64 (Binop_i BOI_add)
  ; BI_global_set glob_tmp2 (* glob_tmp2 = upper 64 bits of 128 bit product *)
  ] ++
  [ BI_global_get glob_tmp3 ; BI_const_num 32%Z ; BI_binop T_i64 (Binop_i BOI_shl) ] ++
  [ BI_global_get glob_tmp1 ] ++ low32 ++
  [ BI_binop T_i64 (Binop_i BOI_or)
  ; BI_global_set glob_tmp1 (* glob_tmp1 = lower 64 bits of 128 bit product *)
  ] ++
  (* Now adjust such that glob_tmp2 = upper _63_ bits of _126_ bit product *)
  [ BI_global_get glob_tmp2
  ; BI_const_num 1%Z
  ; BI_binop T_i64 (Binop_i BOI_shl)
  ; BI_global_get glob_tmp1
  ; BI_const_num 63%Z
  ; BI_binop T_i64 (Binop_i (BOI_shr SX_U))
  ; BI_binop T_i64 (Binop_i BOI_add)
  ; BI_global_set glob_tmp2
  ] ++
  (* And glob_tmp1 = lower _63_ bits of _126_ bit product *)
  [ BI_global_get glob_tmp1
  ; BI_const_num maxuint63
  ; BI_binop T_i64 (Binop_i BOI_and)
  ; BI_global_set glob_tmp1
  ] ++ make_product glob_tmp2 glob_tmp1. (* (upper, lower) *)


Definition diveucl_instrs (x y : localidx) : list basic_instruction :=
  [ BI_local_get x
  ; BI_load T_i64 None {| memarg_offset:=0%N; memarg_align:=2%N |}
  ; BI_testop T_i64 TO_eqz
  ; BI_if (BT_valtype None)
      [ BI_const_num (VAL_int64 (Z_to_i64 0))
      ; BI_global_set glob_tmp1
      ; BI_const_num 0%Z
      ; BI_global_set glob_tmp2
      ]
      [ BI_local_get y
      ; BI_load T_i64 None {| memarg_offset:=0%N; memarg_align:=2%N |}
      ; BI_testop T_i64 TO_eqz
      ; BI_if (BT_valtype None)
          [ BI_const_num (VAL_int64 (Z_to_i64 0))
          ; BI_global_set glob_tmp1
          ; BI_local_get x
          ; BI_load T_i64 None {| memarg_offset:=0%N; memarg_align:=2%N |}
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
  BI_global_get glob_mem_ptr ::
    load_local_i64 x ++
    [ BI_unop T_i64 (Unop_i UOI_clz)
    ; BI_const_num 1%Z
    ; BI_binop T_i64 (Binop_i BOI_sub)
    ; BI_store T_i64 None {| memarg_offset:=0%N; memarg_align:=2%N |}
    ; BI_global_get glob_mem_ptr
    ] ++ increment_glob_mem_ptr 8%N.

(* tail0 x computes the trailing number of zeros in x
   OBS: if x is 0, then result is 63 (can't just use wasm ctz op) ) *)
Definition tail0_instrs (x : localidx) : list basic_instruction :=
  BI_global_get glob_mem_ptr ::
    load_local_i64 x ++
    [ BI_testop T_i64 TO_eqz
    ; BI_if (BT_valtype (Some (T_num T_i64)))
        [ BI_const_num 63%Z ]
        (load_local_i64 x ++ [ BI_unop T_i64 (Unop_i UOI_ctz) ])
    ; BI_store T_i64 None {| memarg_offset:=0%N; memarg_align:=2%N |}
    ; BI_global_get glob_mem_ptr
    ] ++ increment_glob_mem_ptr 8%N.

Definition translate_primitive_unary_op op (x : localidx) : error (list basic_instruction) :=
  match op with
  | PrimInt63head0 => Ret (head0_instrs x)
  | PrimInt63tail0 => Ret (tail0_instrs x)
  | _ => Err "Unknown primitive unary operator"
  end.

Definition diveucl_21_loop_body glob_xh glob_xl glob_y glob_q :=
  [ BI_global_get glob_xl
  ; BI_const_num 1%Z
  ; BI_binop T_i64 (Binop_i BOI_shl)
  ; BI_global_set glob_xl
  (* xl := xl << 1 *)

  ; BI_global_get glob_xh
  ; BI_const_num 1%Z
  ; BI_binop T_i64 (Binop_i BOI_shl)
  ; BI_global_get glob_xl
  ; BI_const_num 63%Z
  ; BI_binop T_i64 (Binop_i (BOI_shr SX_U))
  ; BI_binop T_i64 (Binop_i BOI_or)
  ; BI_global_set glob_xh
  (* xh := (xh << 1) || (xl >> 63) *)

  ; BI_global_get glob_q
  ; BI_const_num 1%Z
  ; BI_binop T_i64 (Binop_i BOI_shl)
  ; BI_global_set glob_q
  (* q := q << 1 *)

  ; BI_global_get glob_xh
  ; BI_global_get glob_y
  ; BI_relop T_i64 (Relop_i (ROI_ge SX_U))
  (* if xh >= y: *)
  ; BI_if (BT_valtype None)
      ([ BI_global_get glob_q
       ; BI_const_num 1%Z
       ; BI_binop T_i64 (Binop_i BOI_or)
       ; BI_global_set glob_q
       (* q := q || 1 *)
       ] ++
       [ BI_global_get glob_xh
       ; BI_global_get glob_y
       ; BI_binop T_i64 (Binop_i BOI_sub)
       ; BI_global_set glob_xh
       (* xh := xh - y *)
       ])
      []
  ].

Definition diveucl_21_loop glob_xh glob_xl glob_y glob_q iterations :=
  [ BI_global_get loop_counter
  ; BI_const_num (VAL_int32 (Int32.repr iterations))
  ; BI_relop T_i32 (Relop_i (ROI_lt SX_U))
  ; BI_if (BT_valtype None)
      ((diveucl_21_loop_body glob_xh glob_xl glob_y glob_q) ++
       [ BI_global_get loop_counter
       ; BI_const_num (VAL_int32 (Int32.repr 1))
       ; BI_binop T_i32 (Binop_i BOI_add)
       ; BI_global_set loop_counter
       ; BI_br 1%N
       ])
      []
  ].

Definition diveucl_21_instrs (xh xl y : localidx) : list basic_instruction :=
  load_local_i64 y ++
    load_local_i64 xh ++
    [ BI_relop T_i64 (Relop_i (ROI_le SX_U))
    ; BI_if (BT_valtype (Some (T_num T_i32)))
        (* if y <= xh, then the result is always 0 *)
        ([ BI_const_num 0%Z ; BI_global_set glob_tmp1] ++ make_product glob_tmp1 glob_tmp1)
        ( (* glob_tmp1 = xh *)
          load_local_i64 xh ++ [ BI_global_set glob_tmp1 ] ++
          (* glob_tmp2 = xl *)
          load_local_i64 xl ++ [ BI_global_set glob_tmp2 ] ++
          (* glob_tmp3 = y *)
          load_local_i64 y  ++ [ BI_global_set glob_tmp3 ] ++
          [ (* glob_tmp4 = q (the quotient, initialised to 0) *)
          BI_const_num (VAL_int64 (Int64.repr 0%Z))
          ; BI_global_set glob_tmp4
          (* Initialise the loop counter to 0 *)
          ; BI_const_num (VAL_int32 (Int32.repr 0%Z))
          ; BI_global_set loop_counter

          (* execute 62 iterations of the loop *)
          ; BI_loop (BT_valtype None) (diveucl_21_loop glob_tmp1 glob_tmp2 glob_tmp3 glob_tmp4 63%Z)
          ] ++ (make_product glob_tmp4 glob_tmp1))
    ].


Definition addmuldiv_instrs p x y :=
  BI_global_get glob_mem_ptr ::
    load_local_i64 p ++
    [ BI_const_num 63%Z
    ; BI_relop T_i64 (Relop_i (ROI_gt SX_U))
    ; BI_if (BT_valtype (Some (T_num T_i64)))
        [ BI_const_num 0%Z ]
        (* Compute x << p on the stack *)
        (load_local_i64 x ++
           load_local_i64 p ++
           [ BI_binop T_i64 (Binop_i BOI_shl) ] ++
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
           ; BI_const_num maxuint63
           ; BI_binop T_i64 (Binop_i BOI_and)
           ])
    ; BI_store T_i64 None {| memarg_offset:=0%N; memarg_align:=2%N |}
    ; BI_global_get glob_mem_ptr
    ] ++ increment_glob_mem_ptr 8%N.

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

(* TODO: Consider what to do for the case where xh < y
   When the dividend (xh * 2^63 + xl) is too large, the quotient will overflow,
   but the behavior of diveucl_21 in that case is not specified as an axiom,
   but all VM/ native implementations return (0, 0) *)
Definition LambdaANF_primInt_diveucl_21 xh xl y :=
  if (y <=? xh)%uint63 then
    Vconstr pair_tag [ Vprim (primInt 0%uint63) ; Vprim (primInt 0%uint63) ]
  else
    Vconstr pair_tag [ Vprim (primInt (fst (diveucl_21 xh xl y))) ; Vprim (primInt (snd (diveucl_21 xh xl y))) ].

Definition LambdaANF_primInt_addmuldiv p x y := Vprim (primInt (addmuldiv p x y)).

(* Define a partial function for applying a primitive operator.
   The result is only defined if the operator is supported and the arguments
   match the type of the Coq operator.
   E.g 'add' has the type 'uint63 -> uint63 -> uint63' so the arguments must be
   2 primitive integer values and the return value is a primitive integer. *)
Definition apply_LambdaANF_primInt_operator op (vs : list cps.val) : option cps.val :=
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

Context {glob_tmp1 glob_tmp2 glob_tmp3 glob_tmp4 : globalidx}.

Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

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
Definition prim_funs_env_wellformed (cenv : ctor_env) (penv : prim_env) (prim_funs : M.t (list cps.val -> option cps.val)) : Prop :=
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
      /\ M.get pair_tag cenv = Some (Build_ctor_ty_info (Common.BasicAst.nNamed "pair") (Common.BasicAst.nNamed "prod") it_prod 2%N pair_ord).

Hint Resolve eq_sym eq_trans : core.
Hint Extern 1 => symmetry : core.

Remark int64_modulus_eq_pow64 : Int64.modulus = (2^64)%Z.
Proof. now unfold Int64.modulus, Int64.half_modulus, two_power_nat. Qed.

Hint Resolve int64_modulus_eq_pow64 : core.

Lemma uint63_lt_pow64 : forall (x : uint63), (0 <= to_Z x < 2^64)%Z.
Proof.
  intros; have H := (to_Z_bounded x).
  cbn in H.
  lia.
Qed.

Hint Resolve uint63_lt_pow64 : core.

Lemma lt_pow64_mod_modulus_id : forall x, (0 <= x < 2^64)%Z -> Int64.Z_mod_modulus x = x.
Proof.
  intros. now rewrite Int64.Z_mod_modulus_id.
Qed.

Hint Resolve lt_pow64_mod_modulus_id : core.

Lemma lt_pow64_unsigned_id : forall x, (0 <= x < 2^64)%Z -> Int64.unsigned x = x.
Proof.
  intros. now cbn.
Qed.

Hint Resolve lt_pow64_unsigned_id : core.

Corollary uint63_mod_modulus_id : forall (x : uint63), Int64.Z_mod_modulus (to_Z x) = to_Z x.
Proof. intros; auto. Qed.

Hint Resolve uint63_mod_modulus_id : core.

Corollary uint63_unsigned_id : forall (x : uint63), Int64.unsigned (to_Z x) = to_Z x.
Proof. intros; auto. Qed.

Hint Resolve uint63_unsigned_id : core.

Hint Resolve Z.mod_pos_bound : core.

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

Lemma uint63_add_i64_add' : forall x y z,
    Int64.iand (Int64.iadd (Int64.iadd (to_Z x) (to_Z y)) (to_Z z)) maxuint63 = to_Z (x + y + z).
Proof.
  intros. unfold Int64.iadd, Int64.add.
  do 3 rewrite uint63_unsigned_id.
  rewrite int64_bitmask_modulo.
  cbn. rewrite Int64.Z_mod_modulus_eq.
  rewrite Int64.modulus_twice_half_modulus.
  rewrite -Zplus_mod_idemp_l.
  rewrite Zaux.Zmod_mod_mult; [|lia|now cbn].
  now do 2 rewrite -add_spec.
Qed.

Lemma uint63_sub_i64_sub : forall x y, Int64.iand (Int64.isub (to_Z x) (to_Z y)) maxuint63 = to_Z (x - y).
Proof. solve_arith_op Int64.isub Int64.sub sub_spec. Qed.

Lemma uint63_sub_i64_sub' : forall x y z,
    Int64.iand (Int64.isub (Int64.isub (to_Z x) (to_Z y)) (to_Z z)) maxuint63 = to_Z (x - y - z).
Proof.
  intros. unfold Int64.isub, Int64.sub.
  do 3 rewrite uint63_unsigned_id.
  rewrite int64_bitmask_modulo.
  cbn. rewrite Int64.Z_mod_modulus_eq.
  rewrite Int64.modulus_twice_half_modulus.
  rewrite -Zminus_mod_idemp_l.
  rewrite Zaux.Zmod_mod_mult; [|lia|now cbn].
  now do 2 rewrite -sub_spec.
Qed.

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

Lemma uint63_diveucl_0 : forall x y,
    to_Z y = to_Z 0 ->
    to_Z (fst (diveucl x y)) = to_Z 0 /\ to_Z (snd (diveucl x y)) = to_Z x.
Proof.
  intros.
  rewrite diveucl_def_spec; unfold diveucl_def; simpl.
  rewrite ->div_spec, ->mod_spec.
  unfold Z.div, Z.modulo, Z.div_eucl.
  split; rewrite H; destruct (to_Z x); auto.
Qed.

Definition local_holds_address_to_i64 (sr : store_record) (fr : frame) (l : localidx) addr val (m : meminst) bs : Prop :=
    lookup_N fr.(f_locs) l = Some (VAL_num (VAL_int32 addr))
    /\ load m (N_of_uint i32m addr) 0%N (N.to_nat (tnum_length T_i64)) = Some bs
    /\ wasm_deserialise bs T_i64 = (VAL_int64 val).

(* diveucl_21 *)

Definition div21_loop_invariant sr fr i xh xl xh' xl' y q :=
  sglob_val sr (f_inst fr) glob_tmp1 = Some (VAL_num (VAL_int64 (Int64.repr xh')))
  /\ sglob_val sr (f_inst fr) glob_tmp2 = Some (VAL_num (VAL_int64 (Int64.repr xl')))
  /\ sglob_val sr (f_inst fr) glob_tmp3 = Some (VAL_num (VAL_int64 (Int64.repr y)))
  /\ sglob_val sr (f_inst fr) glob_tmp4 = Some (VAL_num (VAL_int64 (Int64.repr q)))
  /\ (0 <= y < 2^63)%Z
  /\ (0 <= xh' < y)%Z
  /\ (0 <= q < 2^i)%Z
  /\ (xl' mod 2^64 = (xl * 2^i) mod 2^64)%Z
  /\ ((q * y + xh') * 2^(63 - i) + (xl mod 2^(63 - i)) = (xh mod y) * 2^63 + xl)%Z.

(* mulc *)

Lemma Z_bitmask_modulo32_equivalent :
  forall (n : Z), Z.land n 4294967295%Z = Z.modulo n (2^32)%Z.
Proof.
intros; replace 4294967295%Z with (Z.ones 32);[now rewrite Z.land_ones; lia|now cbn].
Qed.

Ltac unfold_modulus64 := unfold Int64.modulus, Int64.half_modulus, two_power_nat in *; cbn in *.

Ltac solve_unsigned_id := cbn; rewrite Int64.Z_mod_modulus_id; now replace Int64.modulus with (2^64)%Z.



Lemma lt_pow32_mod_modulus_id : forall x, (0 <= x < 2^32)%Z -> Int64.Z_mod_modulus x = x.
Proof.
  intros. rewrite Int64.Z_mod_modulus_id. reflexivity. rewrite int64_modulus_eq_pow64. lia.
Qed.

Hint Resolve lt_pow32_mod_modulus_id : core.

Lemma lt_pow32_unsigned_id : forall x, (0 <= x < 2^32)%Z -> Int64.unsigned x = x.
Proof. intros; now cbn. Qed.

Hint Resolve lt_pow32_unsigned_id : core.

Lemma low32_max_int32 : forall x,
    (0 <= x mod 2^32 < 2^32)%Z.
Proof. intros; lia. Qed.

Lemma low32_modulo64_id : forall x,
    Int64.unsigned (x mod 2^32)%Z = (x mod 2^32)%Z.
Proof. intros; auto. Qed.

Lemma low32_modulo64_id' : forall x,
    Int64.Z_mod_modulus (x mod 2^32)%Z = (x mod 2^32)%Z.
Proof. intros; auto. Qed.

Lemma int64_low32' : forall x,
    (0 <= x < 2^64)%Z -> (Int64.iand x 4294967295%Z = x mod 2^32)%Z.
Proof.
intros.
unfold Int64.iand, Int64.and.
replace (Int64.unsigned x) with x; auto.
replace (Int64.unsigned 4294967295%Z) with 4294967295%Z; auto.
now rewrite Z_bitmask_modulo32_equivalent.
Qed.

Lemma int64_low32 : forall x,
    (0 <= x < 2^64)%Z -> Int64.unsigned (Int64.iand x 4294967295%Z) = (x mod 2^32)%Z.
Proof.
intros. rewrite int64_low32'; auto.
Qed.

Lemma high32_max_int32 : forall x,
    (0 <= x < 2^64)%Z -> (0 <= x / 2^32 < 2^32)%Z.
Proof. lia. Qed.

Lemma high32_max_int32' : forall x,
    (0 <= x < 2^64)%Z -> (0 <= x / 4294967296 < 4294967296)%Z.
Proof. lia. Qed.

Lemma int64_high32 : forall x,
    (0 <= x < 2^64)%Z -> Int64.ishr_u x 32 = (x / 2^32)%Z.
Proof.
intros.
unfold Int64.ishr_u, Int64.shru.
replace (Int64.unsigned (Z_to_i64 (Int64.unsigned 32 mod Int64.wordsize))) with (Int64.unsigned 32%Z) by now cbn.
replace (Int64.unsigned x) with x; auto.
replace (Int64.unsigned 32%Z) with 32%Z; auto.
now rewrite Z.shiftr_div_pow2; auto.
Qed.

Lemma max32bit_mul_modulo64_id : forall x y,
  (0 <= x < 2^32)%Z -> (0 <= y < 2^32)%Z -> Int64.imul x y = (x * y)%Z.
Proof.
intros.
unfold Int64.imul, Int64.mul.
replace (Int64.unsigned x) with x; replace (Int64.unsigned y) with y; auto.
Qed.

Definition lo x := (x mod 2^32)%Z.
Definition hi x := (x / 2^32)%Z.
Definition cross x y := (hi (lo x * lo y) + lo (hi x * lo y) + lo x * hi y)%Z.
Definition lower x y := ((cross x y) * 2^32 + (lo (lo x * lo y)))%Z.
Definition upper x y := (hi (hi x * lo y) + hi (cross x y) + (hi x * hi y))%Z.

Hint Transparent lo hi cross lower upper : core.

Lemma lo_range : forall x, (0 <= x < 2^64)%Z -> (0 <= lo x < 2^32)%Z.
Proof. intros. eauto. Qed.

Lemma hi_range : forall x, (0 <= x < 2^64)%Z -> (0 <= hi x < 2^32)%Z.
Proof. intros. unfold hi; lia. Qed.

Lemma hi_range_63bit : forall x,
    (0 <= x < 2^63)%Z -> (0<= hi x < 2^31)%Z.
Proof. intros. unfold hi; lia. Qed.

Hint Resolve lo_range hi_range hi_range_63bit : core.

Lemma lo_hi_product_63bit : forall x y,
    (0 <= x < 2^63)%Z -> (0 <= y < 2^63)%Z -> (0 <= lo x * hi y <=  (2^32 - 1) * (2^31 - 1))%Z.
Proof.
intros ?? Hx Hy.
have Hxlo := lo_range x. have Hyhi := hi_range_63bit y Hy.
nia.
Qed.

Corollary hi_lo_product_63bit : forall x y,
    (0 <= x < 2^63)%Z -> (0 <= y < 2^63)%Z -> (0 <= hi x * lo y <= (2^31 - 1) * (2^32 - 1))%Z.
Proof.
intros. replace (hi x * lo y)%Z with (lo y * hi x)%Z by lia.
now apply lo_hi_product_63bit.
Qed.

Lemma lo_lo_product_63bit : forall x y,
    (0 <= x < 2^63)%Z -> (0 <= y < 2^63)%Z ->
    (0 <= lo x * lo y <= (2^32 -1) * (2^32 - 1))%Z.
Proof.
intros ?? Hx Hy.
have Hxlo := lo_range x. have Hylo := lo_range y.
nia.
Qed.

Lemma hi_hi_product_63bit : forall x y,
    (0 <= x < 2^63)%Z -> (0 <= y < 2^63)%Z -> (0 <= hi x * hi y <= (2^31 - 1) * (2^31 - 1))%Z.
Proof.
intros ?? Hx Hy.
have Hxhi := hi_range_63bit x Hx. have Hyhi := hi_range_63bit y Hy.
nia.
Qed.

Lemma lo_hi_lo_range : forall x y,
    (0 <= x < 2^63)%Z -> (0 <= y < 2^63)%Z -> (0<= lo (hi x * lo y) <= 2^32)%Z.
Proof.
intros ?? Hx Hy. have H := hi_lo_product_63bit x y Hx Hy. unfold lo, hi in *; lia.
Qed.

Lemma sum1_range : forall x y,
    (0 <= x < 2^63)%Z -> (0 <= y < 2^63)%Z ->
    (0 <= hi (lo x * lo y) + lo (hi x * lo y) <= 2^32-1 + 2^32-1)%Z.
Proof.
intros ?? Hx Hy.
have H := lo_lo_product_63bit x y Hx Hy. have H' := hi_lo_product_63bit x y Hx Hy.
unfold lo, hi in *; lia.
Qed.

Lemma sum1_i64 : forall x y,
    (0 <= x < 2^63)%Z -> (0 <= y < 2^63)%Z ->
    Int64.iadd (Int64.repr (hi (lo x * lo y))) (Int64.repr (lo (hi x * lo y))) = Int64.repr (hi (lo x * lo y) + lo (hi x * lo y))%Z.
Proof.
intros ?? Hx Hy.
unfold Int64.iadd, Int64.add.
have H := lo_lo_product_63bit x y Hx Hy. have H' := hi_lo_product_63bit x y Hx Hy.
repeat rewrite lt_pow64_unsigned_id. reflexivity.
all: unfold hi, lo in *; lia.
Qed.

Lemma cross_range : forall x y,
    (0 <= x < 2^63)%Z -> (0 <= y < 2^63)%Z ->
    (0 <= cross x y <= (2^32-1 + 2^32-1) + (2^32-1) * (2^31-1))%Z.
Proof.
intros ?? Hx Hy.
have H := sum1_range x y Hx Hy. have H' := lo_hi_product_63bit x y Hx Hy.
unfold cross, lo, hi in *; lia.
Qed.

Lemma cross_i64 : forall x y,
    (0 <= x < 2^63)%Z -> (0 <= y < 2^63)%Z ->
    Int64.iadd (Int64.repr (hi (lo x * lo y) + lo (hi x * lo y))) (Int64.repr (lo x * hi y)) = Int64.repr ((hi (lo x * lo y) + lo (hi x * lo y)) + lo x * hi y)%Z.
Proof.
  intros ?? Hx Hy.
  unfold Int64.iadd, Int64.add.
  have H := lo_lo_product_63bit x y Hx Hy.
  have H' := hi_lo_product_63bit x y Hx Hy.
  have H'' := lo_hi_product_63bit x y Hx Hy.
  repeat rewrite lt_pow64_unsigned_id; unfold hi, lo in *; auto; lia.
Qed.

Lemma hi_cross_range : forall x y,
    (0 <= x < 2^63)%Z -> (0 <= y < 2^63)%Z -> (0 <= hi (cross x y) <= 2^31)%Z.
Proof.
  intros ?? Hx Hy. have H := cross_range x y Hx Hy. unfold hi; lia.
Qed.

Lemma hi_hi_lo_range : forall x y,
    (0 <= x < 2^63)%Z -> (0 <= y < 2^63)%Z -> (0<= hi (hi x * lo y) <= 2^31 - 2)%Z.
Proof.
  intros ?? Hx Hy. have H := hi_lo_product_63bit x y Hx Hy. unfold hi in *; lia.
Qed.

Lemma sum2_range : forall x y,
    (0 <= x < 2^63)%Z -> (0 <= y < 2^63)%Z ->
    (0 <= hi (hi x * lo y) + hi (cross x y) <= (2^31 - 2) + 2^31)%Z.
Proof.
intros ?? Hx Hy.
have H := hi_cross_range x y Hx Hy. have H' := hi_hi_lo_range x y Hx Hy.
unfold hi in *; lia.
Qed.

Lemma sum2_i64 : forall x y,
    (0 <= x < 2^63)%Z -> (0 <= y < 2^63)%Z ->
    Int64.iadd (Int64.repr (hi (hi x * lo y))) (Int64.repr (hi (cross x y))) = Int64.repr (hi (hi x * lo y) + hi (cross x y))%Z.
Proof.
intros ?? Hx Hy.
have H := hi_cross_range x y Hx Hy. have H' := hi_hi_lo_range x y Hx Hy.
unfold Int64.iadd, Int64.add.
repeat rewrite lt_pow64_unsigned_id. reflexivity.
all: unfold hi in *; lia.
Qed.

Lemma upper_range : forall x y,
    (0 <= x < 2^63)%Z -> (0 <= y < 2^63)%Z ->
    (0 <= upper x y <= ((2^31 - 2) + 2^31) + (2^31 - 1) * (2^31-1))%Z.
Proof.
intros ?? Hx Hy.
have H := sum2_range x y Hx Hy. have H' := hi_hi_product_63bit x y Hx Hy.
unfold upper, hi in *; lia.
Qed.

Lemma upper_i64 : forall x y,
    (0 <= x < 2^63)%Z -> (0 <= y < 2^63)%Z ->
    Int64.iadd (Int64.repr (hi (hi x * lo y) + hi (cross x y))) (Int64.repr (hi x * hi y)) = Int64.repr ((hi (hi x * lo y) + hi (cross x y)) + hi x * hi y)%Z.
Proof.
intros ?? Hx Hy.
have H := sum2_range x y Hx Hy. have H' := hi_hi_product_63bit x y Hx Hy.
unfold Int64.iadd, Int64.add.
repeat rewrite lt_pow64_unsigned_id; auto; lia.
Qed.

Lemma lo_lo_lo_range : forall x y,
    (0 <= x < 2^63)%Z -> (0 <= y < 2^63)%Z -> (0 <= lo (lo x * lo y) < 2^32)%Z.
Proof.
  intros ?? Hx Hy. have H := lo_lo_product_63bit x y Hx Hy. unfold lo in *; lia.
Qed.

Lemma upper_shifted_range : forall x y,
    (0 <= x < 2^63)%Z -> (0 <= y < 2^63)%Z -> (0 <= (upper x y) * 2 <= 2^63-2)%Z.
Proof.
intros ?? Hx Hy. have H := upper_range x y Hx Hy; lia.
Qed.

Lemma upper_shifted_i64 : forall x y,
    (0 <= x < 2^63)%Z -> (0 <= y < 2^63)%Z ->
    Int64.ishl (Int64.repr (upper x y)) (Int64.repr 1) = Int64.repr (upper x y * 2)%Z.
Proof.
intros ?? Hx Hy. have H := upper_range x y Hx Hy.
unfold Int64.ishl, Int64.shl.
repeat rewrite lt_pow64_unsigned_id.
replace (1 mod Int64.wordsize)%Z with 1%Z by now cbn.
rewrite Z.shiftl_mul_pow2. f_equal. lia.
all: cbn; lia.
Qed.

Lemma lower_or_i64 : forall x y,
    (0 <= x < 2^63)%Z -> (0 <= y < 2^63)%Z ->
    Int64.ior (Int64.shl (Int64.repr (cross x y)) (Int64.repr 32)) (Int64.repr (lo (lo x * lo y))) = Int64.repr ((cross x y) * 2^32 + lo (lo x * lo y)).
Proof.
intros ?? Hx Hy.
have H := cross_range x y Hx Hy.
have H' := lo_lo_lo_range x y Hx Hy.
unfold Int64.ior.
rewrite Int64.shifted_or_is_add; unfold two_p, two_power_pos; auto.
repeat rewrite lt_pow64_unsigned_id; auto; lia.
cbn. lia.
rewrite lt_pow64_unsigned_id; cbn; lia.
Qed.

Lemma lower_shifted_range : forall x y,
    (0 <= x < 2^63)%Z -> (0 <= y < 2^63)%Z -> (0 <= (lower x y mod 2^64) / 2^63 <= 1)%Z.
Proof. intros ?? Hx Hy. lia. Qed.

Lemma lower_shifted_i64 : forall x y,
    (0 <= x < 2^63)%Z -> (0 <= y < 2^63)%Z ->
    Int64.ishr_u (Int64.repr (lower x y)) (Int64.repr 63) = Int64.repr ((lower x y) mod 2^64 / 2^63).
Proof.
intros ?? Hx Hy.
unfold Int64.ishr_u, Int64.shru.
replace (Int64.unsigned (Int64.repr (lower x y))) with ((lower x y) mod 2^64)%Z.
repeat rewrite lt_pow64_unsigned_id.
replace (63 mod Int64.wordsize)%Z with 63%Z by now cbn.
rewrite Z.shiftr_div_pow2. reflexivity.
lia. lia. cbn; lia. lia.
cbn. rewrite Int64.Z_mod_modulus_eq. now rewrite int64_modulus_eq_pow64.
Qed.

Lemma upper63_range : forall x y,
    (0 <= x < 2^63)%Z -> (0 <= y < 2^63)%Z ->
    (0 <= (upper x y) * 2 + ((lower x y mod 2^64) / 2^63) < 2^63)%Z.
Proof.
intros ?? Hx Hy.
have H := upper_shifted_range x y Hx Hy. have H' := lower_shifted_range x y Hx Hy.
lia.
Qed.

Lemma upper63_i64 : forall x y,
    (0 <= x < 2^63)%Z -> (0 <= y < 2^63)%Z ->
    Int64.iadd (Int64.repr (upper x y * 2)) (Int64.repr (lower x y mod 2^64 / 2^63)) = Int64.repr (upper x y * 2 + lower x y mod 2^64 / 2^63).
Proof.
  intros ?? Hx Hy.
  have H := upper_shifted_range _ _ Hx Hy.
  unfold Int64.iadd, Int64.add.
  repeat rewrite lt_pow64_unsigned_id; auto; lia.
Qed.

Lemma lower_of_product : forall x y,
    (0 <= x < 2^64)%Z -> (0 <= y < 2^64)%Z ->
    ((x * y) mod 2^64 = lower x y mod 2^64)%Z.
Proof.
  intros x y Hx Hy.
  unfold lower, cross, lo, hi. lia.
Qed.

Lemma upper_of_product : forall x y,
    (0 <= x < 2^64)%Z -> (0 <= y < 2^64)%Z ->
    ((x * y) / 2^64 = upper x y)%Z.
Proof.
  intros x y Hx Hy. unfold upper, cross, hi, lo. lia.
Qed.

Corollary decompose_product : forall x y,
    (0 <= x < 2^64)%Z -> (0 <= y < 2^64)%Z ->
    (x * y = 2^64 * upper x y + lower x y mod 2^64)%Z.
Proof.
  intros.
  unfold upper, lower, cross, lo, hi. lia.
Qed.

Lemma lower_of_product_63bit : forall x y,
    (0 <= x < 2^64)%Z -> (0 <= y < 2^64)%Z ->
    ((x * y) mod 2^63 = (lower x y) mod 2^63)%Z.
Proof.
  intros. unfold lower, cross, lo, hi. lia.
Qed.

Lemma upper_of_product_63bit : forall x y,
    (0 <= x < 2^64)%Z -> (0 <= y < 2^64)%Z ->
    ((x * y) / 2^63 = 2 * (upper x y) + ((lower x y mod 2^64) / 2^63))%Z.
Proof.
  intros. unfold upper, lower, cross, lo, hi. lia.
Qed.

Corollary decompose_product_63bit : forall x y,
 (0 <= x < 2^64)%Z -> (0 <= y < 2^64)%Z ->
 (x * y = (2 * (upper x y) + ((lower x y mod 2^64) / 2^63)) * 2^63 + (lower x y mod 2^63))%Z.
Proof.
  intros. unfold upper, lower, cross, lo, hi. lia.
Qed.

Lemma mulc_spec_alt : forall x y,
    to_Z (fst (mulc x y)) = (((to_Z x) * (to_Z y)) / 2^63)%Z /\ to_Z (snd (mulc x y)) = (((to_Z x) * (to_Z y)) mod 2^63)%Z.
Proof.
intros.
have Hspec := mulc_spec x y.
have Hx := to_Z_bounded x.
have Hy := to_Z_bounded y.
cbn in Hx, Hy, Hspec.
assert (0 <= to_Z (snd (mulc x y)) < 2^63)%Z as Hrem by apply to_Z_bounded.
lia.
Qed.

Theorem mulc_fst : forall x y,
    (to_Z (fst (mulc x y)) = ((2 * (upper (to_Z x) (to_Z y)) + ((lower (to_Z x) (to_Z y) mod 2^64) / 2^63))))%Z.
Proof.
intros.
destruct (mulc_spec_alt x y) as [Hfst _].
have Hx := to_Z_bounded x; have Hy := to_Z_bounded y.
rewrite <- upper_of_product_63bit; auto.
Qed.

Theorem mulc_snd : forall x y,
    (to_Z (snd (mulc x y)) = (lower (to_Z x) (to_Z y) mod 2^63))%Z.
Proof.
  intros.
  destruct (mulc_spec_alt x y) as [_ Hsnd].
  rewrite <-lower_of_product_63bit; auto.
Qed.

Lemma low32step : forall state sr fr num,
    (0 <= num < 2^64)%Z ->
    reduce state sr fr ([$VN (VAL_int64 (Int64.repr num))] ++ [ AI_basic (BI_const_num (VAL_int64 (Int64.repr 4294967295))) ] ++
                        [ AI_basic (BI_binop T_i64 (Binop_i BOI_and)) ])
           state sr fr [$VN (VAL_int64 (Int64.repr (lo num))) ].
Proof.
intros.
constructor. apply rs_binop_success. cbn.
unfold Int64.iand, Int64.and. cbn.
rewrite Z_bitmask_modulo32_equivalent.
now replace (Int64.Z_mod_modulus num) with num by now solve_unsigned_id.
Qed.

Lemma high32step : forall state sr fr num,
    (0<= num < 2^64)%Z ->
    reduce state sr fr ([$VN (VAL_int64 (Int64.repr num))] ++ [ AI_basic (BI_const_num (VAL_int64 (Int64.repr 32))) ] ++
                        [ AI_basic (BI_binop T_i64 (Binop_i (BOI_shr SX_U))) ])
           state sr fr [ $VN (VAL_int64 (Int64.repr (hi num))) ].
Proof.
intros.
constructor. apply rs_binop_success.
unfold app_binop. simpl.
rewrite int64_high32. reflexivity. lia.
Qed.

Lemma head0_spec_alt: forall x : uint63, (0 < φ (x)%uint63)%Z -> (to_Z (head0 x) = 62 - Z.log2 (to_Z x))%Z.
Proof.
  intros.
  have H' := head0_spec _ H.
  replace (wB/2)%Z with (2^62)%Z in H' by now cbn. replace wB with (2^63)%Z in H' by now cbn.
  destruct H'.
  assert (Hlog1: (Z.log2 (2^62) <= Z.log2 (2 ^ (to_Z (head0 x)) * to_Z x))%Z) by now apply Z.log2_le_mono.
  assert (Hlog2: (Z.log2 (2 ^ (to_Z (head0 x)) * to_Z x) < 63)%Z).
  apply Z.log2_lt_pow2; lia.
  replace (2 ^ (to_Z (head0 x)) * to_Z x)%Z with (to_Z x * 2 ^ (to_Z (head0 x)))%Z in Hlog1, Hlog2 by lia.
  rewrite Z.log2_mul_pow2 in Hlog1, Hlog2. 2: lia. 2: apply to_Z_bounded.
  replace (Z.log2 (2 ^ 62)) with 62%Z in Hlog1 by now rewrite Z.log2_pow2.
  lia.
Qed.

Lemma powserie_nonneg : forall l,
    (forall x, In x l -> 0 <= x)%Z ->
    (0 <= Zbits.powerserie l)%Z.
Proof.
  induction l.
  intros.
  discriminate.
  intros.
  unfold Zbits.powerserie.
  fold Zbits.powerserie.
  assert (In a (a :: l)) by (constructor; reflexivity).
  assert (0 <= a)%Z by now apply H.
  assert (forall x, In x l -> 0 <= x)%Z.
  intros.
  assert (In x (a :: l)). right. assumption.
  now apply H.
  assert (0 <= Zbits.powerserie l)%Z by now apply IHl.

  apply Z.add_nonneg_nonneg.
  have Htwop := two_p_gt_ZERO a H1. lia. lia.
Qed.

Lemma in_Z_one_bits_pow : forall l i,
    (i \in l) ->
    (forall x, In x l -> 0 <= x)%Z ->
    (2^i <= Zbits.powerserie l)%Z.
Proof.
  induction l; intros.
  discriminate.
  unfold Zbits.powerserie.
  destruct (Z.eq_dec i a).
  fold Zbits.powerserie.
  rewrite <-e.
  rewrite two_p_equiv.
  assert (0 <= Zbits.powerserie l)%Z. apply powserie_nonneg; auto.
  assert (forall x, In x l -> 0 <= x)%Z.
  intros.
  assert (In x (a :: l)). right. assumption.
  now apply H0.
  assumption.
  lia.
  fold Zbits.powerserie.
  assert (i \in l).
  have H' := in_cons a l i.
  have Hrefl := reflect_iff.
  have H''' := eqP.
  specialize (H''' _ i a).
  specialize (Hrefl _ _ H''').
  destruct Hrefl.
  destruct (i == a)%Z eqn:Heqb. specialize (H2 Logic.eq_refl). contradiction.
  rewrite orb_false_l in H'. auto.
  rewrite <-H'. assumption.
  assert (forall x, In x l -> 0 <= x)%Z.
  intros.
  assert (In x (a :: l)). right. assumption.
  now apply H0.
  assert (0 <= a)%Z. apply H0; auto. now constructor.
  have Htwop := two_p_gt_ZERO a H3.
  assert (2^i <= Zbits.powerserie l)%Z. apply IHl; auto. lia.
Qed.

Lemma one_bits_non_zero : forall n x,
    0 < n ->
    (0 < x < two_power_nat n)%Z ->
    Zbits.Z_one_bits n x 0%Z <> nil.
Proof.
  intros.
  have Hz := Zbits.Z_one_bits_zero n 0.
  intro Hcontra.
  rewrite <-Hz in Hcontra.
  have Hps := Zbits.Z_one_bits_powerserie n x.
  assert (0 <= x < two_power_nat n)%Z by lia. apply Hps in H1. rewrite Hcontra in H1. rewrite Hz in H1. cbn in H1. lia.
Qed.

Lemma convert_from_bits_head : forall l i,
             i < size l ->
             i = find (fun b => b == true)  l ->
             (fun b => b == true) (nth false l i) = true ->
             (forall k, k < i -> (fun b => b == true) (nth false l k) = false) ->
             (Zbits.powerserie (Int64.convert_from_bits_to_Z_one_bits l) < two_p (Z.of_nat ((size l - i) - 1) + 1))%Z.
Proof.
assert (Hhead : forall l i',
             i' < size l ->
             i' = find (fun b => b==true) l ->
             (fun b => b == true) (nth false l i') = true ->
             (forall k, k < i' -> (fun b => b == true) (nth false l k) = false) ->
             exists l', Z.of_nat ((seq.size l) - i' - 1) :: l' = Int64.convert_from_bits_to_Z_one_bits l). {
    induction l.
    now intros.
    intros i' Hi1 Hi2 Hi3 Hk.
    simpl.
    simpl in Hi1.
    simpl in Hi2.
    destruct a.
    rewrite Hi2.
    rewrite Nat.sub_0_r. exists (Int64.convert_from_bits_to_Z_one_bits l).
    simpl. rewrite Nat.sub_0_r.
    reflexivity.
    simpl in Hi2.
    simpl in IHl.
    assert (i' - 1 =  (find (fun b => b == true) l)). rewrite Hi2. simpl. rewrite Nat.sub_0_r. reflexivity.
    assert (forall k, k < (i' - 1) -> (fun b => b == true) (nth false l k) = false). {
      intros k' Hk'.
      assert (ssrnat.leq (S k') (find (fun b => b == true) l)). rewrite -?(rwP ssrnat.leP). lia.
      have Hbf := before_find _ H0.
      apply Hbf; auto. }
    destruct (IHl (i' - 1)).
    simpl in Hi1. rewrite Hi2 in Hi1. rewrite H. simpl in Hi1. lia.
    rewrite Hi2. now cbn. rewrite Hi2. simpl.
    rewrite Hi2 in Hi3. simpl in Hi3. rewrite Nat.sub_0_r. assumption. assumption.
    assert (size l - (i' - 1) = S (size l) - i'). lia. simpl in H2.
    rewrite H2 in H1.
    exists x. assumption. }
  assert (forall l,
             (Zbits.powerserie (Int64.convert_from_bits_to_Z_one_bits l) < two_p (S (size l)))%Z).
  induction l.
  cbn. unfold two_power_pos. cbn. lia.
  destruct a. rewrite two_p_equiv.
  replace (S (size (true :: l))) with (size l + 2).
  simpl. rewrite two_p_equiv in IHl. rewrite two_p_equiv. replace  (S (size l)) with (size l + 1) in IHl.
  replace (2^ ((size l) + 1)%nat)%Z with (2^(Z.of_nat (size l) + 1))%Z in IHl.
  replace (2^ ((size l) + 2)%nat)%Z with (2^(Z.of_nat (size l) + 2))%Z.
  assert (2 ^ (size l) +  2 ^ (Z.of_nat (size l) + 1) < 2^ (Z.of_nat (size l) + 2))%Z. {

    replace (2^ (Z.of_nat (size l)) + 2^(Z.of_nat (size l) + 1))%Z with (2^(size l) * 3)%Z.
    replace (2^(Z.of_nat (size l) + 2))%Z with (2^(size l) * 4)%Z.

    apply Zmult_lt_compat_l. lia. lia. replace 4%Z with (2 * 2)%Z by lia.
    replace (2 * 2)%Z with (2^2)%Z by lia. rewrite Z.pow_add_r. reflexivity. lia. lia.
    replace 3%Z with (1 + 2)%Z.

    rewrite Z.mul_add_distr_l.
    replace (2 ^ (size l) * 2)%Z with (2^(size l + 1))%Z. rewrite Z.mul_1_r. reflexivity.
    rewrite Z.pow_add_r. lia. lia. lia. lia. }
  lia. lia. lia. lia. simpl. lia.
  replace (S (size (false  :: l))) with (size l + 2).
  replace (Z.of_nat (size l + 2))%Z with ((Z.of_nat (size l) + 2))%Z.
  rewrite two_p_equiv.
  simpl. rewrite two_p_equiv in IHl. replace (2^ (S (size l))%nat)%Z with (2^(Z.of_nat (size l) + 1))%Z in IHl.
  assert (2^ (Z.of_nat (size l) + 1) < 2^ (Z.of_nat (size l)  + 2))%Z.
  replace (2^ (Z.of_nat (size l) + 1))%Z with (2^(Z.of_nat (size l)) * 2)%Z.
  replace (2^ (Z.of_nat (size l) + 2))%Z with (2^(Z.of_nat (size l)) * 4)%Z.
  apply Zmult_lt_compat_l. lia. lia. replace 4%Z with (2 * 2)%Z by lia.
  replace (2 * 2)%Z with (2^2)%Z by lia. rewrite Z.pow_add_r. reflexivity. lia. lia.
  rewrite Z.pow_add_r. lia. lia. lia. lia. lia. lia. cbn. lia.


  assert (forall xs x,
             (Zbits.powerserie (Int64.convert_from_bits_to_Z_one_bits (x :: xs)) < two_p (size (x :: xs)))%Z). {
    induction xs. intros.
    cbn.
    destruct x. cbn. unfold two_power_pos. cbn. lia. cbn. unfold two_power_pos. lia.
    intros.
    specialize (IHxs a).
    destruct x.
    assert (Z.of_nat (size (true :: a :: xs)) = Z.of_nat (size (a :: xs)) + 1)%Z. unfold size. fold (size xs). rewrite <-Nat.add_1_l. rewrite Nat2Z.inj_add. rewrite Z.add_comm. reflexivity.
    rewrite H0.
    unfold Int64.convert_from_bits_to_Z_one_bits. fold (Int64.convert_from_bits_to_Z_one_bits (a :: xs)).
    unfold Zbits.powerserie. fold (Zbits.powerserie (Int64.convert_from_bits_to_Z_one_bits (a :: xs))).
    assert (two_p (Z.of_nat (size (a :: xs))) < two_p (Z.of_nat (size (a :: xs)) + 1))%Z.
    rewrite two_p_equiv.
    rewrite two_p_equiv.
    rewrite Z.pow_add_r.
    lia.
    lia. lia.
    assert (forall x y y' z, y < y' -> x + y' < z -> x + y < z)%Z. intros. lia.
    assert (forall x y z, x < y -> z = 2 * y -> x + y  < z)%Z. intros. lia.
    assert (two_p (Z.of_nat (size (a :: xs)) + 1) = 2 * two_p (Z.of_nat (size (a :: xs))))%Z.
    rewrite two_p_equiv.
    rewrite two_p_equiv.
    rewrite Z.pow_add_r.
    lia.
    lia. lia.
    rewrite Z.add_comm.
    apply H3.
    assumption.
    assumption.
    assert (Z.of_nat (size (false :: a :: xs)) = Z.of_nat (size (a :: xs)) + 1)%Z. unfold size. fold (size xs). rewrite <-Nat.add_1_l. rewrite Nat2Z.inj_add. rewrite Z.add_comm. reflexivity. rewrite H0.

    assert (two_p (Z.of_nat (size (a :: xs))) < two_p (Z.of_nat (size (a :: xs)) + 1))%Z.
    rewrite two_p_equiv.
    rewrite two_p_equiv.
    rewrite Z.pow_add_r.
    lia.
    lia. lia.
    unfold Int64.convert_from_bits_to_Z_one_bits. fold (Int64.convert_from_bits_to_Z_one_bits (a :: xs)). lia. }
  induction l. now intros.
  intros i Hi1 Hi2 Hi3 Hk.
  have Hds := H0 l a.
  simpl in Hi1.
  simpl in Hi2.
  simpl in Hi3.
  remember (a :: l) as xs.
  destruct a.
  simpl in *. rewrite Hi2.
  simpl.
  rewrite Nat.sub_0_r.
  assert (two_p (Z.of_nat (size xs)) = two_power_pos (Pos.of_succ_nat (size l))). subst xs. cbn. reflexivity.
  rewrite <-H1 in Hds.
  assert (size xs - 1 = size l). subst xs. cbn. lia.
  rewrite H2. rewrite Heqxs. simpl. assert (Z.of_nat (size l) + 1 = Z.of_nat (size xs))%Z. subst xs. simpl. lia. rewrite H3. assumption.
  simpl in Hds.
  assert (two_p (Z.of_nat (size xs)) = two_power_pos (Pos.of_succ_nat (size l))). subst xs. cbn. reflexivity.
  simpl in H1.
  rewrite <-H1 in Hds.
  simpl.
  assert (Zbits.powerserie (Int64.convert_from_bits_to_Z_one_bits xs) = Zbits.powerserie (Int64.convert_from_bits_to_Z_one_bits l)). {
    subst xs. cbn. reflexivity. }
  rewrite H2.
  simpl in Hi2.
  assert (i - 1 < size l). rewrite Hi2. simpl. rewrite Nat.sub_0_r. lia.
  assert (i - 1 = find (fun b => b == true) l). subst i. cbn. lia.
  assert ((nth false l (i - 1) == true) = true).
  rewrite Hi2. simpl. rewrite Nat.sub_0_r.
  rewrite Hi2 in Hi3. simpl in Hi3. assumption.
  assert (forall k, k < (i - 1) -> (nth false l k == true) = false).
  intros k Hk'.
  assert (ssrnat.leq (S k) (find (fun b => b == true) l)). rewrite -?(rwP ssrnat.leP). lia.      have Hbf := before_find _ H6.
  simpl in Hbf. apply Hbf.
  have IH := IHl (i - 1) H3 H4 H5 H6.
  simpl in IH.
  assert (size l - (i - 1) = size l + 1 - i). lia. rewrite H7 in IH.
  assert (size xs = size l + 1). subst xs. cbn. lia. rewrite H8.
  assumption.
Qed.

Lemma clz_last : forall x i,
    i < Int64.wordsize ->
    i = Z.to_nat (Int64.intval (Int64.clz x)) ->
    (Int64.intval x < two_p (Z.of_nat (Int64.wordsize - i)))%Z.
Proof.
  intros x i Hi Hclz.
  unfold Int64.clz in Hclz.
  remember (Z.of_nat (Int64.wordsize - i - 1)) as j eqn:Hj.
  remember (Z.of_nat (ssrnat.subn (ssrnat.subn Int64.wordsize i) 1)) as j' eqn:Hj'.
  assert (j = j') by now rewrite <- ssrnat.minusE in Hj'.
  remember (fun b : bool_eqType => b == true) as a eqn:Ha.
  remember (Int64.intval x) as x' eqn:Hx'.
  remember (Int64.wordsize) as n eqn:Hn.
  remember (j' \in Zbits.Z_one_bits n x' 0) as inbits eqn:Hinbits.
  assert (nth false (Int64.convert_to_bits x) i = inbits). {
    rewrite Hinbits. rewrite  Hj'. rewrite Hn. rewrite  Hx'.
    apply Int64.convert_to_bits_nth. rewrite Hn in Hi.
    rewrite -?(rwP ssrnat.leP). lia.  }
  remember (Int64.convert_to_bits x) as s eqn:Hs.
  have Hsize := Int64.convert_to_bits_size x. rewrite <-Hs in Hsize.
  have : Int64.wordsize = 64. by unfold Int64.wordsize, Integers.Wordsize_64.wordsize.
  intro Hws.
  have : find a s <= 64.
  have Hsize' := find_size a s. rewrite <-Hws.
  rewrite -?(rwP ssrnat.leP) in Hsize'. simpl in Hsize'. rewrite Hsize in  Hsize'. auto.
  intro Hfindleq. simpl in Hfindleq.
  have : (Int64.intval (Z_to_i64 (find a s)) = Z.of_nat (find a s)).
  unfold Z_to_i64. simpl.
  rewrite Int64.Z_mod_modulus_id. reflexivity.
  rewrite int64_modulus_eq_pow64. cbn. lia.
  intro Hint.
  have : (i = find a s).
  rewrite Hint in Hclz. by rewrite Nat2Z.id in Hclz.
  intro Hieq. simpl in Hieq.
  have : has a s. rewrite has_find. rewrite -?(rwP ssrnat.leP). simpl. rewrite <-Hieq. rewrite ->Hsize, ->Hws. lia.
  intro Hhas.
  have :  a inbits.
  rewrite Hj' in Hinbits. rewrite Hn in Hinbits. rewrite Hx' in Hinbits.
  rewrite <-Int64.convert_to_bits_nth in Hinbits. rewrite Hieq in Hinbits. rewrite  Hs in Hinbits.
  rewrite Hinbits.
  apply nth_find. by subst s.
  rewrite -?(rwP ssrnat.leP). rewrite Hws. lia.
  intro Hinbits'.
  rewrite Ha in Hinbits'. rewrite eqb_id in Hinbits'.
  have Hsize' := find_size a s. rewrite (rwP ssrnat.leP) in Hfindleq.
  have : forall k, k < i -> a (nth false s k) = false. intros k Hk.
  have : (ssrnat.leq (S k) (find a s)). rewrite -?(rwP ssrnat.leP). simpl. rewrite <- Hieq. lia.
  intro.
  now apply before_find.
  intro Hbefore.
  assert (a (nth false s i) = true).
  rewrite Hieq.
  apply nth_find.
  assumption.
  have Hkl := convert_from_bits_head s i.
  assert (i < size s).
  rewrite has_find in Hhas. rewrite -?(rwP ssrnat.leP) in Hhas. lia.
  simpl in Hkl.
  rewrite Ha in Hieq. rewrite Ha in H1. rewrite Ha in Hbefore.
  specialize (Hkl H2 Hieq H1 Hbefore).
  rewrite Hsize in Hkl. rewrite Hws in Hkl.
  rewrite Hsize in H2.
  rewrite Hws in H2.
  rewrite Hn.
  rewrite Hws.
  assert (Z.of_nat (64 - i - 1) = Z.of_nat (63 - i))%Z. lia. rewrite H3 in Hkl.
  assert (Z.of_nat (63 - i) + 1 = Z.of_nat (64 - i))%Z. lia. rewrite H4 in Hkl.
  assert (two_p (Z.of_nat (64 - i)) <= Int64.modulus)%Z.
  rewrite two_p_equiv in Hkl.
  rewrite int64_modulus_eq_pow64. rewrite Nat2Z.inj_sub in Hkl. replace (Z.of_nat 64) with 64%Z in Hkl by lia.
  rewrite two_p_equiv.

  replace (Z.of_nat (64 - i))%Z with (64 - Z.of_nat i)%Z by lia.
  apply Z.pow_le_mono_r. lia. lia. lia.
  assert (forall l,
             0 <= Zbits.powerserie (Int64.convert_from_bits_to_Z_one_bits l))%Z. {
    induction l.
    cbn. lia.
    cbn.
    destruct a0.
    cbn.
    assert (two_p (Z.of_nat (size l)) > 0)%Z. apply two_p_gt_ZERO. lia. lia. lia. }

  assert (Zbits.powerserie (Int64.convert_from_bits_to_Z_one_bits s) < Int64.modulus)%Z by lia.
  have Hlow := H6 s.
  assert (Int64.intval (Int64.repr (Zbits.powerserie (Int64.convert_from_bits_to_Z_one_bits s))) = (Zbits.powerserie (Int64.convert_from_bits_to_Z_one_bits s))). {
    simpl. rewrite Int64.Z_mod_modulus_id. reflexivity. lia. }
  assert (x' = Zbits.powerserie (Int64.convert_from_bits_to_Z_one_bits s)).
    have : x = Int64.convert_from_bits (Int64.convert_to_bits x).
    apply Int64.convert_to_from_bits.
    intro Htofrom.
    unfold Int64.convert_from_bits in Htofrom.
    rewrite Hx'. rewrite Htofrom.
    rewrite Hs. rewrite Hs in H8.
    rewrite H8. reflexivity.
    rewrite H9. assumption.
Qed.

Lemma clz_lowerbound : forall x i,
    (-1 < Int64.intval x < Int64.modulus)%Z ->
    i < Int64.wordsize ->
    i = Z.to_nat (Int64.intval (Int64.clz x)) ->
    (two_power_nat (Int64.wordsize - i - 1) <= Int64.intval x)%Z.
Proof.
  intros x i Hrange Hi Hclz.
  unfold Int64.clz in Hclz.
  remember (Z.of_nat (Int64.wordsize - i - 1)) as j eqn:Hj.
  remember (Z.of_nat (ssrnat.subn (ssrnat.subn Int64.wordsize i) 1)) as j' eqn:Hj'.
  assert (j = j') by now rewrite <- ssrnat.minusE in Hj'.
  remember (fun b : bool_eqType => b == true) as a eqn:Ha.
  remember (Int64.intval x) as x' eqn:Hx'.
  remember (Int64.wordsize) as n eqn:Hn.
  remember (j' \in Zbits.Z_one_bits n x' 0) as inbits eqn:Hinbits.
  assert (nth false (Int64.convert_to_bits x) i = inbits). {
    rewrite Hinbits. rewrite  Hj'. rewrite Hn. rewrite  Hx'.
    apply Int64.convert_to_bits_nth. rewrite Hn in Hi.
    rewrite -?(rwP ssrnat.leP). lia.  }
  remember (Int64.convert_to_bits x) as s eqn:Hs.
  have Hsize := Int64.convert_to_bits_size x. rewrite <-Hs in Hsize.
  have : Int64.wordsize = 64. by unfold Int64.wordsize, Integers.Wordsize_64.wordsize.
  intro Hws.
  have : find a s <= 64.
  have Hsize' := find_size a s. rewrite <-Hws.
  rewrite -?(rwP ssrnat.leP) in Hsize'. simpl in Hsize'. rewrite Hsize in  Hsize'. auto.
  intro Hfindleq. simpl in Hfindleq.
  have : (Int64.intval (Z_to_i64 (find a s)) = Z.of_nat (find a s)).
  unfold Z_to_i64. simpl.
  rewrite Int64.Z_mod_modulus_id. reflexivity.
  rewrite int64_modulus_eq_pow64. cbn. lia.
  intro Hint.
  have : (i = find a s).
  rewrite Hint in Hclz. by rewrite Nat2Z.id in Hclz.
  intro Hieq. simpl in Hieq.
  have : has a s. rewrite has_find. rewrite -?(rwP ssrnat.leP). simpl. rewrite <-Hieq. rewrite ->Hsize, ->Hws. lia.
  intro Hhas.
  have :  a inbits.
  rewrite Hj' in Hinbits. rewrite Hn in Hinbits. rewrite Hx' in Hinbits.
  rewrite <-Int64.convert_to_bits_nth in Hinbits. rewrite Hieq in Hinbits. rewrite  Hs in Hinbits.
  rewrite Hinbits.
  apply nth_find. by subst s.
  rewrite -?(rwP ssrnat.leP). rewrite Hws. lia.
  intro Hinbits'.
  rewrite Ha in Hinbits'. rewrite eqb_id in Hinbits'.
  have Hsize' := find_size a s. rewrite (rwP ssrnat.leP) in Hfindleq.
  assert (forall k, In k (Zbits.Z_one_bits Int64.wordsize (Int64.intval x) 0) -> 0 <= k)%Z. {
    intros k Hk.
    have Hk' := Zbits.Z_one_bits_range _ _ _ Hk; lia. }
  assert (Hx'': (0 <= (Int64.intval x) < two_power_nat Int64.wordsize)%Z).
  rewrite two_power_nat_equiv. unfold Int64.wordsize, Integers.Wordsize_64.wordsize. rewrite int64_modulus_eq_pow64 in Hrange. lia.
  have Hpow := Zbits.Z_one_bits_powerserie 64 (Int64.intval x) Hx''.
  rewrite two_power_nat_equiv.
  rewrite Hx'. rewrite Hpow.
  have Hpow' := in_Z_one_bits_pow.
  specialize (Hpow' (Zbits.Z_one_bits 64 (Int64.intval x) 0)).
  specialize (Hpow' j).
  rewrite <-H in Hinbits. rewrite Hinbits in Hinbits'.
  rewrite Hn in Hinbits'. rewrite Hws in Hinbits'. rewrite Hx' in Hinbits'.
  specialize (Hpow' Hinbits').
  rewrite Hws in H1.
  specialize (Hpow' H1).
  rewrite <-Hj . assumption.
Qed.

Lemma clz_spec : forall x,
    (0 < x < Int64.modulus)%Z ->
    (2^63 <= 2^(Int64.intval (Int64.clz (Int64.repr x))) * x < 2^64)%Z.
Proof.
intros x Hx.
have Hclz_last := clz_last.
assert (Hsize : size (Int64.convert_to_bits (Z_to_i64 x)) = Int64.wordsize).
apply Int64.convert_to_bits_size.
remember (Int64.intval (Int64.clz (Z_to_i64 x))) as i eqn:Hi.
assert (0 <= Int64.intval (Int64.clz (Z_to_i64 x)) < Int64.wordsize)%Z.
have Hi' := Hi.
unfold Int64.clz in Hi.
remember (Int64.convert_to_bits (Z_to_i64 x)) as bits eqn:Hc2b.
remember (fun b => b == true) as a eqn:Ha.
assert (0 <= Z.of_nat (find a bits))%Z. lia.
assert (ssrnat.leq (find a bits) Int64.wordsize)%Z.
rewrite <-Hsize. apply find_size.
rewrite -?(rwP ssrnat.leP) in H0.
unfold Int64.clz.
rewrite <- Hc2b. rewrite <-Ha.
destruct (le_lt_eq_dec (find a bits) Int64.wordsize) as [Hlt|Heq]. assumption.
simpl.
rewrite Int64.Z_mod_modulus_id. unfold Int64.wordsize, Integers.Wordsize_64.wordsize in Hlt. simpl in Hlt. lia.
unfold Int64.wordsize, Integers.Wordsize_64.wordsize in Hlt. simpl in Hlt.
rewrite int64_modulus_eq_pow64. lia.
rewrite Heq in Hi.
simpl in Hi.
assert (Int64.repr x = Int64.repr 0).
apply Int64.clz_wordsize.
remember (Int64.clz (Z_to_i64 x)) as clz eqn:Hclz.
assert (Int64.intval (Z_to_i64 i) = (Int64.intval clz)).
rewrite Hi'. simpl.
rewrite Int64.Z_mod_modulus_id. reflexivity. rewrite <-Hi'. rewrite Hi. rewrite int64_modulus_eq_pow64. lia.

apply Int64.eq_T_intval in H1.
rewrite <-H1. simpl. now rewrite Hi.
apply Int64.repr_inv in H1. lia. lia. lia.
assert (Z.to_nat i < Int64.wordsize). lia.
specialize (Hclz_last (Int64.repr x) (Z.to_nat i) H0).
rewrite <-Hi in Hclz_last. specialize (Hclz_last Logic.eq_refl).
replace (Int64.intval (Z_to_i64 x)) with x in Hclz_last. 2: simpl; rewrite Int64.Z_mod_modulus_id; lia.
rewrite Nat2Z.inj_sub in Hclz_last. 2: lia.

rewrite Z2Nat.id in Hclz_last.
replace (Z.of_nat Int64.wordsize) with 64%Z in Hclz_last by now cbn.
rewrite two_p_equiv in Hclz_last.
assert (2^i * x < 2^64)%Z.
replace (2^64)%Z with (2^i * 2^(64 - i))%Z.
apply Zmult_lt_compat_l. lia. lia.
rewrite <-Z.pow_add_r. replace (i + (64 - i))%Z with 64%Z by lia. reflexivity. lia.
unfold Int64.wordsize, Integers.Wordsize_64.wordsize in H0. lia.
assert (2^63 <= 2^i * x)%Z.
have Hlower := clz_lowerbound.
assert (-1 < Int64.intval x < Int64.modulus)%Z. simpl. rewrite Int64.Z_mod_modulus_id; lia.
specialize (Hlower (Int64.repr x) (Z.to_nat i) H2 H0).
rewrite <-Hi in Hlower.
specialize (Hlower Logic.eq_refl).
rewrite two_power_nat_equiv in Hlower.
replace (Int64.intval (Int64.repr x)) with x in Hlower.
unfold Int64.wordsize, Integers.Wordsize_64.wordsize in Hlower.
assert (Z.of_nat (64 - Z.to_nat i - 1) = 63 - i)%Z. rewrite Nat2Z.inj_sub. rewrite Nat2Z.inj_sub. lia. unfold Int64.wordsize, Integers.Wordsize_64.wordsize in H0. lia. unfold Int64.wordsize, Integers.Wordsize_64.wordsize in H0. lia.
rewrite H3 in Hlower.
assert (2^(63 - i) = 2^63/2^i)%Z.
rewrite Z.pow_sub_r; lia.
assert ((2^i * x) / 2^i = x)%Z.
rewrite Z.mul_comm. rewrite Z_div_mult. reflexivity.
lia.
assert (63 = (63 - i) + i)%Z. lia.
rewrite H6.
rewrite Z.pow_add_r.
rewrite Z.mul_comm.
apply Zmult_le_compat. lia.  assumption.  lia.  lia. lia.
lia.
simpl. rewrite Int64.Z_mod_modulus_id; lia.
lia. lia.
Qed.

Lemma clz_spec_alt : forall x,
    (0 < x < Int64.modulus)%Z ->
    Int64.intval (Int64.clz (Int64.repr x)) = (63 - Z.log2 (Int64.intval (Int64.repr x)))%Z.
Proof.
  intros.
  have H' := clz_spec _ H.
  destruct H' as [Hle1 Hle2].
  assert (Hlog1: (Z.log2 (2^63) <= Z.log2 (2 ^ (Int64.intval (Int64.clz (Int64.repr x))) * x))%Z) by (apply Z.log2_le_mono; assumption).
  assert (Hlog2: (Z.log2 (2 ^ (Int64.intval (Int64.clz (Int64.repr x))) * x) < 64)%Z) by (apply Z.log2_lt_pow2; lia).
  replace (2 ^ (Int64.intval (Int64.clz (Int64.repr x))) * x)%Z with (x * 2 ^ (Int64.intval (Int64.clz (Int64.repr x))))%Z in Hlog1, Hlog2 by lia.
  rewrite Z.log2_mul_pow2 in Hlog1, Hlog2.
  replace (Z.log2 (2 ^ 63)) with 63%Z in Hlog1 by (rewrite Z.log2_pow2; lia).
  replace (Int64.intval (Z_to_i64 x)) with x.
  lia.
  simpl. rewrite Int64.Z_mod_modulus_id; lia. lia.
  unfold Int64.clz.
  assert (forall n, 0 <= Int64.intval (Z_to_i64 (Z.of_nat n)))%Z. intro. simpl.
  rewrite Int64.Z_mod_modulus_eq. lia.
  apply H0.
Qed.

Lemma head0_int64_clz : forall x,
    (0 < to_Z x)%Z ->
    to_Z (head0 x) = (Int64.unsigned (Int64.clz (Int64.repr (to_Z x))) - 1)%Z.
Proof.
  intros.
  unfold Int64.unsigned.
  rewrite clz_spec_alt.
  replace (63 - Z.log2 (Int64.intval (Z_to_i64 φ (x)%uint63)) - 1)%Z with (62 - Z.log2 (Int64.intval (Z_to_i64 φ (x)%uint63)))%Z by lia.
  replace (Int64.intval (Z_to_i64 (to_Z x))) with (to_Z  x). rewrite head0_spec_alt; auto.
  simpl. rewrite uint63_mod_modulus_id.
  reflexivity. auto.
  rewrite int64_modulus_eq_pow64. split; auto. apply uint63_lt_pow64.
Qed.

Lemma powerserie_convert_from_bits_rev : forall l i,
    i < size l ->
    i = find (fun b => b == true)  (rev l) ->
    (fun b => b == true) (nth false (rev l) i) = true ->
    (forall k, k < i -> (fun b => b == true) (nth false (rev l) k) = false) ->
    exists y,
      Zbits.powerserie (Int64.convert_from_bits_to_Z_one_bits l) = ((y * 2 + 1) * 2^i)%Z.
Proof.
  induction l.
  now intros.
  intros i Hsize Hfind Hnth Hbefore.
  assert (ssrnat.leq (S i) (size (a :: l))).
  simpl. simpl in Hsize.
  rewrite -?(rwP ssrnat.leP). lia.
  destruct (size l - i) eqn:Hdiff.
  { (* Special case? is is the index of the _last_ 1 bit in (a :: l), i.e. i = size l *)
    have Hnth' := Hnth.
    rewrite nth_rev in Hnth'.
    assert (Hsize' : i = size l). simpl in Hsize, Hdiff |-*. lia.
    unfold ssrnat.subn, ssrnat.subn_rec in Hnth'; simpl in Hnth'.
    rewrite Hdiff in Hnth'.
    simpl in Hnth'.
    rewrite eqb_id in Hnth'. rewrite Hnth'.
    simpl. rewrite two_p_equiv. rewrite Hsize'.
    remember (Zbits.powerserie (Int64.convert_from_bits_to_Z_one_bits l)) as ps eqn:Hps.
    have Hbefore' := Hbefore.
    assert (Hps0 : forall l' i',
               i' = size l' ->
               (forall k : nat, k < i' -> (nth false (rev l') k == true) = false) ->
               Zbits.powerserie (Int64.convert_from_bits_to_Z_one_bits l') = 0). {
      induction l'. now intros.
      intros.
      have : (nth false (a0 :: l') 0 == true) = false.
      assert ((i' - 1) < i'). simpl in H0. simpl. lia.
      apply H1 in H2.
      rewrite nth_rev in H2. rewrite <-H0 in H2.
      unfold ssrnat.subn, ssrnat.subn_rec in H2. simpl in H2.
      assert (i' - S (i' - 1) = 0). lia. rewrite H3 in H2. assumption.
      rewrite -(rwP ssrnat.leP). simpl in H0 |- *. lia.
      intro Ha0.
      rewrite eqb_id in Ha0. simpl in Ha0.
      rewrite Ha0. simpl.
      apply IHl' with (i' - 1). simpl in H0 |- *. lia.
      intros k Hk.
      have Hrcons := rev_cons a0 l'.
      have Hnc := nth_rcons false (rev l') a0 k.
      assert (Hk' : k < i'). lia.
      have Hbf' := H1 k Hk'.
      rewrite Hrcons in Hbf'.
      assert (ssrnat.leq (S k) (size (rev l'))).
      rewrite -(rwP ssrnat.leP). simpl. rewrite size_rev. simpl in H0. lia.
      rewrite H2 in Hnc. rewrite <- Hnc. assumption.  }

    have : ps = 0%Z.
    rewrite Hps. apply Hps0 with (i':=i); auto.
    intros k Hk.
    have Hrcons := rev_cons a l.
    have Hnc := nth_rcons false (rev l) a k.
    assert (Hk' : k < i). lia.
    have Hbf' := Hbefore k Hk'.
    rewrite Hrcons in Hbf'.
    assert (ssrnat.leq (S k) (size (rev l))).
    rewrite -(rwP ssrnat.leP). simpl. rewrite size_rev. simpl. simpl in Hsize'. rewrite <-Hsize'. lia.
    rewrite H0 in Hnc.
    simpl. simpl in Hnc.
    rewrite <- Hnc. assumption.
    intro Hps0'. exists 0%Z.
    rewrite Z.mul_0_l.
    rewrite Z.add_0_l.
    rewrite Hps0'. rewrite Z.add_0_r.
    rewrite Z.mul_1_l. reflexivity.
    rewrite -(rwP ssrnat.leP). simpl. simpl in Hsize. lia. }
  { (* inductive case: i < size l *)
  assert (Hsize' : i = size l - S n). lia. assert (Hn : n < size l). lia.
  assert (Hnth' : (nth false (rev l) i) == true).
  assert (Hsize'' : (size l) - (S n) = i). by rewrite Hsize'.
  assert (Hsize''' :n = (size l) - (S i)). lia.
  rewrite nth_rev in Hnth; auto.
  rewrite nth_rev.
  rewrite ssrnat.subnE in Hnth |- *. simpl in Hnth |- *.
  unfold ssrnat.subn_rec in Hnth |- *.
  rewrite eqb_id in Hnth.
  simpl in Hnth.
  rewrite Hdiff in Hnth. simpl in Hnth. simpl in Hsize'''. rewrite <-Hsize'''. rewrite eqb_id. assumption.
  rewrite -(rwP ssrnat.leP). simpl in Hsize', Hsize''. simpl in Hsize', Hdiff. lia.
  assert (Hfind' : i = find (fun b => b == true) (rev l)).
  rewrite <-cat1s in Hfind.
  rewrite rev_cat in Hfind. rewrite find_cat in Hfind.
  unfold ssrnat.addn, ssrnat.addn_rec in Hfind.
  destruct (has (fun b => b == true) (rev l)). assumption.
  simpl in Hfind. destruct a; simpl in Hfind. rewrite size_rev in Hfind. simpl in Hdiff, Hsize'. lia. rewrite size_rev in Hfind. simpl in Hdiff, Hsize'. lia.
  assert (Hbefore' : forall k, k < i -> (nth false (rev l) k == true) = false).
  intros k Hk.
  have Hbf := before_find.
  assert (ssrnat.leq (S k) i). rewrite -(rwP ssrnat.leP). lia. rewrite Hfind' in H0. apply Hbf with (x0:=false) in H0. assumption.
  assert (Hsizei : i < (size l)). lia.
  have IH := IHl i Hsizei Hfind' Hnth' Hbefore'.
  destruct IH as [y Hy].
  simpl. destruct a.
  exists (2^(size l - i - 1) + y)%Z.
  rewrite [((2 ^ (size l - i - 1) + y) * 2)%Z] Z.mul_add_distr_r.
  replace 2%Z with (2^1)%Z at 2. rewrite <- Z.pow_add_r. rewrite Z.sub_add.
  rewrite Z.mul_add_distr_r.
  rewrite Z.mul_add_distr_r. rewrite <- Z.pow_add_r. rewrite Z.sub_add.
  rewrite <-Z.add_assoc. rewrite <-Z.mul_add_distr_r.
  simpl. rewrite two_p_equiv.
  rewrite Hy. reflexivity. simpl in Hsize'.  lia. lia. lia. lia. lia.
  exists y. assumption. }
Qed.

Lemma to_from_bits_modulus : forall x,
    (-1 < x < Int64.modulus)%Z ->
    x = Zbits.powerserie (Int64.convert_from_bits_to_Z_one_bits (Int64.convert_to_bits (Int64.repr x))).
Proof.
  intros x Hx.
  rewrite Int64.convert_from_bits_to_Z_one_bits_power_index_to_bits.
  have E: filter (fun x => Coqlib.zlt x Int64.wordsize) (Zbits.Z_one_bits Int64.wordsize (Int64.intval x) 0) = Zbits.Z_one_bits Int64.wordsize (Int64.intval x) 0.
  rewrite filter_for_all => //.
  rewrite list_all_forall => e. rewrite -List_In_in_mem => I.
  apply Int64.Zbits_Z_one_bits_range in I. destruct Coqlib.zlt => //. lia.
  rewrite E.
  replace (Int64.intval (Z_to_i64_co x)) with x.
  apply Zbits.Z_one_bits_powerserie.
  rewrite int64_modulus_eq_pow64 in Hx. unfold Int64.wordsize, Integers.Wordsize_64.wordsize.
  unfold two_power_nat. simpl. lia.
  simpl. rewrite Int64.Z_mod_modulus_id; lia.
  by apply Int64.Zbits_Z_one_bits_uniq.
Qed.

Lemma ctz_non_zero : forall x i,
    (0 < x < Int64.modulus)%Z ->
    i < Int64.wordsize ->
    i = Z.to_nat (Int64.intval (Int64.ctz (Int64.repr x))) ->
    exists y,
      (x = (y * 2 + 1) * 2^i)%Z.
Proof.
  intros x i Hx Hi Hctz.
  unfold Int64.ctz in Hctz.
  remember (Int64.convert_to_bits (Int64.repr x)) as s eqn:Hs.
  have Hsize := Int64.convert_to_bits_size (Int64.repr x). rewrite <-Hs in Hsize.
  have : Int64.wordsize = 64. by unfold Int64.wordsize, Integers.Wordsize_64.wordsize.
  intro Hws.
  have : i = find (fun b => b == true) (rev s).
  rewrite Hctz. cbn. rewrite Int64.Z_mod_modulus_id.
  rewrite Nat2Z.id. reflexivity.
  have : find (fun b => b == true) (rev s) <= size (rev s).
  rewrite (rwP ssrnat.leP).
  apply find_size.
  rewrite size_rev.
  cbn.
  intro Hfindsize.
  rewrite int64_modulus_eq_pow64.
  lia.
  have Hex := powerserie_convert_from_bits_rev.
  assert (Hleq : ssrnat.leq (S i) (size (rev s))).
  rewrite -(rwP ssrnat.leP).
  rewrite size_rev. rewrite Hsize.  rewrite Hws in Hi. lia.
  intro Hifind.
  have Hnth := Hleq.
  rewrite Hifind in Hnth.
  rewrite <-has_find in Hnth.
  apply nth_find with (x0:=false) in Hnth.
  assert ((nth false (rev s) i == true) = true).
  rewrite Hifind. auto.
  have Hbefore := before_find.
  assert (Hbf: forall k, k < i -> (nth false (rev s) k == true) = false). {
    intros k Hk.
    specialize (Hbefore (Equality.sort bool_eqType) false (fun b => b == true) (rev s) k).
    rewrite <-Hifind in Hbefore.
    apply Hbefore.
    rewrite -(rwP ssrnat.leP). lia. }
  assert (Hisize : i < size s). rewrite Hws in Hi. lia.
  assert (Hinth : (nth false (rev s) i == true) = true). rewrite Hifind; auto.
  specialize (Hex s i Hisize Hifind Hinth Hbf).
  destruct Hex as [c Hc].
  assert (x = Zbits.powerserie (Int64.convert_from_bits_to_Z_one_bits s)).
  rewrite Hs. apply to_from_bits_modulus. lia.
  exists c. now subst x.
Qed.

Lemma ctz_spec : forall x,
    (0 < x < Int64.modulus)%Z ->
    exists y,
      (x = (y * 2 + 1) * 2^(Int64.unsigned (Int64.ctz (Int64.repr x))))%Z.
Proof.
intros x Hx.
have Hctz := ctz_non_zero.
assert (Hsize : size (Int64.convert_to_bits (Z_to_i64 x)) = Int64.wordsize).
apply Int64.convert_to_bits_size.
remember (Int64.intval (Int64.ctz (Z_to_i64 x))) as i eqn:Hi.
assert (0 <= Int64.intval (Int64.ctz (Z_to_i64 x)) < Int64.wordsize)%Z.
have Hi' := Hi.
unfold Int64.ctz in Hi.
remember (Int64.convert_to_bits (Z_to_i64 x)) as bits eqn:Hc2b.
remember (fun b => b == true) as a eqn:Ha.
assert (0 <= Z.of_nat (find a (rev bits)))%Z. lia.
assert (ssrnat.leq (find a (rev bits)) Int64.wordsize)%Z.
rewrite <-Hsize. rewrite <-size_rev.  apply find_size.
rewrite -?(rwP ssrnat.leP) in H0.
unfold Int64.ctz.
rewrite <- Hc2b. rewrite <-Ha.
destruct (le_lt_eq_dec (find a (rev bits)) Int64.wordsize) as [Hlt|Heq]. assumption.
cbn.
rewrite Int64.Z_mod_modulus_id. unfold Int64.wordsize, Integers.Wordsize_64.wordsize in Hlt. cbn in Hlt. lia.
unfold Int64.wordsize, Integers.Wordsize_64.wordsize in Hlt. cbn in Hlt.
rewrite int64_modulus_eq_pow64. lia.
rewrite Heq in Hi.
cbn in Hi.
assert (Int64.repr x = Int64.repr 0).
apply Int64.ctz_wordsize.
remember (Int64.ctz (Z_to_i64 x)) as ctz eqn:Hctzv.
assert (Int64.intval (Z_to_i64 i) = (Int64.intval ctz)).
rewrite Hi'. cbn.
rewrite Int64.Z_mod_modulus_id. reflexivity. rewrite <-Hi'. rewrite Hi. rewrite int64_modulus_eq_pow64. lia.
apply Int64.eq_T_intval in H1.
rewrite <-H1. simpl. now rewrite Hi.
apply Int64.repr_inv in H1. lia. lia. lia.
assert (Z.to_nat i < Int64.wordsize). lia.
specialize (Hctz x (Z.to_nat i) Hx H0).
rewrite Hi in Hctz. specialize (Hctz Logic.eq_refl).
replace (Int64.intval (Z_to_i64 x)) with x in Hctz. 2: cbn; rewrite Int64.Z_mod_modulus_id; lia.
rewrite Z2Nat.id in Hctz.
destruct Hctz as [c Hc].
unfold Int64.unsigned.
exists c. exact Hc.
lia.
Qed.

Lemma unique_greatest_power_of_two_divisor : forall x n m,
    (0 < x)%Z ->
    (0 <= n)%Z ->
    (0 <= m)%Z ->
    (exists y, x = (2 * y + 1) * 2^n)%Z ->
    (exists y', x = (2 * y' + 1) * 2^m)%Z ->
    n = m.
Proof.
  assert (forall i, 0 < i -> Z.odd (2^i) = false)%Z as Hpow2odd. {
    intros i Hi.
    replace (2^i)%Z with (2^(i - 1) * (2 ^ 1))%Z. rewrite Z.odd_mul. simpl. lia.
    rewrite <-Z.pow_add_r. now rewrite Z.sub_add.
    lia. lia. }
  intros x n m Hxnz Hnge0 Hmge0 [y Hxn] [y' Hxm].
  remember (2 * y + 1)%Z as a eqn:Ha.
  remember (2 * y' + 1)%Z as b eqn:Hb.
  assert (a * 2^n = b * 2^m)%Z as Heq. rewrite <- Hxn, <- Hxm. reflexivity.
  destruct (Z_lt_dec n  m) as [Hlt | Hnlt]. {
    assert (a = b * 2^(m - n))%Z as Ha'. {
      rewrite Z.pow_sub_r; [|lia|lia].
      rewrite <-Znumtheory.Zdivide_Zdiv_eq_2. 2: lia.
      replace a with (a * 2^n / 2^n)%Z by nia.
      rewrite <-Hxn. rewrite <-Hxm. reflexivity.
      exists (2^(m - n))%Z. rewrite <-Z.pow_add_r.
      now rewrite Z.sub_add. lia. lia. }
    assert (Z.odd a = true) as Hodda. {
      subst a.
      rewrite Z.add_comm. rewrite Z.odd_add_mul_2.
      reflexivity. }
    assert (Z.odd a = false) as Hodda'. {
      rewrite Ha'. rewrite Z.mul_comm.
      rewrite Z.odd_mul. rewrite Hpow2odd. reflexivity. lia. }
    rewrite Hodda' in Hodda. discriminate. }
  destruct (Z_lt_dec m n) as [Hlt' | Hnlt']. {
    assert (b = a * 2^(n - m))%Z as Hb'. {
      rewrite Z.pow_sub_r; [|lia|lia].
      rewrite <-Znumtheory.Zdivide_Zdiv_eq_2. 2: lia.
      replace b with (b * 2^m / 2^m)%Z by nia.
      rewrite <-Hxn. rewrite <-Hxm. reflexivity.
      exists (2^(n - m))%Z. rewrite <-Z.pow_add_r.
      now rewrite Z.sub_add. lia. lia. }
    assert (Z.odd b = true) as Hoddb. {
      subst b.
      rewrite Z.add_comm. rewrite Z.odd_add_mul_2.
      reflexivity. }
    assert (Z.odd b = false) as Hoddb'. {
      rewrite Hb'. rewrite Z.mul_comm.
      rewrite Z.odd_mul. rewrite Hpow2odd. reflexivity. lia. }
    rewrite Hoddb' in Hoddb. discriminate. }
  lia.
Qed.

Lemma tail0_int64_ctz : forall x,
    (0 < to_Z x)%Z ->
    Int64.repr (to_Z (tail0 x)) = (Int64.ctz (Int64.repr (to_Z x))).
Proof.
  intros.
  have HxBounded := to_Z_bounded x.
  assert (0 < to_Z x < Int64.modulus)%Z as HxBounded'. rewrite int64_modulus_eq_pow64. cbn in HxBounded. lia.
  have Hctz := ctz_spec (to_Z x) HxBounded'.
  have Htail0 := tail0_spec x H.
  assert (to_Z (tail0 x) = Int64.unsigned (Int64.ctz (Int64.repr (to_Z x)))). {
    apply unique_greatest_power_of_two_divisor with (x:=to_Z x); auto.
    destruct (to_Z_bounded (tail0 x)). lia.
    destruct (Int64.unsigned_range (Int64.ctz (Z_to_i64 φ (x)%uint63))). lia.
    destruct Htail0 as [y [_ Hy]]. exists y. auto.
    destruct Hctz as [y Hy]. rewrite - [(y * 2)%Z] Z.mul_comm in Hy.
    exists y; auto. }
  rewrite H0.
  rewrite Int64.repr_unsigned.
  reflexivity.
Qed.

End CORRECTNESS.
