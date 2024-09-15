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

Variables global_mem_ptr glob_tmp1 glob_tmp2 glob_tmp3 glob_tmp4 loop_counter : globalidx.

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



(* the following is for in_Z_one_bits_last, there must be a better way :| *)
#[local] Fixpoint increasing (idx : nat) (len : nat) :=
  match len with
  | 0 => []
  | S len' => Z.of_nat idx :: increasing (S idx) len'
  end.

#[local] Lemma increasing_snoc : forall len idx,
  increasing idx len ++ [Z.of_nat (idx + len)] = increasing idx (S len).
Proof.
  induction len; intros.
  - now rewrite Nat.add_0_r.
  - replace  (idx + S len) with (S idx + len) by lia.
  cbn. now rewrite IHlen.
Qed.

#[local] Lemma increasing_ge_idx : forall len idx (y:Z),
  In y (increasing idx len) -> (y >= idx)%Z.
Proof.
  induction len; intros=>//.
  cbn in H. destruct H as [H|H].
  - lia.
  - apply IHlen in H. lia.
Qed.

#[local] Lemma increasing_concat : forall  len idx,
  increasing 0 idx ++ increasing idx len = increasing 0 (idx + len).
Proof.
  induction len; intros.
  - cbn. now rewrite cats0 Nat.add_0_r.
  - cbn. replace (idx + S len) with (S idx + len) by lia.
    rewrite -IHlen. cbn.
    replace (Z.of_nat idx :: increasing (S idx) len) with
            ([Z.of_nat idx] ++ increasing (S idx) len) by now cbn.
    rewrite catA. now rewrite increasing_snoc.
Qed.

#[local] Lemma increasing_in : forall len idx (y : Z),
  (Z.of_nat idx <= y < Z.of_nat idx + Z.of_nat len)%Z ->
  In y (increasing idx len).
Proof.
  induction len; intros; first lia.
  cbn.
  destruct (Z.eqb_spec idx y); first now left. right.
  apply IHlen. lia.
Qed.

#[local] Lemma powerserie_concat : forall l1 l2,
  Zbits.powerserie (l1 ++ l2) = (Zbits.powerserie l1 + Zbits.powerserie l2)%Z.
Proof.
  induction l1; intros=>//.
  cbn. rewrite IHl1. lia.
Qed.


#[local] Lemma powerserie_increasing : forall len,
  (Zbits.powerserie (increasing 0 len) = 2 ^ len - 1)%Z.
Proof.
  intros.
  induction len; intros=>//.
  rewrite -increasing_snoc.
  rewrite powerserie_concat. rewrite IHlen.
  remember (S len) as slen. cbn. rewrite two_p_equiv.
  enough (2 ^ len + 2 ^ len = 2 ^ slen)%Z by lia. subst.
  replace (S len) with (1 + len) by lia.
  enough (2 ^ len + 2 ^ len = 2 ^ (1 + len))%Z by lia.
  rewrite Zpower_exp; lia.
Qed.


#[local] Lemma powerserie_incl : forall l1 l2,
  (forall x, In x (l1 ++ l2) -> x >= 0)%Z ->
  NoDup l1 ->
  incl l1 l2 ->
  (Zbits.powerserie l1 <= Zbits.powerserie l2)%Z.
Proof.
  induction l1; intros. cbn.
  { induction l2=>//. cbn. cbn in IHl2.
    assert (a >= 0)%Z. apply H. now left. assert (0 <= a)%Z by lia. apply two_p_gt_ZERO in H3.
    enough (0 <= Zbits.powerserie l2)%Z by lia. apply IHl2=>//.
    intros. apply H. now right.
    }
  { cbn. assert (In a l2). { apply H1. now left. }
    apply in_split in H2. destruct H2 as [l3 [l4 Heq]].
    inv H0. rewrite powerserie_concat. cbn.
    enough (Zbits.powerserie l1 <= Zbits.powerserie l3 + Zbits.powerserie l4)%Z by lia.
    rewrite -powerserie_concat.
    apply IHl1; auto.
    - intros. apply H. right.
      apply in_app in H0. destruct H0 as [H0|H0]. now apply in_app.
      apply in_app in H0. destruct H0 as [H0|H0]. apply in_app. right. now apply in_app.
      apply in_app. right. apply in_app. right. now right.
    - intros ??.
      assert (In a0 (a :: l1)) by now right.
      have H' := H1 a0 H2.
      apply in_app in H'. destruct H'. apply in_app. now left.
      cbn in H3. destruct H3 as [-> |H3]=>//. apply in_app. now right. }
Qed.

(* from https://github.com/VeriNum/LAProof/blob/main/mathcomp_compat/CommonSSR.v#L417 *)
Lemma in_mem_In: forall {A: eqType} (l: list A) x,
  x \in l <-> In x l.
Proof.
  move => A l x. elim: l => [//| h t IH /=].
  rewrite in_cons -IH eq_sym. split => [/orP[/eqP Hx | Ht]| [Hx | Hlt]]. by left. by right.
  subst. by rewrite eq_refl. by rewrite Hlt orbT.
Qed.

Lemma uniq_NoDup: forall {A: eqType} (l: list A),
  uniq l <-> NoDup l.
Proof.
  move => A l. elim : l => [//=|h t IH].
  - split =>[H{H}|//]. by apply NoDup_nil.
  - rewrite /=. split => [/andP[Hnotin Hun]| ].
    constructor. rewrite -in_mem_In. move => Hin. by move : Hin Hnotin ->.
    by apply IH.
    move => Hnod. inversion Hnod as [|x l Hnotin Hnodup] ; subst.
    have->: h \notin t. case Hin: (h\in t). have: h\in t by []. by rewrite in_mem_In =>{} Hin.
    by []. by rewrite IH.
Qed.

Lemma Z_one_bits_lowerbound : forall n l x idx y,
  l = Zbits.Z_one_bits n x idx ->
  In y l ->
  (y >= idx)%Z.
Proof.
  induction n; intros.
  - cbn in H. subst l=>//.
  - cbn in H. destruct (Z.odd x).
    2:{ apply (IHn _ _ _ y) in H=>//. lia. }
    destruct l=>//. injection H as ->.
    destruct H0. lia.
    apply (IHn _ _ _ y) in H=>//. lia.
Qed.

Lemma Z_one_bits_monotone : forall n l x idx i j i' j' ,
  l = Zbits.Z_one_bits n x idx ->
  i > j ->
  nth_error l i = Some i' ->
  nth_error l j = Some j' ->
  (i' >= j')%Z.
Proof.
  induction n; intros.
  - cbn in H. subst l. now destruct i.
  - cbn in H. destruct (Z.odd x).
    + destruct l=>//. injection H as ->.
      have IH := IHn _ _ _ _ _ _ _ H.
      destruct i. lia. destruct j. injection H2 as <-. cbn in H1.
      apply nth_error_In in H1. apply Z_one_bits_lowerbound with (y:=i') in H=>//. lia.
      assert (i > j) by lia. eapply IH; eassumption.
    + eapply IHn; eassumption.
Qed.

Lemma in_Z_one_bits_last : forall x h i,
    (0 <= x < two_power_nat 64)%Z ->
    h ++ [i] = Zbits.Z_one_bits 64 x 0 ->
    (x < 2^(i+1))%Z.
Proof.
  intros ??? Hbound Hbits.
  have Huniq := Int64.Zbits_Z_one_bits_uniq x 0.
  have Hrange := Zbits.Z_one_bits_range 64 x. rewrite -Hbits in Huniq, Hrange.
  assert (Hincl: incl (h ++ [i]) (increasing 0 (Z.to_nat (i + 1)))). {
    intros ??.
    apply increasing_in. cbn.
    apply In_nth_error in H. destruct H as [n Hn].
    assert (nth_error (h ++ [i]) (length h) = Some i). {
      rewrite nth_error_app2=>//. now replace (_ - _) with 0 by lia. }
    assert (Ha: (a >= 0)%Z). { apply nth_error_In in Hn. apply Hrange in Hn. lia. }
    destruct (Nat.eqb_spec n (length h)).
    - subst n. assert (a = i) by congruence. subst. lia.
    - assert (Hlen: nth_error (h ++ [i]) n <> None) by congruence.
      apply nth_error_Some in Hlen. rewrite app_length in Hlen. cbn in Hlen.
      assert (Hlen': Datatypes.length h > n) by lia. clear Hlen.
      have H' := Z_one_bits_monotone _ _ _ _ _ _ _ _ Hbits Hlen' H Hn. lia. }
  assert (Hnodup: NoDup (h ++ [i])) by apply uniq_NoDup=>//.
  assert (Hge0: forall x : Z, In x ((h ++ [i]) ++ increasing 0 (Z.to_nat (i + 1))) -> (x >= 0)%Z). {
    intros ? Hin. apply in_app in Hin. destruct Hin as [Hin |Hin].
    - apply Hrange in Hin. lia.
    - apply increasing_ge_idx in Hin. lia. }
  have H' := powerserie_incl _ _ Hge0 Hnodup Hincl.
  rewrite powerserie_increasing in H'.
  apply Zbits.Z_one_bits_powerserie in Hbound.
  rewrite Hbits -Hbound in H'.
  rewrite Z2Nat.id in H'. lia.
  assert (0 <= i)%Z. { apply Hrange. apply in_app. right. cbn. now left. }
  lia.
Qed.

Search List.find.

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

Set Printing Coercions.
Set Printing Implicit.

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
      About before_find.
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
    Search (Z.pow).
    rewrite two_p_equiv.    
    rewrite Z.pow_add_r.
    lia.
    lia. lia.
    Search (_ + _ < _)%Z.
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
  rewrite Ha in Hinbits'. About rwP. Search (_ == true). rewrite eqb_id in Hinbits'.  
  have Hsize' := find_size a s. rewrite (rwP ssrnat.leP) in Hfindleq.
  have : forall k, k < i -> a (nth false s k) = false. intros k Hk.
  have : (ssrnat.leq (S k) (find a s)). rewrite -?(rwP ssrnat.leP). simpl. rewrite <- Hieq. lia.
  intro.
  now apply before_find.
  intro Hbefore.
  assert (forall l i',
             i' < size l ->
             i' = find a l ->
             a (nth false l i') = true ->
             (forall k, k < i' -> a (nth false l k) = false) ->
             exists l', Z.of_nat ((seq.size l) - i' - 1) :: l' = Int64.convert_from_bits_to_Z_one_bits l). {
    induction l.
    now intros.
    intros i' Hi1 Hi2 Hi3 Hk.
    destruct a0.
    rewrite Ha in Hi2. simpl in Hi2.
    simpl. rewrite Hi2. simpl.    
    rewrite Nat.sub_0_r. exists (Int64.convert_from_bits_to_Z_one_bits l). reflexivity.
    simpl.
    rewrite Ha in  Hi2. simpl in Hi2.
    rewrite  Ha in IHl. simpl in  IHl.
    assert (i' - 1 =  (find a l)). rewrite Hi2. simpl. rewrite Nat.sub_0_r. now rewrite Ha.    
    assert (forall k, k < (i' - 1) -> a (nth false l k) = false). {
      intros k' Hk'.
      assert (ssrnat.leq (S k') (find a l)). rewrite -?(rwP ssrnat.leP). lia.      
      apply  before_find; auto. }
    destruct (IHl (i' - 1)).
    simpl in Hi1. rewrite Hi2 in Hi1. rewrite H1. simpl in Hi1. lia.
    rewrite Hi2. now cbn. rewrite Hi2. simpl.
    rewrite Hi2 in Hi3. simpl in Hi3. rewrite Ha in Hi3. rewrite Nat.sub_0_r. assumption. rewrite Ha in H2. assumption. 
    assert (size l - (i' - 1) = S (size l) - i'). lia. rewrite H4 in H3.
    
    exists x0. assumption. }

  assert (forall l,             
             (Zbits.powerserie (Int64.convert_from_bits_to_Z_one_bits l) < two_p (S (size l)))%Z).
  induction l.
  cbn. unfold two_power_pos. cbn. lia.
  destruct a0. rewrite two_p_equiv.
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
  assert (forall l i',
             i' < size l ->
             i' = find a  l ->
             a (nth false l i') = true ->
             (forall k, k < i' -> a (nth false l k) = false) ->
             (Zbits.powerserie (Int64.convert_from_bits_to_Z_one_bits l) < two_p (Z.of_nat ((size l - i') - 1) + 1))%Z). { admit. }
  assert (a (nth false s i) = true).
  rewrite Hieq.
  apply nth_find.
  assumption.
  have Hkl := H3 s i.
  assert (i < size s).
  rewrite has_find in Hhas. rewrite -?(rwP ssrnat.leP) in Hhas. lia.
  specialize (Hkl H5 Hieq H4 Hbefore).
  rewrite Hsize in Hkl. rewrite Hws in Hkl.
  rewrite Hsize in H5.
  rewrite Hws in H5.
  rewrite Hn.
  rewrite Hws.
  assert (Z.of_nat (64 - i - 1) = Z.of_nat (63 - i))%Z. lia. rewrite H6 in Hkl.
  assert (Z.of_nat (63 - i) + 1 = Z.of_nat (64 - i))%Z. lia. rewrite H7 in Hkl.
  assert (x' = Zbits.powerserie (Int64.convert_from_bits_to_Z_one_bits s)). { admit.
    (*                                                                           assert (-1 < x' < Int64.modulus)%Z. *)
    (* rewrite Hx'. apply Int64.intrange. *)
    (* have : x = Int64.convert_from_bits (Int64.convert_to_bits x). *)
    (* apply Int64.convert_to_from_bits. *)
    (* intro Htofrom. *)
    (* unfold Int64.convert_from_bits in Htofrom. *)
    (* remember (Zbits.powerserie (Int64.convert_from_bits_to_Z_one_bits (Int64.convert_to_bits x))) as bits. *)
    (* assert (Int64.intval x = bits). rewrite Htofrom. simpl. *)
    (* rewrite Int64.Z_mod_modulus_id. reflexivity. *)
    (* unfold Z_to_i64 in Htofrom.  *)
    (* assert (forall y, *)
    (*            Int64.intval y = Int64.convert_from_bits (Int64.convert_to_bits y)). { *)
    (*   intro y. *)
    (*   unfold Int64.convert_to_bits. *)
    (*   have Hy := Zbits.Z_one_bits_powerserie Int64.wordsize (Int64.intval y). *)
    (*   have Hy_range := Int64.intrange y. *)
      
      
    (*   assert (0 <= Int64.intval y < two_power_nat Int64.wordsize)%Z. *)
    (*   rewrite Hws. *)
    (*   Search two_power_nat. *)
    (*   rewrite two_power_nat_equiv. *)
    (*   replace (Z.of_nat 64) with 64%Z by lia. rewrite int64_modulus_eq_pow64 in Hy_range. lia. *)
    (*   specialize (Hy H9). *)
    (*   Unset Printing Coercions. *)
    (*   unfold Int64.convert_from_bits. *)
    (*   unfold Z_to_i64. *)
    (*   assert ( *)
    (*   assert ( *)
    (*   rewrite  *)
    (*   rewrite Int64. *)
    (*   rewrite <-Int64.convert_to_from_bits. *)
    (*   f_equal. *)
      
    (*   About reverse_coercion. *)
    (*   Unset Printing Coercions.  *)
    (*   rewrite  *)
    (* simpl in Htofrom. *)

    (* simpl. *)

    (* assert (x' =  *)
    (* unfold Int64.convert_from_bits in Htofrom. *)
    
    (* apply  *) }
  rewrite H8. assumption.
Admitted.
  

(*     unfold Int64.convert_from_bits in Htofrom. *)
(*     rewrite Hx'. rewrite Htofrom. *)
(*     remember (Zbits.powerserie (Int64.convert_from_bits_to_Z_one_bits (Int64.convert_to_bits x))) as bits. simpl. *)
    
(*     rewrite Hs. unfold  *)
(*     rewrite Hs. *)
(*     unfold  *)
(*     assert (Int64.intval (Z_to_i64 (Zbits.powerserie (Int64.convert_from_bits_to_Z_one_bits (Int64.convert_to_bits x)))) = Zbits.powerserie (Int64.convert_from_bits_to_Z_one_bits (Int64.convert_to_bits x))). *)
(*     remember (Zbits.powerserie (Int64.convert_from_bits_to_Z_one_bits (Int64.convert_to_bits x))) as bits. *)
(*     simpl. *)
    
    
(*     assert (x' = powerserie *)

(*     assert (Int64.intval x = Int64.intval (Z_to_i64 (Zbits.powerserie (Int64.convert_from_bits_to_Z_one_bits (Int64.convert_to_bits x))))). *)
(*     rewrite Htofrom.  *)
(*     f_equal. *)
(*     Search Int64.intval. *)
(*     unfold Z_to_i64. *)
(*     unfold *)
(*     Int64.eq_T_intval. *)
    

(*     rewrite Hs. *)
(*     rewrite Hx'. rewrite Htofrom. *)
    
    
(*     remember (Z_to_i64 (Zbits.powerserie (Int64.convert_ *)
(*     unfold Z_to_i64. Search *)

  
(*   assert (forall l i' t,              *)
(*              i' :: t = Int64.convert_from_bits_to_Z_one_bits l -> *)
(*              (Zbits.powerserie t < two_p i')%Z). { *)
(*     induction l. now intros. *)
(*     intros i' t Hi'. *)
(*     have H2' := H2 (a0 :: l). *)
(*     simpl in Hi'. *)
(*     destruct a0. *)
(*     assert (S (size (true :: l)) = size l + 2). simpl. lia. rewrite H3 in H2'. *)
(*     simpl in H2'. *)
(*     assert (i' = Z.of_nat (size l))%Z by congruence. *)
(*     assert (t = (Int64.convert_from_bits_to_Z_one_bits l)) by congruence. *)
(*     have H2'' := H2 l. *)
(*     assert (S (size l) = size l + 1). simpl. lia. *)
(*     destruct l. cbn in H5. subst t. simpl. rewrite two_p_equiv. lia. simpl in H5. *)
(*     destruct t. simpl. rewrite two_p_equiv. lia. *)
(*     inversion Hi'. *)
(*     have IH := IHl z t H9. *)
    
(*     have IH := IHl z t H9. assumption. }              *)
(*     apply IH.     *)
(*     Hi'. assumption. }        *)
(*     rewrite H4. rewrite H6 in H2''. *)
(*     rewrite H5. *)
(*     assert (Z.of_nat (size l + 1) = Z.of_nat (size l) + 1)%Z. lia. *)
(*     rewrite H7 in H2''. assumption. *)
(*     assert (S (size (false :: l)) = size l + 2). simpl. lia. rewrite H3 in H2'. *)
(*     have IH := IHl i' t Hi'. assumption. }              *)
(*   assert (forall l i', *)
(*              i' < size l -> *)
(*              i' = find a  l -> *)
(*              a (nth false l i') = true -> *)
(*              (forall k, k < i' -> a (nth false l k) = false) -> *)
(*              (Zbits.powerserie (Int64.convert_from_bits_to_Z_one_bits l) < two_p (Z.of_nat ((size l - i') - 1) + 1))%Z). { *)
(*     induction l. now intros. *)
(*     intros i' Hi1 Hi2 Hi3 Hk.     *)
(*     have Hre := H1 (a0 :: l) i'. *)
(*     destruct Hre as [l' Hl']; auto. *)
(*     have Hre' := H3 (a0 :: l) (size (a0 :: l) - i'- 1) l' Hl'. *)
(*     destruct a0. simpl. *)
(*     simpl in Hre'. *)
(*     assert (Z.of_nat (size (a0 :: l) - i' - 1) = Z.of_nat (size l - i')). destruct a0. cbn. lia. cbn. lia. *)
(*     rewrite H4 in Hre'. *)
(*     assert (Z.of_nat (size (a0 :: l) - i' -1) = Z.of_nat (size l - i'))%Z. destruct a0. lia. lia. *)
(*     rewrite H5.     *)
(*     simpl. *)
(*     assert (Z.of_nat (size l - i') = Z.of_nat (size l) - Z.of_nat i')%Z. *)
(*     rewrite Nat2Z.inj_sub. reflexivity. simpl in Hi1. simpl. lia.     *)
(*     assert (two_p (Z.of_nat (size l - i' - 1)) + two_p (Z.of_nat (size l - i' - 1) + 1) < two_p (Z.of_nat (size l - i' - 1) + 1 + 1))%Z. { *)
(*       repeat rewrite two_p_equiv. *)
(*       replace (2 ^ (size l - i' - 1)%nat + 2 ^ ((size l - i' - 1)%nat + 1))%Z with (2^(size l - i' - 1)%nat * (1 + 2))%Z.  *)
(*       replace (2 ^ ((size l - i' - 1)%nat + 1 + 1))%Z with (2^((size l - i' - 1)%nat + 2))%Z. *)
(*       rewrite Z.pow_add_r. *)
(*       apply Zmult_lt_compat_l. lia. lia. lia. lia.       *)
(*       replace (Z.of_nat (size l - i' - 1) + 1 + 1)%Z with ((Z.of_nat (size l - i' - 1) + 2))%Z by lia. reflexivity. *)
(*       rewrite Z.mul_add_distr_l. *)
(*       rewrite Z.mul_1_r. *)
(*       rewrite Z.pow_add_r. lia. lia. lia. } *)

(*       (* assert (Z.of_nat (size l - i' - 1) = Z.of_nat (size l) - (Z.of_nat i') - 1)%Z. *) *)
(*       (* assert (Z.of_nat (size l - i') = Z.of_nat (size l) - Z.of_nat i')%Z.  *) *)
(*       (* lia. rewrite <-H6.   *) *)
(*       (* rewrite Nat2Z.inj_sub. *) *)
(*       (* replace (Z.of_nat 1) with 1%Z by lia. reflexivity. *) *)
(*       (* simpl in Hi1. *) *)
(*       (* replace (Z.of_nat 1) with 1%Z by lia. reflexivity. *) *)
(*       (* lia. *) *)
(*       (* simpl in Hi1. simpl.  *) *)
(*       (* rewrite H6.  *) *)
(*       (* apply Zmult_lt_compat_l. lia. lia. lia. lia. replace (Z.of_nat (size l - i') + 1 + 1)%Z with ((Z.of_nat (size l - i') + 2))%Z by lia. reflexivity. *) *)
(*       (* rewrite Z.mul_add_distr_l. *) *)
(*       (* rewrite H6. *) *)
(*       (* rewrite Z.mul_1_r. *) *)
(*       (* rewrite Z.pow_add_r. lia. lia. lia. } *) *)

(*     destruct a0. *)
(*     simpl in Hl'. *)
(*     inversion Hl'. rewrite <-H10. *)
(*     About Nat.add_sub_assoc. *)
(*     assert (Z.of_nat (size l - i') + 1 = Z.of_nat (1 + size l - i'))%Z. *)
(*     rewrite Z.add_comm. *)
(*     replace 1%Z with (Z.of_nat 1) by lia.  *)
(*     rewrite <-Nat2Z.inj_add. *)
(*     rewrite <-Nat.add_sub_assoc. reflexivity. lia. *)
(*     rewrite H8. rewrite Nat.add_1_l. *)
(*     simpl. *)
(*     rewrite H8 in Hre'. rewrite Nat.add_1_l in Hre'.  *)
(*     assert (forall x y y' z, y < y' -> x + y' < z -> x + y < z)%Z. intros. lia. *)
(*     destruct a0. *)
(*     simpl in Hl'. *)
(*     assert (l' = (Int64.convert_from_bits_to_Z_one_bits l)) by congruence. *)
(*     rewrite <-H8. *)
(*     simpl. simpl in H4. rewrite H4 in Hl'. *)
(*     inversion Hl'. *)
(*     rewrite <-H8. *)
(*     apply H7 with (y':=(two_p ((size l - i')%nat + 1))%Z).  lia. assumption. *)

(*     assert ( *)
(*     simpl. *)
(*     Search (S _)%nat. *)
(*     rewrite H6. *)
(*     simpl. *)
(*     rewrite H6 in Hre'. *)
(*     simpl in Hl'. *)
(*     inversion Hl'. rewrite <-H9. *)
(*     assert (S (size l) - i' - 1 = size l - i'). lia. *)
(*     rewrite H7 in H8. *)
(*     rewrite H7. *)
(*     rewrite H8.     *)
(*     assert (size l <= size l - i'). *)
(*     Unset Printing All. *)
(*     rewrite <-H8. *)
(*     assert (i' = 0). Search (_ - _ = ?c).  *)
(*     assert (i' = 0).  *)
(*     rewrite H7. *)
(*     rewrite H8. *)
    

(*     assert (two_p (Z.of_nat (size l - i' - 1)) + two_p (Z.of_nat (size l - i' - 1) + 1) < two_p (Z.of_nat (size l - i' - 1) + 1 + 1))%Z. { *)
(*       repeat rewrite two_p_equiv. *)
(*       replace (2 ^ (size l - i' - 1)%nat + 2 ^ ((size l - i' - 1)%nat + 1))%Z with (2^(size l - i' - 1) * (1 + 2))%Z.  *)
(*       replace (2 ^ ((size l - i' - 1)%nat + 1 + 1))%Z with (2^((size l - i' - 1)%nat + 2))%Z. *)
(*       rewrite Z.pow_add_r. *)
(*       assert (Z.of_nat (size l - i' - 1) = Z.of_nat (size l) - (Z.of_nat i') - 1)%Z. *)
(*       Set Printing All. *)
(*       assert (Z.of_nat (size l - i') = Z.of_nat (size l) - Z.of_nat i')%Z. Unset Printing All. *)
(*       lia. rewrite <-H6.   *)
(*       rewrite Nat2Z.inj_sub. *)
(*       replace (Z.of_nat 1) with 1%Z by lia. reflexivity. *)
      
(*       rewrite Nat2Z.inj_sub. *)
(*       replace (Z.of_nat 1) with 1%Z by lia. reflexivity. *)
(*       lia. *)
(*       simpl in Hi1. simpl.  *)
(*       (* rewrite H6.  *) *)
(*       apply Zmult_lt_compat_l. lia. lia. lia. lia. replace (Z.of_nat (size l - i') + 1 + 1)%Z with ((Z.of_nat (size l - i') + 2))%Z by lia. reflexivity. *)
(*       rewrite Z.mul_add_distr_l. *)
(*       rewrite H6. *)
(*       rewrite Z.mul_1_r. *)
(*       rewrite Z.pow_add_r. lia. lia. lia. } *)
(*     assert (forall x y y' z, y < y' -> x + y' < z -> x + y < z)%Z. intros. lia. *)
(*     destruct a0. *)
(*     simpl in Hl'. *)
(*     assert (l' = (Int64.convert_from_bits_to_Z_one_bits l)) by congruence. *)
(*     rewrite <-H8. *)
(*     simpl. simpl in H4. rewrite H4 in Hl'. *)
(*     inversion Hl'. *)
(*     rewrite <-H8. *)
(*     apply H7 with (y':=(two_p ((size l - i')%nat + 1))%Z).  lia. assumption. *)
(*     simpl in Hi2.     *)
(*     rewrite Ha in Hi2. *)
(*     rewrite <- Ha in Hi2. *)
(*     simpl in Hi2. *)
(*     assert (i' - 1 = find a l). simpl in Hi2. simpl. lia. *)
(*     assert (forall k, k < (i' - 1) -> a (nth false l k) = false). { *)
(*       intros k' Hk'. *)
(*       assert (ssrnat.leq (S k') (find a l)). rewrite -?(rwP ssrnat.leP). lia.       *)
(*       apply  before_find; auto. } *)
(*     have IH := (IHl (i' - 1)). *)
(*     have : i' - 1 < size l. *)
(*     simpl in Hi1. rewrite Hi2 in Hi1. simpl. lia. intro. *)
(*     specialize (IH H10 H8). *)
(*     have : (a (nth false l (i' - 1)) = true). *)
(*     rewrite Hi2 in Hi3. simpl in Hi3. rewrite Ha in Hi3. *)
(*     rewrite Ha. rewrite H8. rewrite <- Ha in Hi3. assumption. intro. *)
(*     specialize (IH H11 H9). *)
(*     replace (Z.of_nat (S O)) with 1%Z in IH by lia.     *)
(*     assert (Z.of_nat (size l) - (Z.of_nat (i' - 1)) + 1 = Z.of_nat (size l) - (Z.of_nat i') + 1 + 1)%Z. lia. *)
(*     assert (i' <= size l). lia. *)
(*     rewrite Nat2Z.inj_sub; auto. *)
(*     rewrite Nat2Z.inj_sub in IH; auto. *)
(*     rewrite Nat2Z.inj_sub in IH. *)
(*     replace (Z.of_nat (S O)) with 1%Z in IH by lia.     *)
(*     assert (Z.of_nat (size l) - ((Z.of_nat i') - 1) + 1 = Z.of_nat (size l) - (Z.of_nat i') + 1 + 1)%Z. lia. *)
(*     rewrite H14 in IH. assumption. lia. lia. } *)
(*   assert (a (nth false s i) = true). *)
(*   rewrite Hieq. *)
(*   apply nth_find. *)
(*   assumption. *)
(*   have Hkl := H4 s i. *)
(*   assert (i < size s). *)
(*   rewrite has_find in Hhas. rewrite -?(rwP ssrnat.leP) in Hhas. lia. *)
(*   specialize (Hkl H6 Hieq H5 Hbefore). *)
(*   rewrite Hsize in Hkl. rewrite Hws in Hkl. *)

(* 64 - *)
(*   rewrite  *)
  
(*     replace (Z.of_nat (size l *)
(*     rewrite H12 in IH. *)
(*     assert (size  *)
(*     rewrite  H12  *)

    

    
(*     rewrite Nat2Z.inj_sub in IH. *)
    
(*     assert ( *)

(*     rewrite Nat2Z.inj_sub. simpl. *)
(*     rewrite Nat2Z.inj_sub. *)
(*     assert  *)

    
    
(*     simpl. *)
(*     simpl. *)
    

(*     have :  *)
(*     assumption. *)
    
(*     simpl in Hi3. rewrite Nat.sub_0_r. assumption. rewrite Ha  *)



(*     simpl in Hi2.  *)
(*     assert (Zbits.powerserie l' < two_p ((size l - i')%nat + 1 + 1))%Z.  *)
(*       replace (2 ^ (Z.of_nat (size l - i')) * 2)%Z with (2^(size l + 1))%Z. rewrite Z.mul_1_r. reflexivity. *)
(*       rewrite Z.pow_add_r. lia. lia. lia. lia. } *)

(*       replace 4%Z with (2 * 2)%Z by lia. *)
      
(*  rewrite [(2^(Z.of_nat (size l -i)))%Z] <-Nat.add_0_r.  *)
(*       replace ( *)
     
(*     assert ( *)
(*     assert (size l = size l - i') by congruence. *)
    
    
(*     assert (Z.of_nat (size (a0 :: l) - i') + 1 = Z.of_nat (size l - i') + 2)%Z. destruct a0. cbn. *)
    


(*     (* intros. rewrite Nat.sub_0_r. *) *)
(*     (* have H2' := H2 l. *) *)
(*     (* assert (Z.of_nat (S (size l)) = Z.of_nat (size l) + 1)%Z. lia. rewrite H7 in H2'. assumption.  *) *)
    
(*     (* replace (Z.of_nat (S (size l))) with (Z.of_nat (size l) + 1)%Z in H2'. *) *)
(*     (* simpl in H2'. replace (two_p (S (size l))%nat) with (two_p (size l + 1)%nat) in H2'. *) *)
(*     intros i' Hi1 Hi2 Hi3 Hk.     *)
(*     have Hre := H1 (a0 :: l) i'.     *)
(*     destruct Hre as [l' Hl']; auto. *)
(*     (* simpl in Hi1. simpl.  *) *)
(*     (* have Hre' := H2 l. *) *)
(*     rewrite <-Hl'. *)
(*     (* simpl. *) *)
(*     (* rewrite <-Hl'. *) *)
(*     (* simpl. *) *)
(*     assert (S (size l) - i' - 1 = size l - i'). lia.     *)
(*     About Int64.convert_from_bits_to_Z_one_bits. *)
(*     rewrite  H3. *)
(*     destruct a0. *)
(*     simpl in  Hl'. *)
(*     replace l' with (Int64.convert_from_bits_to_Z_one_bits l) by congruence. *)
(*     assert (Zbits.powerserie (Int64.convert_from_bits_to_Z_one_bits l) < two_p (S (size l)))%Z. *)
(*     apply H2. *)
(*     Set  Printing All. *)
(*     replace (Z.of_nat (S (@size bool l) - i')) with (Z.of_nat (@size bool l) - (Z.of_nat i') + 1)%Z. *)
(*     Unset Printing All. *)
(*     assert (two_p (size l - i') < two_p ((Z.of_nat (size l)) - (Z.of_nat i') + 1))%Z. *)
(*     rewrite two_p_equiv. rewrite two_p_equiv. *)
(*     replace (2 ^ (size l - i'))%Z with (2^(size l - i') * 1)%Z. *)
(*     rewrite Z.pow_add_r. apply Zmult_lt_compat_l. *)
(*     Search (0 < _ ^_)%Z. apply Z.pow_pos_nonneg. lia. simpl in Hi1. assert (i' <= size l). Search (_ < S _). *)
(*     apply Nat.lt_succ_r. Set Printing All. simpl. lia. Unset Printing All. *)
(*     lia. lia. *)
(*     simpl in Hi1. assert (i' <= size l). simpl. *)
(*     lia. lia. lia. lia. *)
(*     assert (two_p (size l) < two_p (size l - i'))%Z. admit. *)

    
(*     have IH := IHl (i' - 1). *)
(*     assert ((i' - 1) < size l). *)
(*     simpl in Hi1. assert (i' - 1 <= size l). simpl. lia. simpl. simpl in Hi2. destruct a.  *)
(*     apply Nat.lt_sub_lt_add_r. *)

(*     have IH :=  *)
    
    
(*     rewr *)
    

    
(*     assert (two_p (size l - i') < two_p (S (size l) - i'))%Z. *)
(*     rewrite two_p_equiv. assert (S (size l) - i' = 1 + (size l - i')). Search (S _ - _). rewrite Nat.sub_succ_l. lia. *)
(*     cbn in Hi1. simpl in Hi1. simpl. lia. *)
(*     Set  Printing All. *)
    
(*     rewrite H5. *)
(*     simpl. *)
    
(*     rewrite  *)
(*     assert  *)
(*     replace (S (size l) - i')  with ((size l - i') + i'). *)
(*     replace (two_p (Z.of_nat (S (size l) - i'))) with (two_p ((Z.of_nat (size l - i') + 1)))%Z.  *)
(*     rewrite two_p_equiv. *)
(*     replace (Z.of_nat (S (size l) - i')) with ((Z.of_nat (size l - i') + 1))%Z.  *)
    
(*     simpl in Hl'. *)

(*   assert (2 ^ (size l) +  2 ^ (Z.of_nat (size l) + 1) < 2^ (Z.of_nat (size l) + 2))%Z. { *)
(*     Search (_ + _ < _)%Z. *)
(*     replace (2^ (Z.of_nat (size l)) + 2^(Z.of_nat (size l) + 1))%Z with (2^(size l) * 3)%Z. *)
(*     replace (2^(Z.of_nat (size l) + 2))%Z with (2^(size l) * 4)%Z. *)
(*     Search (_ * _ <  _ * _)%Z. *)
(*     apply Zmult_lt_compat_l. lia. lia. replace 4%Z with (2 * 2)%Z by lia. *)
(*     replace (2 * 2)%Z with (2^2)%Z by lia. rewrite Z.pow_add_r. reflexivity. lia. lia. *)
(*     replace 3%Z with (1 + 2)%Z. *)
(*     Search (_ * ( _ + _))%Z. *)
(*     rewrite Z.mul_add_distr_l. *)
(*     replace (2 ^ (size l) * 2)%Z with (2^(size l + 1))%Z. rewrite Z.mul_1_r. reflexivity. *)
(*     rewrite Z.pow_add_r. lia. lia. lia. lia. } *)
(*   lia. lia. lia. lia. simpl. lia. *)
    
(*     rewrite two_p_equiv. *)
    
    
(*     replace  l' with (Int64.convert_from_bits_to_Z_one_bits l) by congruence. *)

(*     replace ( *)
(*     destruct a0. *)

(*     rewrite  Hi2. *)
(*     simpl. *)
(*     rewrite Nat.sub_0_r. *)
(*     rewrite Nat.sub_0_r. *)

    
(*   replace (2^(Z.of_nat (size l) + 2))%Z with (2^(size l) * 4)%Z. *)
  
(*   cbn. unfold two_power_pos. cbn. lia. *)
(*   destruct a0. rewrite two_p_equiv. *)
(*   replace (S (size (true :: l))) with (size l + 2).  *)
(*   simpl. rewrite two_p_equiv in IHl. rewrite two_p_equiv. replace  (S (size l)) with (size l + 1) in IHl. *)
  
(*     reflexivity. *)
(*     rewrite Zmult_distr_l. *)
(*     replace *)
    
(*   simpl. *)
  
  
(*   unfold Int64.convert_from_bits_to_Z_one_bits. *)
(*   cbn.  *)
  
(*              i' < size l -> *)
(*              i' = find a  l -> *)
(*              a (nth false l i') = true -> *)
(*              (forall k, k < i' -> a (nth false l k) = false) -> *)
(*              (Zbits.powerserie (Int64.convert_from_bits_to_Z_one_bits l) < 2^(Z.of_nat (size l - i')))%Z). { *)
(*     induction l. now intros. *)
(*     intros i' Hi1 Hi2 Hi3 Hk. *)
(*     have Hre := H1 (a0 :: l) i'. *)
(*     destruct Hre as [l' Hl']; auto.     *)
(*     rewrite <-Hl'. *)
(*     simpl. *)
(*     assert (S (size l) - i' - 1 = size l - i'). lia. *)
(*     rewrite  H2. *)
(*     rewrite two_p_equiv. *)
(*     destruct a0. *)

(*     rewrite  Hi2. *)
(*     simpl. *)
(*     rewrite Nat.sub_0_r. *)
(*     rewrite Nat.sub_0_r. *)

(*     simpl in Hl'. *)

(*     replace  l' with (Int64.convert_from_bits_to_Z_one_bits l) by congruence. *)
(*     assert (S (size l) - i' - 1 = size l - i'). lia. *)
(*     rewrite  H2. *)
(*     rewrite two_p_equiv. *)
(*     rewrite  Hi2. *)
(*     simpl. *)
(*     rewrite Nat.sub_0_r. *)
(*     rewrite Nat.sub_0_r. *)

(*     rewrite Ha in Hi2, Hi3. *)
(*     simpl in Hi3. *)
(*     simpl in Hi2. *)
(*     simpl in Hi1. *)
(*     lia. *)
(*     rewrite Ha in Hi2, Hi3. *)
(*     simpl in Hi3. *)
(*     simpl in Hi2. *)
(*     simpl in Hi1. *)
(*     have IH := IHl (i' - 1). *)
    
(*     assert (S (size l) - i' - 1 = size l - i'). lia. *)
(*     rewrite  H2. *)
(*     rewrite two_p_equiv. *)
(*     rewrite  Hi2. *)
(*     rewrite Nat.sub_0_r. *)
(*     rewrite Nat.sub_0_r. *)
    
(*     destruct i'. *)
(*     have IH ( *)

(*     replace (two_p (Z.of_nat (S (size l) -i' - 1))) with (two_p (Z.of_nat (size l - i'))). *)
(*     About  two_p. *)
(*     simpl in i *)
    
    
             
(*              l,  *)
(*    rewrite H1. *)
    
(*     rewrite Hi2. simpl cbn.  rewrite Nat.sub_0_r. *)
(*     rewrite Hi2. cbn. rewrite Nat.sub_0_r. *)
(*     assert (has a l).  *)
    
    
(*       simpl in  H1 |-*. *)
(*       assert (i' - 1) *)
(*       have Hbefore' := before_find. *)
(*       apply before_find. *)
(*       have Hk2 := Hk k' H *)
      
(*       destruct k'. simpl in Hk2. simpl. *)
(*       simpl in Hk2. *)
(*       rewrite Ha in Hk2. *)

(*       assert (k' < i'). lia. *)
      
(*       destruct k'. simpl in Hk2. simpl. *)

(*       simpl in Hk2. *)
(*       simpl. *)
(*       simpl in Hk2. *)
(*       apply Hk  *)
(*       rewrite Hi2 in  Hk'. simpl in Hk'. *)
      
(*       rewrite Nat.sub_0_r in Hk'.  *)
(*     rewrite <-Ha in Hi2. *)
    
    
(*     unfold  *)
(*     unfold Int64.convert_from_bits_to_Z_one_bits. *)
(*     destruct (eq_dec i' a0). *)
          
(*       convert_from_bits_to_Z_one_bits ( *)
(*   assert ( *)


(*   intros k Hk. *)
(*   Search  (~~ (_ \in _)). *)
  
  
(*   rewrite -?(rwP eqB) in Hinbits.' *)
(*   rewrite  *)

(*   assert (inbits = true). *)
  
(*   rewrite has_find.  *)


(*   have Hsize := Int64.convert_to_bits_size x. rewrite <-Hs in Hsize. *)
(*   assert (find a s <= size s).  *)
(*   have Hsize' := find_size a s. auto.  *)
(*   rewrite -?(rwP ssrnat.leP) in Hsize'. *)
(*   simpl in Hsize'. *)
(*   simpl. lia. *)
(*   simpl in H1. *)
(*   rewrite Hsize in H1.   *)
(*   replace Int64.wordsize with 64 in H1. *)
(*   rewrite int64_modulus_eq_pow64. split. lia. lia. *)
(*   unfold Int64.wordsize, Integers.Wordsize_64.wordsize. reflexivity. *)
(*   assert (i = find a s). *)
(*   rewrite H1 in Hclz. Search (Z.to_nat (Z.of_nat _)). by rewrite Nat2Z.id in Hclz. *)
(*   assert (inbits = true). *)
(*   assert (has a s). *)
(*   rewrite has_find. rewrite -?(rwP ssrnat.leP). *)
  
(*   assert (Z.of_nat (find a s) <= 64)%Z. lia. cbn. *)

(*   assert ( *)
(*   auto. *)
(*   have H *)
(*   Check (size s).   *)
(*   replace (size s) with Int64.wordsize in Hsize. *)
(*   assert (find a s < 64). replace 64 with Int64.wordsize. *)
  
(*   )  = ( *)
  
(*   assert (i = find a (Int64.convert_to_bits x)). *)
  
  
(*   simpl in Hclz. *)
(*   assert (inbits = true). rewrite Hinbits. *)
  
(*     intro Hcontra. *)
(*     Search seq.nth. *)
    
      
(*     List.last (Zbits.Z_one_bits Int64.wordsize (Int64.intval x) 0) =  *)

(*     (2^63 <= 2^i * x < 2^64)%Z. *)


(* Lemma  *)

(* Lemma clz_spec : forall x i, *)
(*     (0 < x < Int64.modulus)%Z -> *)
(*     Int64.repr i = Int64.clz (Int64.repr x) -> *)
(*     (2^63 <= 2^i * x < 2^64)%Z. *)
(* Proof. *)
(* intros x i Hx Hi. *)
(* unfold Int64.clz in Hi. *)
(* assert (HiRange : (0 <= i < 63)%Z). admit. *)
(* assert (Hlast : exists l, l ++ [(63 - i)%Z] = Zbits.Z_one_bits Int64.wordsize x 0). admit. *)
(* destruct Hlast as [l Hlast]. *)
(* have : (x < 2^((63 - i) + 1))%Z. *)
(* apply in_Z_one_bits_last with (h:=l). *)
(* rewrite int64_modulus_eq_pow64 in Hx.  *)
(* rewrite two_power_nat_two_p. rewrite two_p_equiv. lia. *)
(* unfold Int64.wordsize in Hlast.  unfold Integers.Wordsize_64.wordsize in Hlast. assumption.  *)
(* intro Hupper. *)
(* have : (2^(63 - i) <= x)%Z. admit. *)
(* intro Hlower. *)
(* split. *)
(* replace (2^63)%Z with (2^i * 2^(63 - i))%Z. *)
(* apply Zmult_le_compat_l; auto with zarith. rewrite <-Z.pow_add_r. replace (i + (63 - i))%Z with 63%Z by lia. reflexivity.  lia. lia.  *)
(* replace (2^64)%Z with (2^i * 2^(63 - i + 1))%Z.  *)
(* apply Zmult_lt_compat_l; auto with zarith. *)
(* replace (63 - i + 1)%Z with (64 - i)%Z by lia. *)
(* rewrite <-Z.pow_add_r. replace (i + (64 - i))%Z with 64%Z by lia. reflexivity. lia. lia. *)
(* Admitted. *)
    

(* Lemma clz1 : forall x, *)
(*     (0 < x < Int64.modulus)%Z -> *)
(*     (Int64.unsigned (Int64.clz (Int64.repr x)) < Int64.wordsize)%Z. *)
(* Proof. *)
(* intros. *)
(* destruct (Z.eq_dec 0 x). *)
(* unfold Int64.clz. subst x. cbn. simpl. lia.  *)


(* assert (Int64.clz (Int64.repr 0) = Int64.wordsize). unfold Int64.clz.  *)

(* cbn. *)
(* cbn. *)
(* unfold Int64.clz in  *)


(* Lemma clz_spec : forall x i, *)
(*     (0 < x < Int64.modulus)%Z -> *)
(*     i = Int64.unsigned (Int64.clz (Int64.repr x)) -> *)
(*     (2^63 <= 2^i * x < 2^64)%Z. *)
(* Proof. *)
(*   intros x i Hx Hi. *)
(*   assert (Hws: Int64.wordsize = 64) by (unfold Int64.wordsize, Integers.Wordsize_64.wordsize; reflexivity). *)
(*   assert (Htpn: two_power_nat 64 = Int64.modulus). { *)
(*     rewrite two_power_nat_two_p. replace (Z.of_nat 64) with Int64.zwordsize. rewrite <-Int64.modulus_power. reflexivity. now cbn. } *)
(*   assert (Htpn' : two_power_nat 64 = (2^64)%Z) by now rewrite int64_modulus_eq_pow64 in Htpn. *)
(*   assert (Int64.intval x = x)%Z. { *)
(*     cbn. rewrite Int64.Z_mod_modulus_id; auto; lia. } *)
(*   unfold Int64.clz in Hi. *)
(*   Search Int64.unsigned. *)
(*   rewrite Int64.unsigned_repr in Hi. 2: {  *)
(* Search (ssrnat.leq (find _) _)%Z. *)
(* have Hsize := find_size ((fun b => b == true)) (Int64.convert_to_bits (Int64.repr x)). *)
(* move/ssrnat.leP in Hsize. *)
(* rewrite Int64.convert_to_bits_size in Hsize. unfold Int64.max_unsigned. unfold Int64.wordsize in Hsize. unfold Integers.Wordsize_64.wordsize in Hsize. rewrite int64_modulus_eq_pow64. lia. } *)
(* assert (ssrnat.leq (find (fun b : bool_eqType => b == true) (Int64.convert_to_bits (Z_to_i64 x))) (size (Int64.convert_to_bits (Z_to_i64 x)))).  *)
(* rewrite find_size. auto. *)
(* rewrite Int64.convert_to_bits_size in H0. unfold Int64.wordsize, Integers.Wordsize_64.wordsize in H0. *)
(* move/ssrnat.leP in H0.  *)
(* assert (i <= 64)%Z by lia. *)
(* have : (Zbits.Z_one_bits 64 x 0%Z <> nil).  *)
(* apply one_bits_non_zero. lia. lia. intros. *)

(* assert (ssrnat.leq 0 (find (fun b : bool_eqType => b == true) (Int64.convert_to_bits (Z_to_i64 x)))). *)
(* apply ssrnat.leq0n. *)
(* move/ssrnat.leP in H2.  *)
(* assert (0 <= i)%Z by lia. *)
(* assert (Hi' : (63 - i)%Z \in (Zbits.Z_one_bits 64 x 0)). {         *)
(*   unfold Int64.clz in Hi. *)
(*   unfold Int64.convert_to_bits in Hi. *)

(*   have: (has (fun b => b == true) (Int64.convert_to_bits (Int64.repr x))). *)
(*   rewrite has_find. rewrite Int64.power_index_to_bits_size.  *)
(*   rewrite Hws. rewrite lt_pow64_unsigned_id in Hi; auto. *)
(*     (* assert (S (find (fun b : bool_eqType => b == true) (Int64.convert_to_bits (Z_to_i64 x))) <= 64). *) *)
(*     have Hrefl := ssrnat.leP. *)
(*     have Hrefl' := reflect_iff _ _ (Hrefl (S (find (fun b : bool_eqType => b == true) (Int64.convert_to_bits (Z_to_i64 x)))) 64). *)
(*     have Hsize := Int64.convert_to_bits_size (Int64.repr x). rewrite Hws in Hsize. *)
(*     (* rewrite Hrefl' in H1. auto. *) *)
    
(*     have Hfind_size := find_size (fun b : bool_eqType => b == true) (Int64.convert_to_bits (Z_to_i64 x)).  *)
(*     assert (0 <= find (fun b : bool_eqType => b == true) (Int64.convert_to_bits (Z_to_i64 x))). *)
(*     unfold find. destruct (Int64.convert_to_bits (Z_to_i64 x)); lia. *)
(*     rewrite Hsize in Hfind_size. *)
(*     have Hfd := (ssrnat.leP Hfind_size). lia. *)
(*     intro. *)
(*     assert (Z.of_nat (Int64.wordsize - (Z.to_nat i) - 1) \in Zbits.Z_one_bits Int64.wordsize (Int64.intval x) 0). *)
(*     assert (seq.nth false (Int64.convert_to_bits (Int64.repr x)) (Z.to_nat i) = true).  (* = (64 - (Z.to_nat i) - 1)%Z \in (Zbits.Z_one_bits 64 x 0)). { *) *)

(*     apply nth_find with (x0:=false) (a:=(fun b : bool_eqType => b == true)) (s:=(Int64.convert_to_bits (Z_to_i64 x))) in H1. *)
(*     rewrite lt_pow64_unsigned_id in Hi; auto. *)
(*     rewrite Hi. *)
(*     rewrite Nat2Z.id. auto. *)
(*     unfold is_true in H1. *)
(*     auto. *)
(*     have HeqP := eqP H1. *)
(*     auto. *)
(*     have Hsize := Int64.convert_to_bits_size (Int64.repr x). rewrite Hws in Hsize. *)
(*     have Hfind_size := find_size (fun b : bool_eqType => b == true) (Int64.convert_to_bits (Z_to_i64 x)).  *)
(*     assert (0 <= find (fun b : bool_eqType => b == true) (Int64.convert_to_bits (Z_to_i64 x))). *)
(*     unfold find. destruct (Int64.convert_to_bits (Z_to_i64 x)); lia. *)
(*     rewrite Hsize in Hfind_size. *)
(*     have Hfd := (ssrnat.leP Hfind_size). lia. *)
(*     assert (ssrnat.subn (ssrnat.subn Int64.wordsize (Z.to_nat i)) 1 = Int64.wordsize - Z.to_nat i - 1) by auto. *)
(*     rewrite <-H3. *)
(*     rewrite Int64.convert_to_bits_nth in H2. *)
(*     rewrite H. *)
(*     replace (Int64.intval (Int64.repr x)) with x in H2. *)
(*     auto. *)
(*     rewrite Hws. *)
(*     assert (S (Z.to_nat i) <= 64) by lia.     *)
(*     now eapply (introT ssrnat.leP) in H2. *)
(*     rewrite Hws in H2. *)
(*     replace (64 - Z.to_nat i - 1) with (63 - Z.to_nat i) in H2 by lia. *)
(*     replace (Z.of_nat (63 - Z.to_nat i)) with (63 - i)%Z in H2 by lia. *)
(*     rewrite H in H2. assumption. } *)
(*   assert (0 < x < two_power_nat 64)%Z by auto. *)
(*   have Hbounds := in_Z_one_bits x (63 - i)%Z H1 Hi'. *)
(*   rewrite Htpn' in Hbounds. *)
(*   clear H1. *)
(*   split. *)
(*   destruct Hbounds. *)
(*   assert (2^(63 - i) = 2^63/2^i)%Z. *)
(*   rewrite Z.pow_sub_r; lia. *)
(*   assert ((2^i * x) / 2^i = x)%Z. *)
(*   rewrite Z.mul_comm. rewrite Z_div_mult. reflexivity. *)
(*   lia. *)
(*   (* rewrite <- H4 in H1. *) *)
(*   (* rewrite H3 in H1. *) *)
(*   assert ((2^(63-i)) * 2^i = 2^63)%Z.  *)

(* assert (63 = (63 - i) + i)%Z. lia. *)
(* assert (2^63 = 2^((63 - i) + i))%Z. pattern (2^63-i + i)%Z. rewrite <- H5. reflexivity. *)
(* rewrite H6. *)

(* rewrite <-Z.pow_add_r. reflexivity. lia. lia. *)
(* rewrite Z.mul_comm. *)
(* rewrite <-H5. *)
(* apply Zmult_le_compat. assumption. lia. lia. lia.  *)
(* destruct Hbounds.  *)
(* assert (2^(63 - i) < 2^64)%Z. lia. *)
(* assert (2^i * x < 2^i * 2^64)%Z. nia. *)
(* assert (2^64 < 2^i * 2^64)%Z. *)
(* assert (1 < 2^i)%Z. *)
(* assert (0 < i)%Z by lia. *)
(* assert (1 <= i)%Z by lia. *)
(* assert (1 < 2^1)%Z by lia. *)
(* Search Z.pow. *)
(* apply Zpow_facts.Zpower_gt_1. *)
(* lia. *)
(* lia. lia. *)
(* assert (2^64 = 2^i * 2^(64 - i))%Z.  *)
(* rewrite <-Z.pow_add_r.  *)
(* replace (i + (64 - i))%Z with 64%Z by lia. reflexivity. *)
(* lia. lia.  *)
(* assert (Z.log2 x < 64)%Z. *)
(* apply Z.log2_lt_pow2. lia. lia.  *)
(* assert (0 <= Z.log2 x)%Z. *)
(* apply Z.log2_nonneg. *)
(* assert (0 <= Z.log2 x < Z.of_nat 64)%Z. lia. *)
(* assert (Zbits.Z_one_bits 64 (two_p (Z.log2 x)) i = [(i + Z.log2 x)%Z]). { *)
(*   apply Zbits.Z_one_bits_two_p. lia. } *)
(*     assert (forall n x i j, *)
(*                In j (Zbits.Z_one_bits n x i) -> (i <= j < i + Z.of_nat n)%Z). *)
(*   { *)
(*   induction n; simpl In. *)
(*   tauto. *)
(*   intros x0 i0 j0. rewrite Nat2Z.inj_succ. *)
(*   assert (In j0 (Zbits.Z_one_bits n (Z.div2 x0) (i0 + 1)) -> (i0 <= j0 < i0 + Z.succ (Z.of_nat n))%Z). *)
(*     intros. exploit IHn; eauto. lia. *)
(*   destruct (Z.odd x0); simpl. *)
(*   intros [A|B]. subst j0. lia. auto. *)
(*   auto. *)
(*   } *)

(* assert (In (i + Z.log2 x)%Z (Zbits.Z_one_bits 64 (two_p (Z.log2 x)) i))%Z. { *)
(*   unfold In. *)
(*   destruct (Zbits.Z_one_bits 64 (two_p (Z.log2 x)) i)%Z. discriminate. *)
(*   left. congruence. } *)
(*   apply H11 in H12. *)
(* assert (Z.log2 x < i + Z.log2 x)%Z. { *)
(* lia. } *)
(* assert (In (i + Z.log2 x)%Z (Zbits.Z_one_bits 64 (two_p (Z.log2 x)) 0))%Z. { *)
(*   unfold In. *)
(*   Search (2 ^ (Z.log2 _))%Z. *)
(*   destruct (Zbits.Z_one_bits 64 (two_p (Z.log2 x)) i)%Z. discriminate. *)
(*   left. congruence. } *)
(*   apply H11 in H12. *)
(* assert (Z.log2 x < i + Z.log2 x)%Z. { *)
(* lia. } *)

(* assert (Zbits.Z_one_bits *)

  
(*   simpl. *)
(*   cbn. *)
(*   Search In. *)
(*   apply in_eq. *)
(*   have H11' := H11 64 ((two_p (Z.log2 x))) i (i + Z.log2 x)%Z. *)
(*   constructor *)
(* assert (i <= i + Z.log2 < i +  *)
(*   assert (x = two_p (Z.log2 x)). { *)
(*     Search two_p. *)
(* Search Z.pow. *)
(* Search Z.log2. *)
  
(* About Z.log2_le_mono. *)
(* Search (Z.log2 _ < Z.log2 _)%Z. *)
(* Search Z.pow. *)
(* assert (Z.log2 (2^64) = 64)%Z.  *)
(* Search Z.pow. *)
(* rewrite Z.log2_pow2. lia. lia. *)
(* Search (Z.log2 _ < _)%Z. *)


(*   assert (Hlog1: (Z.log2 (2^63) <= Z.log2 (2 ^ (Int64.unsigned (Int64.clz (Int64.repr x))) * x))%Z) by (apply Z.log2_le_mono; assumption).     *)
(*   assert (Hlog2: (Z.log2 (2 ^ (Int64.unsigned (Int64.clz (Int64.repr x))) * x) < 64)%Z) by (apply Z.log2_lt_pow2; lia). *)
(*   replace (2 ^ (Int64.unsigned (Int64.clz (Int64.repr x))) * x)%Z with (x * 2 ^ (Int64.unsigned (Int64.clz (Int64.repr x))))%Z in Hlog1, Hlog2 by lia. *)



(*
Lemma in_Z_one_bits_pow' : forall l i,
    (0 < i)%Z ->
    (forall j, In j l -> (0 <= 2^j + Zbits.powerserie l < 2^(i + 1)))%Z ->
    (Zbits.powerserie l < 2^i)%Z.
Proof.
  induction l. intros. cbn. lia.
intros.
cbn. auto.
  rewrite two_p_equiv. 
  cbn. auto.
 (* Hin Hj1 Hj2. *)  
  cbn in Hin.
  cbn. lia.
  cbn.

assert (0 <= 2^a + Zbits.powerserie l < 2^(n + 1))%Z. 
assert (Zbits.powerserie l = Zbits.powerserie (filter (fun x => x != a) (a ::l))). {
  f_equal.
  cbn.  
  assert (zeq a a). 
  unfold zeq. destruct (Z.eq_dec a a). auto. auto. 
  assert (~~ zeq a a = false). unfold negb. now rewrite H.
  rewrite H0.
  rewrite filter_for_all. auto.
  rewrite list_all_forall.  intro.
  rewrite -List_In_in_mem => I. admit. }
  (* subst a0. *)
  (* cbn in Huniq. *)
  (* unfold negb in Huniq. *)
  (* rewrite I in Huniq. discriminate. } *)

(* assert (~~ zeq a a).  *)
(* Search (~~ _)%Z. *)

(*   rewrite Z_eqP *)
(*   About zeq. *)
(*   unfold zeq. *)
  
(*   destruct (Z.eq_dec a a); auto. *)
(*   assert (zeq a a).   *)
(*   rewrite zeq_false. *)
(*   rewrite filter_for_all. auto. *)
(*   rewrite list_all_forall.  intro. *)
(*   rewrite -List_In_in_mem => I. apply /eqP => ?.  *)
(*   subst a0. *)
(*   cbn in Huniq. *)
(*   unfold negb in Huniq. *)
(*   rewrite I in Huniq. discriminate. } *)
assert (forall j : Z_eqType,
        In j l ->
        (0 <= 2 ^ j + Zbits.powerserie (filter (fun x => x != j) l) < 2 ^ (n + 1))%Z).
{ admit. }
assert (Huniq' : uniq l). admit.
have IH := IHl n Hn Huniq' H0.

assert (
 Search (_ + _ < _)%Z.
have H

intros.
assert (In j (a :: l)). cbn. right; auto.
have Hinn := Hin j  H2.
assert 
rewrite H in H0. 



rewrite <-List_In_in_mem in H0.
cbn in H0.
cbn in H0.

assert (Zbits.powerserie l = Zbits.powerserie (filter (fun x => x != a) l)). {
  f_equal.
  rewrite filter_for_all. auto.
  rewrite list_all_forall.  intro.
  rewrite -List_In_in_mem => I. apply /eqP => ?. 
  subst a0.
  cbn in Huniq.
  unfold negb in Huniq.
  rewrite I in Huniq. discriminate. }

rewrite H.
apply Hin. cbn. left; auto.
assert (uniq l). admit.
assert (forall j, In j l -> (0 <= j < n))%Z. intros. apply Hin. cbn. right; auto. 
have IH := IHl n Hn H0 H1. Search (_ + _ < _)%Z.
cbn.
Search uniq.
cbn in Huniq. unfold "&&" in Huniq. 
  contradiction.
  unfold Zbits.powerserie.

  fold Zbits.powerserie.  
  destruct (Z.eq_dec i a).
  rewrite <-e in *.
  have Hj1' := Hj1 i Hin.
  have Hj2' := Hj2 i Hin.
  unfold Zbits.powerserie in Hj2'.
  fold Zbits.powerserie in Hj2'.  
  rewrite two_p_equiv in Hj2'.
  replace (2^i + Zbits.powerserie l + 2^i)%Z with (2 * 2^i + Zbits.powerserie l)%Z in Hj2' by lia.
  rewrite Z.add_comm.
  rewrite Z.mul_add_distr_l.
  rewrite <-Z.pow_add_r.
  replace (n - i - 1 + i)%Z with (n - 1)%Z by lia.
  Search (_ * _ < _)%Z.
  Zbits.powrser
  
  
 rewrite Z.pow_sub_r. lia. lia. lia. lia. lia. lia.   
  rewrite 
  rewrite Z.mul_add_distr-
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
  assert (2 ^i <= Zbits.powerserie l)%Z. apply IHl; auto. lia.
Qed.

Require ZifyComparison.

Add Zify BinOp ZifyInst.Op_Z_pow.
  Search Z.pow.
Add Zify Saturate ZifyInst.SatPowNonneg.
Add Zify Saturate ZifyInst.SatPowPos.

Lemma head_Z_one_bits_pow_eq : forall t n x i,
    (0 <= x < two_power_nat n)%Z ->
    i :: t = rev (Zbits.Z_one_bits n x 0) ->
    (x = 2^i + Zbits.powerserie t)%Z.
Proof.
  intros.
  assert (x = Zbits.powerserie (Zbits.Z_one_bits n x 0)).
  (* assert (0 <= x < 2^64)%Z. *)
  (* rewrite Htpn' in H. auto. *)


  apply Zbits.Z_one_bits_powerserie. lia.
  assert (forall l k, 
             Zbits.powerserie (l ++ [k]) = Zbits.powerserie (k :: l))%Z. {
    intro. induction l. intros. cbn. reflexivity.
    intros.
    cbn.
    assert (two_p a + Zbits.powerserie l = (Zbits.powerserie (a :: l)))%Z. now cbn.
    rewrite H2. rewrite IHl. cbn. lia. }
  assert (forall m y j,
             Zbits.powerserie (Zbits.Z_one_bits m y j) = Zbits.powerserie (rev (Zbits.Z_one_bits m y j)))%Z. {
    intro. induction m. intros. cbn. unfold Zbits.powerserie. unfold rev. now cbn.
    intros.
    cbn.
    destruct (Z.odd y).
    unfold rev.  cbn. rewrite catrevE.
    assert (two_p j + Zbits.powerserie (Zbits.Z_one_bits m (Z.div2 y) (j + 1)) = Zbits.powerserie (j :: (Zbits.Z_one_bits m (Z.div2 y) (j + 1))))%Z. now cbn.
    rewrite H3.
    rewrite H2. cbn. now rewrite IHm.  apply IHm. }
  have Hp := H3 n x 0%Z. 
replace (Zbits.powerserie (Zbits.Z_one_bits n x 0)) with x in Hp.
rewrite <-H0 in Hp. simpl in Hp.
now rewrite <-two_p_equiv. 
Qed.

Lemma head_Z_one_bits_pow_lt : forall n t x i j,
    (0 <= x < two_power_nat n)%Z ->
    (0 <= i < two_power_nat n)%Z ->
    (forall j, In j (Zbits.Z_one_bits n x j) -> 0 <= j < two_power_nat n)%Z ->
    (Zbits.Z_one_bits n x j) = t ++ [i] ->
    (2^(n - 1 - i) * Zbits.powerserie (Zbits.Z_one_bits n x j) < 2^n)%Z. 
Proof.
  induction n; intros.
  (* have Hx := head_Z_one_bits_pow_eq _ _ _ _ H H0.  *)
  (* symmetry in H0. *)
  (* apply rev_move in H0. unfold rev in H0. replace (catrev [i] []) with [i] in H0 by now cbn. *)
  cbn. lia.
  assert (0 <= i < Z.of_nat n)%Z. eapply Zbits.Z_one_bits_range with (x:=x); eauto.  
  rewrite <-H0. cbn. left. auto.
  rewrite <-H0. unfold Zbits.powerserie.
  rewrite two_p_equiv.
  replace (2^i + 0)%Z with (2^i)%Z by lia. 
  rewrite <-Z.pow_add_r. 
  replace (n - 1 - i + i)%Z with (n - 1)%Z. rewrite Z.pow_sub_r. lia. lia. lia. lia. lia. lia. 
  
  have Hx := head_Z_one_bits_pow_eq _ _ _ _ H H0.

 
  symmetry in H0.
  apply rev_move in H0. unfold rev in H0. replace (catrev [i] []) with [i] in H0 by now cbn.

  assert (0 <= i < Z.of_nat n)%Z. eapply Zbits.Z_one_bits_range with (x:=x); eauto.  
  

  rewrite two

  symmetry in H0. 
  rewrite H0. cbn. left; auto. lia. lia.

  assert (x = Zbits.powerserie (Zbits.Z_one_bits n x 0)).

rewrite H1 in Hp.

  rewrite H0 in H2. cbn in H2.
  rewrite two_p_equiv in H2. replace x with (2^i)%Z by lia.
  rewrite Z.pow_add_r. lia. lia. lia.



Lemma head_Z_one_bits_upper_bound : forall t x i,
    (0 <= x < two_power_nat 64)%Z ->
    i :: t = rev (Zbits.Z_one_bits 64 x 0) ->
    (x < 2^(i + 1))%Z.
Proof.
  assert (Htpn: two_power_nat 64 = Int64.modulus). {
    rewrite two_power_nat_two_p. replace (Z.of_nat 64) with Int64.zwordsize. rewrite <-Int64.modulus_power. reflexivity. now cbn. }
  assert (Htpn' : two_power_nat 64 = (2^64)%Z) by now rewrite int64_modulus_eq_pow64 in Htpn.
  
  induction t; intros.
  symmetry in H0.
  apply rev_move in H0. unfold rev in H0. replace (catrev [i] []) with [i] in H0 by now cbn.
  assert (0 <= i < Z.of_nat 64)%Z. eapply Zbits.Z_one_bits_range with (x:=x); eauto.  
  rewrite H0. cbn. left; auto.
  assert (x = Zbits.powerserie (Zbits.Z_one_bits 64 x 0)).
  assert (0 <= x < 2^64)%Z.
  rewrite Htpn' in H. auto.


  apply Zbits.Z_one_bits_powerserie. lia.
  rewrite H0 in H2. cbn in H2.
  rewrite two_p_equiv in H2. replace x with (2^i)%Z by lia.
  rewrite Z.pow_add_r. lia. lia. lia.
  remember 64 as n. destruct n. cbn in H0. discriminate. cbn in H0. 
  have Hodd := Zdiv2_odd_eqn x.
  destruct (Z.odd x) eqn:Hxodd.  
  assert (Z.div2 x = (x - 1) / 2)%Z by lia.
  
  
  assert (0 <= i < Z.of_nat 64)%Z. eapply Zbits.Z_one_bits_range with (x:=x); eauto.  
  rewrite H0. cbn. left; auto. lia. lia.
  assert (Z.of_nat 64 = 64%Z). lia. rewrite H3 in H2. 
  rewrite H1.

 lia. lia. lia. 
  rewrite 
  rewrite two_p_equiv in H3. rewrite two_p_equiv in H3.
  unfold Zbits.powerserie in H3.
  fold Zbits.powerserie in H3.
  rewrite two_p_equiv in H3. rewrite two_p_equiv in H3.
  rewrite  Htpn' in H.
  assert (forall j, In j t -> 0 <= j)%Z.
    intros.
    assert (In j (Zbits.Z_one_bits 64 x 0))%Z. {

  cbn in H0.
  have Hodd := Zdiv2_odd_eqn x.
  destruct (Z.odd x) eqn:Hxodd.  
  assert (Z.div2 x = (x - 1) / 2)%Z by lia.
  assert (rev (i :: t) = j%Z :: (Zbits.Z_one_bits n (Z.div2 x) (j + 1))). {
    symmetry in H0.
    apply rev_move in H0. auto. 
    
}
replace (j :: Zbits.Z_one_bits n (Z.div2 x) (j + 1)) with ([j] ++ Zbits.Z_one_bits n (Z.div2 x) (j + 1)) in H0.
2: { rewrite cat1s. reflexivity.}
rewrite rev_cat in H0. replace (rev [j]) with [j] in H0 by now unfold rev.
assert (rev (i :: t) = rev t ++ [i])%Z. rewrite <-cat1s. rewrite rev_cat. now unfold rev.
assert (t = Zbits.Z_one_bits n (Z.div2 x)
unfold rev in H0. cbn in H0. 
cbn in H0.
 rewrite rev_cat.
assert (Zbits.Z_one_bits n 
  assert (Zbits.Z_one_bits n (Z.div2 x) 0)
i :: t
           
 rewrite unfold Z.div2.
  2 * 
  assert ((x - 1)
n = (2 * Z.div2 n + (if Z.odd n then 1 else 0))%Z
  destruct (Z.odd x).  
  assert (rev (i :: t) = 0%Z :: (Zbits.Z_one_bits n (Z.div2 x) 1)). {
    symmetry in H0.
    apply rev_move in H0. auto. }
  have H' := Zbits.Z_one_bits_powerserie n.
  Search Z.div2.
 (Z.div2 x) H1.

  assert (
  
rewrite 
    unfold rev. cbn. rewrite catrevE. 
  unfold rev in H0.  cbn in H0. rewrite catrevE in H0.
  rewrite 
p
  cbn in H0.
  Search two_power_nat.
  rewrite two_power_nat_S in H.  
  assert (0<= Z.div2 x < two_power_nat n)%Z. lia.
  have H' := Zbits.Z_one_bits_powerserie n (Z.div2 x) H1.
  assert (forall l k, 
             Zbits.powerserie (l ++ [k]) = Zbits.powerserie (k :: l))%Z. {
    intro. induction l. intros. cbn. reflexivity.
    intros.
    cbn.
    assert (two_p a + Zbits.powerserie l = (Zbits.powerserie (a :: l)))%Z. now cbn.
    rewrite H2. rewrite IHl. cbn. lia. }
  assert (forall m y j,
             Zbits.powerserie (Zbits.Z_one_bits m y j) = Zbits.powerserie (rev (Zbits.Z_one_bits m y j)))%Z. {
    intro. induction m. intros. cbn. unfold Zbits.powerserie. unfold rev. now cbn.
    intros.
    cbn.
    destruct (Z.odd y).
    unfold rev.  cbn. rewrite catrevE.
    assert (two_p j0 + Zbits.powerserie (Zbits.Z_one_bits m (Z.div2 y) (j0 + 1)) = Zbits.powerserie (j0 :: (Zbits.Z_one_bits m (Z.div2 y) (j0 + 1))))%Z. now cbn.
    rewrite H3.
    rewrite H2. cbn. now rewrite IHm.  apply IHm. }
  cbn in H0.
  assert (
  have IH := IHn t (Z.div2 x) i (j + 1)%Z H1 H0.
  assert (forall n l z j, (0 <= z < two_power_nat n)%Z -> j :: l = Zbits.Z_one_bits n z 0 -> l = Zbits.Z_one_bits 64 (z - 2^j) 0).  {

  
  
  assert (forall m y, 
             Zbits.powerserie 
  (* assert (x = Zbits.powerserie (Zbits.Z_one_bits 64 x 0)). *)
  
  (* assert (0 < x < 2^n)%Z. *)
  (* rewrite Htpn' in H. auto. *)
  apply Zbits.Z_one_bits_powerserie. lia. 
  rewrite <-H0 in H1.
  cbn in H1.

  replace (two_p i + 0)%Z with (2^i)%Z in H1.

unfold two_power_nat in H.
  (* assert (x = Zbits.powerserie (Zbits.Z_one_bits 64 x 0)). *)
  
  (* assert (0 < x < 2^n)%Z. *)
  (* rewrite Htpn' in H. auto. *)
  apply Zbits.Z_one_bits_powerserie. lia. 
  rewrite <-H0 in H1.
  cbn in H1.
  replace (two_p i + 0)%Z with (2^i)%Z in H1.
  assert (0 <= i < Z.of_nat 64)%Z. eapply Zbits.Z_one_bits_range with (x:=x); eauto.
  rewrite <-H0. cbn. left; auto.
  assert (Z.of_nat 64 = 64%Z). lia. rewrite H3 in H2. 
  rewrite H1.
  rewrite H1 in H. rewrite Htpn' in H.
  assert (2^(i + 1) = 2^i * 2)%Z. rewrite Z.pow_add_r. lia. lia. lia. 
  rewrite H4. lia.
  rewrite two_p_equiv. lia.
  assert (0 <= i < Z.of_nat 64)%Z. eapply Zbits.Z_one_bits_range with (x:=x); eauto.
  rewrite <-H0. unfold In. left; auto.
  assert (0 <= a < Z.of_nat 64)%Z. eapply Zbits.Z_one_bits_range with (x:=x); eauto.
  rewrite <-H0. unfold In. right; left; auto.
  assert (x = Zbits.powerserie (Zbits.Z_one_bits 64 x 0)).
  assert (0 < x < 2^64)%Z.
  rewrite Htpn' in H. auto.
  apply Zbits.Z_one_bits_powerserie. lia. 
  rewrite <-H0 in H3.
  unfold Zbits.powerserie in H3.
  fold Zbits.powerserie in H3.
  rewrite two_p_equiv in H3. rewrite two_p_equiv in H3.
  rewrite  Htpn' in H.
  assert (forall j, In j t -> 0 <= j)%Z.
    intros.
    assert (In j (Zbits.Z_one_bits 64 x 0))%Z. {
      rewrite <-H0.
      unfold In. unfold In in H4.
      right;right;auto. }
    have H' := Zbits.Z_one_bits_range.
    specialize (H' 64 x j H5). lia. 
  have H' := powserie_nonneg t H4.
  remember (x - 2^i)%Z as y.
  assert (y = (2 ^ a + Zbits.powerserie t))%Z. lia.
  assert (y < x)%Z. lia.
  assert (y < 2^64)%Z. lia.
  assert (0 < y)%Z. 
  subst y. rewrite H3. lia.
  assert (0 < 2^a)%Z. lia.
  assert (0 < y)%Z. lia.
  assert (0 < y < 2^64)%Z. lia.
  have H'' := IHt y a H11.
  assert (forall n l z j, (0 <= z < two_power_nat n)%Z -> j :: l = Zbits.Z_one_bits n z 0 -> l = Zbits.Z_one_bits 64 (z - 2^j) 0).  {
    induction n; intros; auto.
    cbn in H13. discriminate.
    unfold Zbits.Z_one_bits in H13.
    destruct (Z.odd z).
    fold Zbits.Z_one_bits in H13.
    
      assert (z = Zbits.powerserie (Zbits.Z_one_bits 64 z 0)).
      assert (0 < z < 2^64)%Z.
      rewrite Htpn' in H12. auto.
      apply Zbits.Z_one_bits_powerserie. lia. 
      rewrite <-H13 in H14. 
      unfold Zbits.powerserie in H14.
      (* fold Zbits.powerserie in H3. *)
      rewrite two_p_equiv in H14.
      rewrite  Htpn' in H12.
      rewrite H14.
      replace (2^j + 0 - 2^j)%Z with 0%Z. now cbn.
      lia.
      assert (forall j', In j' l -> 0 <= j')%Z.
      intros.
      assert (In j' (Zbits.Z_one_bits 64 z 0))%Z. {
        rewrite <-H13.
        unfold In. unfold In in H14.
        right;right;auto. }
      have Hr := Zbits.Z_one_bits_range.
      specialize (Hr 64 z j' H15). lia. 
      have Hr' := powserie_nonneg l H14.
      assert (z - 2^j  = (2 ^ a0 + Zbits.powerserie l))%Z.
      assert (z = Zbits.powerserie (Zbits.Z_one_bits 64 z 0)).
      assert (0 < z < 2^64)%Z.
      rewrite Htpn' in H12. auto.
      apply Zbits.Z_one_bits_powerserie. lia. 
      rewrite <-H13 in H15. 
      unfold Zbits.powerserie in H15.
      (* fold Zbits.powerserie in H3. *)
      rewrite two_p_equiv in H15. rewrite two_p_equiv in H15.
      rewrite  Htpn' in H12.
      fold Zbits.powerserie in H15.
      rewrite H15.
      lia.
      assert (0 <= (z - 2^j) < 2^64)%Z. lia. 
      rewrite <-Htpn' in H16.
      have Hj := Zbits.Z_one_bits_powerserie 64 (z - 2^j)%Z H16.
      assert (z - 2^j = Zbits.powerserie (a0 :: l))%Z. unfold Zbits.powerserie. fold Zbits.powerserie. rewrite two_p_equiv. auto.
      rewrite Hj in H17. 
      destruct (Zbits.Z_one_bits 64 (z - 2^j)%Z 0). cbn in H17. rewrite two_p_equiv in H17. 
      About f_equal.
      assert (
      remember 64 as n.
      unfold Zbits.Z_one_bits. 
      inv H17.
apply f_equal in H17.
      auto
      f_equal.
      apply f_equal in Hj.
      assert (a0 = z - Z.
      rewrite H15.
      replace (2^j + 0 - 2^j)%Z with 0%Z. now cbn.

 rewrite 
        
lia.
      assert (y < x)%Z. lia.
      assert (y < 2^64)%Z. lia.
      assert (0 < y)%Z. 
      subst y. rewrite H3. lia.
      assert (0 < 2^a)%Z. lia.
      assert (0 < y)%Z. lia.
      assert (0 < y < 2^64)%Z. lia.

      assert (
      have Ha0 := IHl (


    
    intros.
             
a :: t = Zbits.Z_one_bits 64 y 0)%Z.
  
  unfold Zbits.Z_one_bits.

  asser
             
  
  assert (Zbits.powerserie
  assert (0 <= y < two_power_nat 64)%Z. rewrite Htpn'.

  transitivity x.
  subst y
  
  remember ((2 ^ a + Zbits.powerserie t)%Z)

  remember 
  rew

  rewrite <-H0 in H1.
  unfold Zbits.powerserie in H1.
  cbn in H1.
  replace (two_p i + 0)%Z with (2^i)%Z in H1.
  assert (0 <= i < Z.of_nat 64)%Z. eapply Zbits.Z_one_bits_range with (x:=x); eauto.

  


  rewrite Z.pow_add


2^64
2^(63 - i) * x < 2^(64 - i)



< 2^(64 - i + 1)
2^(i - 1)
2^((63 - i) - 1
 

  assert (0 <= i < 64)%Z. 
  assert (two_p i + 0
  assert (

  
  
    (i \in (Zbits.Z_one_bits 64 x 0)) ->
    (2^i <= x < two_power_nat 64)%Z.
    


63 <= 2^i * x

              
2^i * x < 2^(64-(63-i)) * x
2^(63-i) * x < 2^(1 + i)


  


Lemma in_Z_one_bits : forall x i,
    (0 < x < two_power_nat 64)%Z -> (* < two_power_nat n)%Z -> *)
    (i \in (Zbits.Z_one_bits 64 x 0)) ->
    (2^i <= x < two_power_nat 64)%Z.
Proof.
  intros x i Hx Hi.
  assert (Hi' : (i \in (Zbits.Z_one_bits 64 x 0)) = true) by auto.
  assert (forall j, In j (Zbits.Z_one_bits 64 x 0) -> 0 <= j)%Z. {
    intros j Hj. 
    have H := Zbits.Z_one_bits_range _ _ _ Hj; lia. }
  assert (Hx': (0 <= x < two_power_nat 64)%Z) by lia.
  have Hpow := Zbits.Z_one_bits_powerserie 64 x Hx'. 
  assert (2^i <= x)%Z. {
    rewrite Hpow.
    apply in_Z_one_bits_pow; auto. }
  lia.
Qed.

(* Lemma not_in_Z_one_bits_pow : forall l i, *)
(*     (0 <= i < 64)%Z -> *)
(*     0 < length l -> *)
(*     (forall x, In x l -> 0 <= x < i)%Z -> *)
(*     (2^(63 - i) <= Zbits.powerserie l < 2^(64-i))%Z. *)
(* Proof. *)
(*   induction l; intros. cbn in H0. lia. *)
(*   unfold Zbits.powerserie. *)
(*   fold Zbits.powerserie. *)
(*   rename a into j. *)
(*   replace (two_p j) with (2^j)%Z. *)
(*   assert (0 <= j < i)%Z. apply H1. now constructor. *)

(*   apply H1 in H0. lia. *)
(*   Search two_p. *)
(*   now rewrite two_p_equiv. *)
(* Qed. *)
(*   rewrite Z.two_p_correct. *)
(*   assert (2^a < 2^i)%Z. admit.   *)
(*   replace (two_p a) with (2^a)%Z. *)
(*   assert (Zbits.powerserie l < 2^(64 - i))%Z. apply IHl. lia. intros. apply H0. right. assumption. *)
  
(*   Search Z.log2. *)
  
  
(*   apply IHl with (i:=a). *)
(*   unfold  *)
(*   discriminate. *)
(*   unfold Zbits.powerserie. *)
(*   destruct (Z.eq_dec i a). *)
(*   fold Zbits.powerserie.   *)
(*   rewrite <-e. *)
(*   rewrite two_p_equiv. *)
(*   assert (0 <= Zbits.powerserie l)%Z. apply powserie_nonneg; auto. *)
(*   assert (forall x, In x l -> 0 <= x)%Z. *)
(*   intros. *)
(*   assert (In x (a :: l)). right. assumption. *)
(*   now apply H0. *)
(*   assumption. *)
(*   lia. *)
(*   fold Zbits.powerserie. *)
(*   assert (i \in l). *)
(*   have H' := in_cons a l i. *)
(*   have Hrefl := reflect_iff. *)
(*   have H''' := eqP. *)
(*   specialize (H''' _ i a). *)
(*   specialize (Hrefl _ _ H'''). *)
(*   destruct Hrefl. *)
(*   destruct (i == a)%Z eqn:Heqb. specialize (H2 Logic.eq_refl). contradiction.   *)
(*   rewrite orb_false_l in H'. auto. *)
(*   rewrite <-H'. assumption. *)
(*   assert (forall x, In x l -> 0 <= x)%Z. *)
(*   intros. *)
(*   assert (In x (a :: l)). right. assumption. *)
(*   now apply H0. *)
(*   assert (0 <= a)%Z. apply H0; auto. now constructor.  *)
(*   have Htwop := two_p_gt_ZERO a H3. *)
(*   assert (2 ^i <= Zbits.powerserie l)%Z. apply IHl; auto. lia. *)
(* Qed. *)


(* Lemma not_in_Z_one_bits : forall x i, *)
(*     (0 < x < two_power_nat 64)%Z -> *)
(*     (0 <= i < 64)%Z ->  *)
(*     (forall j, (i <= j < 64)%Z -> ~ (In j (Zbits.Z_one_bits 64 x 0))) -> *)
(*     (x < 2^(64-i))%Z. *)
(* Proof. *)
(*   intros x i Hx Hi Hj. *)
(*   assert (Hi' : ~ (In i (Zbits.Z_one_bits 64 x 0))). *)
(*   apply Hj. lia. *)
(*   assert  *)
(*   assert (forall j, In j (Zbits.Z_one_bits 64 x 0) -> 0 <= j)%Z. { *)
(*     intros j Hj.  *)
(*     have H := Zbits.Z_one_bits_range _ _ _ Hj; lia. } *)
(*   assert (Hx': (0 <= x < two_power_nat 64)%Z) by lia. *)
(*   have Hpow := Zbits.Z_one_bits_powerserie 64 x Hx'.  *)
(*   assert (2^i <= x)%Z. { *)
(*     rewrite Hpow. *)
(*     apply in_Z_one_bits_pow; auto. } *)
(*   lia. *)
(* Qed. *)

Lemma clz_spec : forall x i,
    (0 < x < Int64.modulus)%Z ->
    i = Int64.unsigned (Int64.clz (Int64.repr x)) ->
    (* (i = 63 - Z.log2 x)%Z. *)
    (2^63 <= 2^i * x < 2^64)%Z.
Proof.
  intros x i Hx Hi.
  assert (Hws: Int64.wordsize = 64) by (unfold Int64.wordsize, Integers.Wordsize_64.wordsize; reflexivity).
  assert (Htpn: two_power_nat 64 = Int64.modulus). {
    rewrite two_power_nat_two_p. replace (Z.of_nat 64) with Int64.zwordsize. rewrite <-Int64.modulus_power. reflexivity. now cbn. }
  assert (Htpn' : two_power_nat 64 = (2^64)%Z) by now rewrite int64_modulus_eq_pow64 in Htpn.
  assert (Int64.intval x = x)%Z. {
    cbn. rewrite Int64.Z_mod_modulus_id; auto; lia. }
  assert (0 < i < 64)%Z. admit.
 
  assert (Hi' : (63 - i)%Z \in (Zbits.Z_one_bits 64 x 0)). {    
    unfold Int64.clz in Hi.    
    have: (has (fun b => b == true) (Int64.convert_to_bits (Int64.repr x))).
    rewrite has_find. rewrite Int64.power_index_to_bits_size. 
    rewrite Hws. Search (Int64.unsigned _ = _). rewrite lt_pow64_unsigned_id in Hi; auto.
    assert (S (find (fun b : bool_eqType => b == true) (Int64.convert_to_bits (Z_to_i64 x))) <= 64). lia.
    have Hrefl := ssrnat.leP.
    have Hrefl' := reflect_iff _ _ (Hrefl (S (find (fun b : bool_eqType => b == true) (Int64.convert_to_bits (Z_to_i64 x)))) 64).
    rewrite Hrefl' in H1. auto.
    have Hsize := Int64.convert_to_bits_size (Int64.repr x). rewrite Hws in Hsize.
    have Hfind_size := find_size (fun b : bool_eqType => b == true) (Int64.convert_to_bits (Z_to_i64 x)). 
    assert (0 <= find (fun b : bool_eqType => b == true) (Int64.convert_to_bits (Z_to_i64 x))).
    unfold find. destruct (Int64.convert_to_bits (Z_to_i64 x)); lia.
    rewrite Hsize in Hfind_size.
    have Hfd := (ssrnat.leP Hfind_size). lia.
    intro.
    assert (Z.of_nat (Int64.wordsize - (Z.to_nat i) - 1) \in Zbits.Z_one_bits Int64.wordsize (Int64.intval x) 0).
    assert (seq.nth false (Int64.convert_to_bits (Int64.repr x)) (Z.to_nat i) = true).  (* = (64 - (Z.to_nat i) - 1)%Z \in (Zbits.Z_one_bits 64 x 0)). { *)

    apply nth_find with (x0:=false) (a:=(fun b : bool_eqType => b == true)) (s:=(Int64.convert_to_bits (Z_to_i64 x))) in H1.
    rewrite lt_pow64_unsigned_id in Hi; auto.
    rewrite Hi.
    rewrite Nat2Z.id. auto.
    unfold is_true in H1.
    auto.
    have HeqP := eqP H1.
    auto.
    have Hsize := Int64.convert_to_bits_size (Int64.repr x). rewrite Hws in Hsize.
    have Hfind_size := find_size (fun b : bool_eqType => b == true) (Int64.convert_to_bits (Z_to_i64 x)). 
    assert (0 <= find (fun b : bool_eqType => b == true) (Int64.convert_to_bits (Z_to_i64 x))).
    unfold find. destruct (Int64.convert_to_bits (Z_to_i64 x)); lia.
    rewrite Hsize in Hfind_size.
    have Hfd := (ssrnat.leP Hfind_size). lia.
    assert (ssrnat.subn (ssrnat.subn Int64.wordsize (Z.to_nat i)) 1 = Int64.wordsize - Z.to_nat i - 1) by auto.
    rewrite <-H3.
    rewrite Int64.convert_to_bits_nth in H2.
    rewrite H.
    replace (Int64.intval (Int64.repr x)) with x in H2.
    auto.
    rewrite Hws.
    assert (S (Z.to_nat i) <= 64) by lia.    
    now eapply (introT ssrnat.leP) in H2.
    rewrite Hws in H2.
    replace (64 - Z.to_nat i - 1) with (63 - Z.to_nat i) in H2 by lia.
    replace (Z.of_nat (63 - Z.to_nat i)) with (63 - i)%Z in H2 by lia.
    rewrite H in H2. assumption. }
  assert (0 < x < two_power_nat 64)%Z by auto.
  have Hbounds := in_Z_one_bits x (63 - i)%Z H1 Hi'.
  rewrite Htpn' in Hbounds.
  clear H1.
  split.
  destruct Hbounds.
  assert (2^(63 - i) = 2^63/2^i)%Z.
  rewrite Z.pow_sub_r; lia.
  assert ((2^i * x) / 2^i = x)%Z.
  rewrite Z.mul_comm. rewrite Z_div_mult. reflexivity.
  lia.
  (* rewrite <- H4 in H1. *)
  (* rewrite H3 in H1. *)
  assert ((2^(63-i)) * 2^i = 2^63)%Z. 

assert (63 = (63 - i) + i)%Z. lia.
assert (2^63 = 2^((63 - i) + i))%Z. pattern (2^63-i + i)%Z. rewrite <- H5. reflexivity.
rewrite H6.

rewrite <-Z.pow_add_r. reflexivity. lia. lia.
rewrite Z.mul_comm.
rewrite <-H5.
apply Zmult_le_compat. assumption. lia. lia. lia. 
destruct Hbounds. 
assert (2^(63 - i) < 2^64)%Z. lia.
assert (2^i * x < 2^i * 2^64)%Z. nia.
assert (2^64 < 2^i * 2^64)%Z.
assert (1 < 2^i)%Z.
assert (0 < i)%Z by lia.
assert (1 <= i)%Z by lia.
assert (1 < 2^1)%Z by lia.
Search Z.pow.
apply Zpow_facts.Zpower_gt_1.
lia.
lia. lia.
assert (2^64 = 2^i * 2^(64 - i))%Z. 
rewrite <-Z.pow_add_r. 
replace (i + (64 - i))%Z with 64%Z by lia. reflexivity.
lia. lia. 
assert (Z.log2 x < 64)%Z.
apply Z.log2_lt_pow2. lia. lia. 
assert (0 <= Z.log2 x)%Z.
apply Z.log2_nonneg.
assert (0 <= Z.log2 x < Z.of_nat 64)%Z. lia.
assert (Zbits.Z_one_bits 64 (two_p (Z.log2 x)) i = [(i + Z.log2 x)%Z]). {
  apply Zbits.Z_one_bits_two_p. lia. }
    assert (forall n x i j,
               In j (Zbits.Z_one_bits n x i) -> (i <= j < i + Z.of_nat n)%Z).
  {
  induction n; simpl In.
  tauto.
  intros x0 i0 j0. rewrite Nat2Z.inj_succ.
  assert (In j0 (Zbits.Z_one_bits n (Z.div2 x0) (i0 + 1)) -> (i0 <= j0 < i0 + Z.succ (Z.of_nat n))%Z).
    intros. exploit IHn; eauto. lia.
  destruct (Z.odd x0); simpl.
  intros [A|B]. subst j0. lia. auto.
  auto.
  }

assert (In (i + Z.log2 x)%Z (Zbits.Z_one_bits 64 (two_p (Z.log2 x)) i))%Z. {
  unfold In.
  destruct (Zbits.Z_one_bits 64 (two_p (Z.log2 x)) i)%Z. discriminate.
  left. congruence. }
  apply H11 in H12.
assert (Z.log2 x < i + Z.log2 x)%Z. {
lia. }
assert (In (i + Z.log2 x)%Z (Zbits.Z_one_bits 64 (two_p (Z.log2 x)) 0))%Z. {
  unfold In.
  Search (2 ^ (Z.log2 _))%Z.
  destruct (Zbits.Z_one_bits 64 (two_p (Z.log2 x)) i)%Z. discriminate.
  left. congruence. }
  apply H11 in H12.
assert (Z.log2 x < i + Z.log2 x)%Z. {
lia. }

assert (Zbits.Z_one_bits

  
  simpl.
  cbn.
  Search In.
  apply in_eq.
  have H11' := H11 64 ((two_p (Z.log2 x))) i (i + Z.log2 x)%Z.
  constructor
assert (i <= i + Z.log2 < i + 
  assert (x = two_p (Z.log2 x)). {
    Search two_p.
Search Z.pow.
Search Z.log2.
  
About Z.log2_le_mono.
Search (Z.log2 _ < Z.log2 _)%Z.
Search Z.pow.
assert (Z.log2 (2^64) = 64)%Z. 
Search Z.pow.
rewrite Z.log2_pow2. lia. lia.
Search (Z.log2 _ < _)%Z.


  assert (Hlog1: (Z.log2 (2^63) <= Z.log2 (2 ^ (Int64.unsigned (Int64.clz (Int64.repr x))) * x))%Z) by (apply Z.log2_le_mono; assumption).    
  assert (Hlog2: (Z.log2 (2 ^ (Int64.unsigned (Int64.clz (Int64.repr x))) * x) < 64)%Z) by (apply Z.log2_lt_pow2; lia).
  replace (2 ^ (Int64.unsigned (Int64.clz (Int64.repr x))) * x)%Z with (x * 2 ^ (Int64.unsigned (Int64.clz (Int64.repr x))))%Z in Hlog1, Hlog2 by lia.
 
Sear
assert (i + Z.log2 x < 64)%Z. {

assert (2^i * x < 2^i * 2^64)%Z. lia.
destruct (Z_lt_dec (2^i * x) (2^64))%Z. assumption.
have Hnot := Znot_lt_ge.
specialize (Hnot _ _ n). 
assert (2^64 <= 2^i * x)%Z by lia.
assert (2^(64 - i) < 2^64)%Z. by lia.
replace (2 ^ i * 2 ^ 64)%Z with (2 ^ 64 * 2^i)%Z in H4 by now (rewrite Z.mul_comm). 
rewrite <-Z.pow_add_r in H4.
2^i (2^0 + 2^ + ... ) + 2^i * 

Zbits.Z_one_bits 64 x 0 = i :: l

log2 x
log2 x + i < 64
2^i * x < 2^64




x = 2^i * 
*)

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
  rewrite Ha in Hinbits'. About rwP. rewrite eqb_id in Hinbits'.  
  have Hsize' := find_size a s. rewrite (rwP ssrnat.leP) in Hfindleq.
  assert (forall k, In k (Zbits.Z_one_bits Int64.wordsize (Int64.intval x) 0) -> 0 <= k)%Z. {
    intros k Hk. 
    have Hk' := Zbits.Z_one_bits_range _ _ _ Hk; lia. }
  assert (Hx'': (0 <= (Int64.intval x) < two_power_nat Int64.wordsize)%Z).
  rewrite two_power_nat_equiv. unfold Int64.wordsize, Integers.Wordsize_64.wordsize. rewrite int64_modulus_eq_pow64 in Hrange. lia. 
  have Hpow := Zbits.Z_one_bits_powerserie 64 (Int64.intval x) Hx''. 
  rewrite two_power_nat_equiv.
  rewrite Hx'. rewrite Hpow.
  About in_Z_one_bits_pow.
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
(* unfold Int64.clz in Hi. *)
have Hclz_last := clz_last.
(* assert (HiRange : (0 <= i < Int64.wordsize)%Z). *)
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
Search (_ <= _)%nat.
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
Search Int64.intval.
apply Int64.eq_T_intval in H1.
rewrite <-H1. simpl. now rewrite Hi.
apply Int64.repr_inv in H1. lia. lia. lia.
assert (Z.to_nat i < Int64.wordsize). lia.
specialize (Hclz_last (Int64.repr x) (Z.to_nat i) H0).
rewrite <-Hi in Hclz_last. specialize (Hclz_last Logic.eq_refl).
replace (Int64.intval (Z_to_i64 x)) with x in Hclz_last. 2: simpl; rewrite Int64.Z_mod_modulus_id; lia.
rewrite Nat2Z.inj_sub in Hclz_last. 2: lia.
Search (Z.of_nat (Z.to_nat _)). 
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
    Int64.unsigned (Int64.clz (Int64.repr x)) = (63 - Z.log2 (Int64.unsigned (Int64.repr x)))%Z.
Proof.
  intros.
  rewrite Int64.unsigned_repr. 2: cbn; replace Int64.modulus with (2^64)%Z in H; auto; lia.
  have H' := clz_spec _ H.
  destruct H' as [Hle1 Hle2].
  have H' := Int64.unsigned_range (Int64.clz (Int64.repr x)).
  assert (Hlog1: (Z.log2 (2^63) <= Z.log2 (2 ^ (Int64.unsigned (Int64.clz (Int64.repr x))) * x))%Z) by (apply Z.log2_le_mono; assumption).    
  assert (Hlog2: (Z.log2 (2 ^ (Int64.unsigned (Int64.clz (Int64.repr x))) * x) < 64)%Z) by (apply Z.log2_lt_pow2; lia).
  replace (2 ^ (Int64.unsigned (Int64.clz (Int64.repr x))) * x)%Z with (x * 2 ^ (Int64.unsigned (Int64.clz (Int64.repr x))))%Z in Hlog1, Hlog2 by lia.
  rewrite Z.log2_mul_pow2 in Hlog1, Hlog2; [|lia|lia].
  replace (Z.log2 (2 ^ 63)) with 63%Z in Hlog1 by (rewrite Z.log2_pow2; lia).
  lia.
Qed.

Lemma head0_int64_clz : forall x,
    (0 < to_Z x)%Z ->  
    to_Z (head0 x) = (Int64.unsigned (Int64.clz (Int64.repr (to_Z x))) - 1)%Z.
Proof.
  intros.
  rewrite clz_spec_alt.
  replace (63 - Z.log2 (Int64.unsigned (Z_to_i64 φ (x)%uint63)) - 1)%Z with (62 - Z.log2 (Int64.unsigned (Z_to_i64 φ (x)%uint63)))%Z by lia.
  rewrite uint63_unsigned_id.
  rewrite head0_spec_alt; auto.
Qed.

Lemma head0_int64_clz : forall x,
    (0 < to_Z x)%Z ->  
    to_Z (head0 x) = (Int64.unsigned (Int64.clz (Int64.repr (to_Z x))) - 1)%Z.
Proof.
  intros.
  rewrite clz_spec_alt.
  replace (63 - Z.log2 (Int64.unsigned (Z_to_i64 φ (x)%uint63)) - 1)%Z with (62 - Z.log2 (Int64.unsigned (Z_to_i64 φ (x)%uint63)))%Z by lia.



End CORRECTNESS.
