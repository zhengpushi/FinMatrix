
type __ = Obj.t

val negb : bool -> bool

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



val pred : int -> int

val add : int -> int -> int

val sub : int -> int -> int

val even : int -> bool

val odd : int -> bool

type reflect =
| ReflectT
| ReflectF

module Nat :
 sig
  val add : int -> int -> int

  val mul : int -> int -> int

  val ltb : int -> int -> bool

  val even : int -> bool

  val pow : int -> int -> int
 end

val nth : int -> 'a1 list -> 'a1 -> 'a1

val concat : 'a1 list list -> 'a1 list

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

val seq : int -> int -> int list

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos :
 sig
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
 end

module Coq_Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : positive -> mask

  val sub_mask : positive -> positive -> mask

  val sub_mask_carry : positive -> positive -> mask

  val sub : positive -> positive -> positive

  val mul : positive -> positive -> positive

  val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1

  val pow : positive -> positive -> positive

  val size_nat : positive -> int

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val ggcdn : int -> positive -> positive -> positive * (positive * positive)

  val ggcd : positive -> positive -> positive * (positive * positive)

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> int

  val of_nat : int -> positive

  val of_succ_nat : int -> positive
 end

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val sub : z -> z -> z

  val mul : z -> z -> z

  val compare : z -> z -> comparison

  val sgn : z -> z

  val leb : z -> z -> bool

  val ltb : z -> z -> bool

  val max : z -> z -> z

  val min : z -> z -> z

  val abs : z -> z

  val to_nat : z -> int

  val of_nat : int -> z

  val to_pos : z -> positive

  val pos_div_eucl : positive -> z -> z * z

  val div_eucl : z -> z -> z * z

  val div : z -> z -> z

  val ggcd : z -> z -> z * (z * z)
 end

type q = { qnum : z; qden : positive }

type cReal = { seq0 : (z -> q); scale : z }

type dReal = (q -> bool)

module type RbaseSymbolsSig =
 sig
  type coq_R

  val coq_Rabst : cReal -> coq_R

  val coq_Rrepr : coq_R -> cReal

  val coq_R0 : coq_R

  val coq_R1 : coq_R

  val coq_Rplus : coq_R -> coq_R -> coq_R

  val coq_Rmult : coq_R -> coq_R -> coq_R

  val coq_Ropp : coq_R -> coq_R
 end

module RbaseSymbolsImpl :
 RbaseSymbolsSig

val iPR_2 : positive -> RbaseSymbolsImpl.coq_R

val iPR : positive -> RbaseSymbolsImpl.coq_R

val iZR : z -> RbaseSymbolsImpl.coq_R

val total_order_T :
  RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool option

module type RinvSig =
 sig
  val coq_Rinv : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R
 end

module RinvImpl :
 RinvSig

val req_dec_T : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool

val rlt_dec : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool

val rle_dec : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool

val rlt_le_dec : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool

val rle_lt_dec : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool

val id : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R

val sqrt : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R

type 'a dec =
  'a -> 'a -> bool
  (* singleton inductive, whose constructor was Build_Dec *)

val aeqdec : 'a1 dec -> 'a1 -> 'a1 -> bool

val acmpb : 'a1 dec -> 'a1 -> 'a1 -> bool

type 'a order = { lt_cases : ('a -> 'a -> bool option);
                  ltb_reflect : ('a -> 'a -> reflect);
                  leb_reflect : ('a -> 'a -> reflect) }

type 'a orderedARing =
  'a order
  (* singleton inductive, whose constructor was Build_OrderedARing *)

type 'a orderedField =
  'a orderedARing
  (* singleton inductive, whose constructor was Build_OrderedField *)

type 'a convertToR =
  'a order
  (* singleton inductive, whose constructor was Build_ConvertToR *)

val r_eq_Dec : RbaseSymbolsImpl.coq_R dec

val r_le_Dec : RbaseSymbolsImpl.coq_R dec

val r_lt_Dec : RbaseSymbolsImpl.coq_R dec

val rleb : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool

val rltb : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool

val rltb_reflect : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> reflect

val rleb_reflect : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> reflect

val r_Order : RbaseSymbolsImpl.coq_R order

val r_ConvertToR : RbaseSymbolsImpl.coq_R convertToR

val nat_eq_Dec : int dec

val nat_lt_Dec : int dec

type fin = int
  (* singleton inductive, whose constructor was Fin *)

val fin2nat : int -> fin -> int

val fin0 : int -> fin

val nat2finS : int -> int -> fin

val nat2fin : int -> int -> fin

val fin2SuccRange : int -> fin -> fin

val fin2PredRange : int -> fin -> fin

val fin2AddRangeR : int -> int -> fin -> fin

val fin2AddRangeR' : int -> int -> fin -> fin

val fin2AddRangeAddL : int -> int -> fin -> fin

val fin2AddRangeAddL' : int -> int -> fin -> fin

val fin2PredRangePred : int -> fin -> fin

val fin2SuccRangeSucc : int -> fin -> fin

val finseq : int -> fin list

val seqfoldl : (int -> 'a1) -> int -> 'a2 -> ('a2 -> 'a1 -> 'a2) -> 'a2

val seqfoldr : (int -> 'a1) -> int -> 'a2 -> ('a1 -> 'a2 -> 'a2) -> 'a2

val seqsumAux : ('a1 -> 'a1 -> 'a1) -> int -> (int -> 'a1) -> 'a1 -> 'a1

val seqsum : ('a1 -> 'a1 -> 'a1) -> 'a1 -> int -> (int -> 'a1) -> 'a1

val seqprodAux : ('a1 -> 'a1 -> 'a1) -> int -> (int -> 'a1) -> 'a1 -> 'a1

val seqprod : ('a1 -> 'a1 -> 'a1) -> 'a1 -> int -> (int -> 'a1) -> 'a1

module Coq__2 : sig
 type 'a vec = fin -> 'a
end
include module type of struct include Coq__2 end

val veq_dec : int -> 'a1 dec -> 'a1 vec dec

val vrepeat : int -> 'a1 -> 'a1 vec

val vzero : 'a1 -> int -> 'a1 vec

val f2v : int -> (int -> 'a1) -> 'a1 vec

val v2f : 'a1 -> int -> 'a1 vec -> int -> 'a1

val l2v : 'a1 -> int -> 'a1 list -> 'a1 vec

val v2l : int -> 'a1 vec -> 'a1 list

val mkvec1 : 'a1 -> 'a1 -> 'a1 vec

val mkvec2 : 'a1 -> 'a1 -> 'a1 -> 'a1 vec

val mkvec3 : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 vec

val mkvec4 : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 vec

val vmap : ('a1 -> 'a2) -> int -> 'a1 vec -> 'a2 vec

val vmap2 : ('a1 -> 'a2 -> 'a3) -> int -> 'a1 vec -> 'a2 vec -> 'a3 vec

val veye : 'a1 -> 'a1 -> int -> fin -> 'a1 vec

val veyes : 'a1 -> 'a1 -> int -> 'a1 vec vec

val vhead : int -> 'a1 vec -> 'a1

val vtail : int -> 'a1 vec -> 'a1

val vheadN : int -> int -> 'a1 vec -> 'a1 vec

val vtailN : int -> int -> 'a1 vec -> 'a1 vec

val vset : int -> 'a1 vec -> fin -> 'a1 -> 'a1 vec

val vswap : int -> 'a1 vec -> fin -> fin -> 'a1 vec

val vinsert : int -> 'a1 vec -> fin -> 'a1 -> 'a1 vec

val vremove : int -> 'a1 vec -> fin -> 'a1 vec

val vremoveH : int -> 'a1 vec -> 'a1 vec

val vremoveT : int -> 'a1 vec -> 'a1 vec

val vremoveHN : int -> int -> 'a1 vec -> 'a1 vec

val vremoveTN : int -> int -> 'a1 vec -> 'a1 vec

val vconsH : int -> 'a1 -> 'a1 vec -> 'a1 vec

val vconsT : int -> 'a1 vec -> 'a1 -> 'a1 vec

val vapp : int -> int -> 'a1 vec -> 'a1 vec -> 'a1 vec

val vmem_dec : 'a1 dec -> int -> 'a1 vec -> 'a1 -> bool

val vmems_dec : 'a1 dec -> int -> int -> 'a1 vec -> 'a1 vec -> bool

val vequiv_dec : 'a1 dec -> int -> int -> 'a1 vec -> 'a1 vec -> bool

val vfoldl : 'a1 -> int -> 'a1 vec -> 'a2 -> ('a2 -> 'a1 -> 'a2) -> 'a2

val vfoldr : 'a1 -> int -> 'a1 vec -> 'a2 -> ('a1 -> 'a2 -> 'a2) -> 'a2

val vsum : ('a1 -> 'a1 -> 'a1) -> 'a1 -> int -> 'a1 vec -> 'a1

val vadd : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 vec -> 'a1 vec -> 'a1 vec

val vopp : ('a1 -> 'a1) -> int -> 'a1 vec -> 'a1 vec

val vcmul : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 -> 'a1 vec -> 'a1 vec

val vdot :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> int -> 'a1 vec -> 'a1 vec
  -> 'a1

val vlen :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 ->
  RbaseSymbolsImpl.coq_R) -> int -> 'a1 vec -> RbaseSymbolsImpl.coq_R

val vproj :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> int -> 'a1
  vec -> 'a1 vec -> 'a1 vec

val vperp :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 ->
  'a1) -> int -> 'a1 vec -> 'a1 vec -> 'a1 vec

val mrow : int -> int -> 'a1 vec vec -> fin -> 'a1 vec

val mcol : int -> int -> 'a1 vec vec -> fin -> 'a1 vec

val mtrans : int -> int -> 'a1 vec vec -> 'a1 vec vec

val mheadc : int -> int -> 'a1 vec vec -> 'a1 vec

val mtailc : int -> int -> 'a1 vec vec -> 'a1 vec

val cv2v : int -> 'a1 vec vec -> 'a1 vec

val v2cv : int -> 'a1 vec -> 'a1 vec vec

val rv2v : int -> 'a1 vec vec -> 'a1 vec

val v2rv : int -> 'a1 vec -> 'a1 vec vec

val mat0 : 'a1 -> int -> int -> 'a1 vec vec

val m2rvl : int -> int -> 'a1 vec vec -> 'a1 vec list

val rvl2m : 'a1 -> int -> int -> 'a1 vec list -> 'a1 vec vec

val m2cvl : int -> int -> 'a1 vec vec -> 'a1 vec list

val cvl2m : 'a1 -> int -> int -> 'a1 vec list -> 'a1 vec vec

val f2m : int -> int -> (int -> int -> 'a1) -> 'a1 vec vec

val m2f : 'a1 -> int -> int -> 'a1 vec vec -> int -> int -> 'a1

val m2l : int -> int -> 'a1 vec vec -> 'a1 list list

val l2m : 'a1 -> int -> int -> 'a1 list list -> 'a1 vec vec

val mappr : 'a1 -> int -> int -> int -> 'a1 vec vec -> 'a1 vec vec -> 'a1 vec vec

val mappc : 'a1 -> int -> int -> int -> 'a1 vec vec -> 'a1 vec vec -> 'a1 vec vec

val mkmat_0_c : 'a1 -> int -> 'a1 vec vec

val mkmat_r_0 : 'a1 -> int -> 'a1 vec vec

val mkmat_1_c : int -> 'a1 vec -> 'a1 vec vec

val mkmat_r_1 : int -> 'a1 vec -> 'a1 vec vec

val mkmat_1_1 : 'a1 -> 'a1 -> 'a1 vec vec

val mkmat_1_2 : 'a1 -> 'a1 -> 'a1 -> 'a1 vec vec

val mkmat_2_1 : 'a1 -> 'a1 -> 'a1 -> 'a1 vec vec

val mkmat_2_2 : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 vec vec

val mkmat_1_3 : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 vec vec

val mkmat_3_1 : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 vec vec

val mkmat_3_3 :
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 vec
  vec

val mkmat_1_4 : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 vec vec

val mkmat_4_1 : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 vec vec

val mkmat_4_4 :
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 vec vec

val mdiagMk : 'a1 -> int -> 'a1 vec -> 'a1 vec vec

val msetr : int -> int -> 'a1 vec vec -> 'a1 vec -> fin -> 'a1 vec vec

val msetc : int -> int -> 'a1 vec vec -> 'a1 vec -> fin -> 'a1 vec vec

val mremovecH : int -> int -> 'a1 vec vec -> 'a1 vec vec

val mremovecT : int -> int -> 'a1 vec vec -> 'a1 vec vec

val mconsrH : int -> int -> 'a1 vec -> 'a1 vec vec -> 'a1 vec vec

val mconsrT : int -> int -> 'a1 vec vec -> 'a1 vec -> 'a1 vec vec

val mconscH : int -> int -> 'a1 vec -> 'a1 vec vec -> 'a1 vec vec

val mconscT : int -> int -> 'a1 vec vec -> 'a1 vec -> 'a1 vec vec

val madd :
  ('a1 -> 'a1 -> 'a1) -> int -> int -> 'a1 vec vec -> 'a1 vec vec -> 'a1 vec vec

val mat1 : 'a1 -> 'a1 -> int -> 'a1 vec vec

val mtrace : ('a1 -> 'a1 -> 'a1) -> 'a1 -> int -> 'a1 vec vec -> 'a1

val mopp : ('a1 -> 'a1) -> int -> int -> 'a1 vec vec -> 'a1 vec vec

val mcmul : ('a1 -> 'a1 -> 'a1) -> int -> int -> 'a1 -> 'a1 vec vec -> 'a1 vec vec

val mmul :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> int -> int -> int -> 'a1
  vec vec -> 'a1 vec vec -> 'a1 vec vec

val mmulv :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> int -> int -> 'a1 vec vec
  -> 'a1 vec -> 'a1 vec

val mvmul :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> int -> int -> 'a1 vec ->
  'a1 vec vec -> 'a1 vec

val mrowScale :
  ('a1 -> 'a1 -> 'a1) -> int -> fin -> 'a1 -> 'a1 vec vec -> 'a1 vec vec

val mrowAdd :
  ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> int -> fin -> fin -> 'a1 -> 'a1
  vec vec -> 'a1 vec vec

val mrowSwap : int -> fin -> fin -> 'a1 vec vec -> 'a1 vec vec

module Coq_method3 :
 sig
  val permOne : 'a1 -> 'a1 list -> 'a1 list list

  val perm : 'a1 list -> 'a1 list list
 end

val ronum1 : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> int

val ronum : ('a1 -> 'a1 -> bool) -> 'a1 list -> int

val mdet :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 -> int
  -> 'a1 vec vec -> 'a1

val mdet1 : 'a1 vec vec -> 'a1

val mdet2 :
  ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 vec vec -> 'a1

val mdet3 :
  ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 vec vec -> 'a1

val mdet4 :
  ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 vec vec -> 'a1

val msubmat : int -> 'a1 vec vec -> fin -> fin -> 'a1 vec vec

val mdetEx :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 -> int
  -> 'a1 vec vec -> 'a1

val mcofactorEx :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 -> int
  -> 'a1 vec vec -> fin -> fin -> 'a1

val madj :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 -> int
  -> 'a1 vec vec -> 'a1 vec vec

val cramerRule :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 ->
  ('a1 -> 'a1) -> int -> 'a1 vec vec -> 'a1 vec -> 'a1 vec

val cramerRuleList :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 ->
  ('a1 -> 'a1) -> int -> 'a1 list list -> 'a1 list -> 'a1 list

module OrderedElementTypeR :
 sig
  val coq_Order : RbaseSymbolsImpl.coq_R order
 end

module OrderedRingElementTypeR :
 sig
  val coq_Order : RbaseSymbolsImpl.coq_R order

  val coq_OrderedARing : RbaseSymbolsImpl.coq_R orderedARing
 end

module OrderedFieldElementTypeR :
 sig
  val coq_Order : RbaseSymbolsImpl.coq_R order

  val coq_OrderedARing : RbaseSymbolsImpl.coq_R orderedARing

  val coq_OrderedAField : RbaseSymbolsImpl.coq_R orderedField
 end

module type NormedOrderedFieldElementType =
 sig
  type coq_A

  val coq_Azero : coq_A

  val coq_AeqDec : coq_A dec

  val coq_Aadd : coq_A -> coq_A -> coq_A

  val coq_Aone : coq_A

  val coq_Amul : coq_A -> coq_A -> coq_A

  val coq_Aopp : coq_A -> coq_A

  val coq_Ainv : coq_A -> coq_A

  val coq_Altb : coq_A -> coq_A -> bool

  val coq_Aleb : coq_A -> coq_A -> bool

  val coq_Order : coq_A order

  val coq_OrderedARing : coq_A orderedARing

  val coq_OrderedAField : coq_A orderedField

  val a2r : coq_A -> RbaseSymbolsImpl.coq_R

  val coq_ConvertToR : coq_A convertToR
 end

module NormedOrderedFieldElementTypeR :
 sig
  type coq_A = RbaseSymbolsImpl.coq_R

  val coq_Azero : coq_A

  val coq_AeqDec : coq_A dec

  val coq_Aadd :
    RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R

  val coq_Aone : coq_A

  val coq_Aopp : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R

  val coq_Amul :
    RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R

  val coq_Ainv : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R

  val coq_Altb : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool

  val coq_Aleb : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool

  val coq_Order : RbaseSymbolsImpl.coq_R order

  val coq_OrderedARing : RbaseSymbolsImpl.coq_R orderedARing

  val coq_OrderedAField : RbaseSymbolsImpl.coq_R orderedField

  val a2r : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R

  val coq_ConvertToR : RbaseSymbolsImpl.coq_R convertToR
 end

val minvtbleb :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 -> 'a1
  dec -> int -> 'a1 vec vec -> bool

val minvo :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 ->
  ('a1 -> 'a1) -> 'a1 dec -> int -> 'a1 vec vec -> 'a1 vec vec option

val minv :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 ->
  ('a1 -> 'a1) -> 'a1 dec -> int -> 'a1 vec vec -> 'a1 vec vec

val minvNoCheck :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 ->
  ('a1 -> 'a1) -> int -> 'a1 vec vec -> 'a1 vec vec

val minvElement :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 ->
  ('a1 -> 'a1) -> int -> 'a1 vec vec -> fin -> fin -> 'a1

val minv1 :
  'a1 -> ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> 'a1 vec vec -> 'a1 vec vec

val minv2 :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 ->
  'a1) -> 'a1 vec vec -> 'a1 vec vec

val minv3 :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 ->
  'a1) -> 'a1 vec vec -> 'a1 vec vec

val minv4 :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 ->
  'a1) -> 'a1 vec vec -> 'a1 vec vec

type 'a rowOp =
| ROnop
| ROswap of fin * fin
| ROscale of fin * 'a
| ROadd of fin * fin * 'a

val rowOps2mat :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> 'a1 -> int -> 'a1 rowOp
  list -> 'a1 vec vec

val rowOps2matInv :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 ->
  ('a1 -> 'a1) -> int -> 'a1 rowOp list -> 'a1 vec vec

val firstNonzero :
  'a1 -> 'a1 dec -> int -> 'a1 vec vec -> int -> fin -> fin option

val elimDown :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 dec ->
  int -> 'a1 vec vec -> int -> fin -> 'a1 rowOp list * 'a1 vec vec

val rowEchelon :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 ->
  'a1) -> 'a1 dec -> int -> 'a1 vec vec -> int -> ('a1 rowOp list * 'a1 vec vec)
  option

val elimUp :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 dec ->
  int -> 'a1 vec vec -> int -> fin -> 'a1 rowOp list * 'a1 vec vec

val minRowEchelon :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 dec ->
  int -> 'a1 vec vec -> int -> 'a1 rowOp list * 'a1 vec vec

val minvtbleb0 :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 ->
  'a1) -> 'a1 dec -> int -> 'a1 vec vec -> bool

val minvo0 :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 ->
  ('a1 -> 'a1) -> 'a1 dec -> int -> 'a1 vec vec -> 'a1 vec vec option

val minv0 :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 ->
  ('a1 -> 'a1) -> 'a1 dec -> int -> 'a1 vec vec -> 'a1 vec vec

module NormedOrderedFieldMatrixTheory :
 functor (E:NormedOrderedFieldElementType) ->
 sig
  type vec = E.coq_A Coq__2.vec

  val veq_dec : int -> vec dec

  val v2f : int -> vec -> int -> E.coq_A

  val f2v : int -> (int -> E.coq_A) -> vec

  val v2l : int -> vec -> E.coq_A list

  val l2v : int -> E.coq_A list -> vec

  val mkvec1 : E.coq_A -> vec

  val mkvec2 : E.coq_A -> E.coq_A -> vec

  val mkvec3 : E.coq_A -> E.coq_A -> E.coq_A -> vec

  val mkvec4 : E.coq_A -> E.coq_A -> E.coq_A -> E.coq_A -> vec

  val vmap : int -> (E.coq_A -> E.coq_A) -> vec -> vec

  val vmap2 : int -> (E.coq_A -> E.coq_A -> E.coq_A) -> vec -> vec -> vec

  val vrepeat : int -> E.coq_A -> vec

  val vzero : int -> vec

  val vset : int -> vec -> fin -> E.coq_A -> vec

  val vswap : int -> vec -> fin -> fin -> vec

  val vinsert : int -> vec -> fin -> E.coq_A -> vec

  val vremove : int -> vec -> fin -> vec

  val vhead : int -> vec -> E.coq_A

  val vtail : int -> vec -> E.coq_A

  val vheadN : int -> int -> vec -> vec

  val vtailN : int -> int -> vec -> vec

  val vremoveH : int -> vec -> vec

  val vremoveT : int -> vec -> vec

  val vremoveHN : int -> int -> vec -> vec

  val vremoveTN : int -> int -> vec -> vec

  val vconsH : int -> E.coq_A -> vec -> vec

  val vconsT : int -> vec -> E.coq_A -> vec

  val vapp : int -> int -> vec -> vec -> vec

  val vmem_dec : int -> vec -> E.coq_A -> bool

  val vmems_dec : int -> int -> vec -> vec -> bool

  val vequiv_dec : int -> int -> vec -> vec -> bool

  val vfoldl : int -> vec -> 'a1 -> ('a1 -> E.coq_A -> 'a1) -> 'a1

  val vfoldr : int -> vec -> 'a1 -> (E.coq_A -> 'a1 -> 'a1) -> 'a1

  type mat = E.coq_A Coq__2.vec Coq__2.vec

  val cv2v : int -> mat -> vec

  val v2cv : int -> vec -> mat

  val rv2v : int -> mat -> vec

  val v2rv : int -> vec -> mat

  val f2m : int -> int -> (int -> int -> E.coq_A) -> mat

  val m2f : int -> int -> mat -> int -> int -> E.coq_A

  val l2m : int -> int -> E.coq_A list list -> mat

  val m2l : int -> int -> mat -> E.coq_A list list

  val m2rvl : int -> int -> mat -> vec list

  val rvl2m : int -> int -> vec list -> mat

  val m2cvl : int -> int -> mat -> vec list

  val cvl2m : int -> int -> vec list -> mat

  val mkmat_0_c : int -> mat

  val mkmat_r_0 : int -> mat

  val mkmat_1_1 : E.coq_A -> mat

  val mkmat_1_c : int -> vec -> mat

  val mkmat_r_1 : int -> vec -> mat

  val mkmat_1_2 : E.coq_A -> E.coq_A -> mat

  val mkmat_2_1 : E.coq_A -> E.coq_A -> mat

  val mkmat_2_2 : E.coq_A -> E.coq_A -> E.coq_A -> E.coq_A -> mat

  val mkmat_1_3 : E.coq_A -> E.coq_A -> E.coq_A -> mat

  val mkmat_3_1 : E.coq_A -> E.coq_A -> E.coq_A -> mat

  val mkmat_3_3 :
    E.coq_A -> E.coq_A -> E.coq_A -> E.coq_A -> E.coq_A -> E.coq_A -> E.coq_A ->
    E.coq_A -> E.coq_A -> mat

  val mkmat_1_4 : E.coq_A -> E.coq_A -> E.coq_A -> E.coq_A -> mat

  val mkmat_4_1 : E.coq_A -> E.coq_A -> E.coq_A -> E.coq_A -> mat

  val mkmat_4_4 :
    E.coq_A -> E.coq_A -> E.coq_A -> E.coq_A -> E.coq_A -> E.coq_A -> E.coq_A ->
    E.coq_A -> E.coq_A -> E.coq_A -> E.coq_A -> E.coq_A -> E.coq_A -> E.coq_A ->
    E.coq_A -> E.coq_A -> mat

  val mrow : int -> int -> mat -> fin -> vec

  val mcol : int -> int -> mat -> fin -> vec

  val mappr : int -> int -> int -> mat -> mat -> mat

  val mappc : int -> int -> int -> mat -> mat -> mat

  val mheadc : int -> int -> mat -> vec

  val mtailc : int -> int -> mat -> vec

  val mremovecH : int -> int -> mat -> mat

  val mremovecT : int -> int -> mat -> mat

  val mconsrH : int -> int -> vec -> mat -> mat

  val mconsrT : int -> int -> mat -> vec -> mat

  val mconscH : int -> int -> vec -> mat -> mat

  val mconscT : int -> int -> mat -> vec -> mat

  val mmap : int -> int -> (E.coq_A -> E.coq_A) -> mat -> mat

  val mmap2 : int -> int -> (E.coq_A -> E.coq_A -> E.coq_A) -> mat -> mat -> mat

  val msetr : int -> int -> mat -> vec -> fin -> mat

  val msetc : int -> int -> mat -> vec -> fin -> mat

  val mtrans : int -> int -> mat -> mat

  val mdiagMk : int -> vec -> mat

  val mat0 : int -> int -> mat

  val vsum : int -> vec -> E.coq_A

  val vadd : int -> vec -> vec -> vec

  val madd : int -> int -> mat -> mat -> mat

  val veye : int -> fin -> vec

  val veyes : int -> E.coq_A Coq__2.vec Coq__2.vec

  val vopp : int -> vec -> vec

  val vcmul : int -> E.coq_A -> vec -> vec

  val vdot : int -> vec -> vec -> E.coq_A

  val mat1 : int -> mat

  val mtrace : int -> mat -> E.coq_A

  val mopp : int -> int -> mat -> mat

  val mcmul : int -> int -> E.coq_A -> mat -> mat

  val mmul : int -> int -> int -> mat -> mat -> mat

  val mmulv : int -> int -> mat -> vec -> vec

  val mvmul : int -> int -> vec -> mat -> vec

  val mdet : int -> mat -> E.coq_A

  val mdet1 : mat -> E.coq_A

  val mdet2 : mat -> E.coq_A

  val mdet3 : mat -> E.coq_A

  val madj : int -> mat -> mat

  module AM :
   sig
    module Minv_inst :
     sig
      module AMNotations :
       sig
       end

      val minvtbleb : int -> E.coq_A Coq__2.vec Coq__2.vec -> bool

      val minvo :
        int -> E.coq_A Coq__2.vec Coq__2.vec -> E.coq_A Coq__2.vec Coq__2.vec
        option

      val minv :
        int -> E.coq_A Coq__2.vec Coq__2.vec -> E.coq_A Coq__2.vec Coq__2.vec

      val minvNoCheck :
        int -> E.coq_A Coq__2.vec Coq__2.vec -> E.coq_A Coq__2.vec Coq__2.vec
     end

    module MinvMore_inst :
     sig
      val minvtblebList : int -> E.coq_A list list -> bool

      val minvList : int -> E.coq_A list list -> E.coq_A list list

      val solveEq :
        int -> E.coq_A Coq__2.vec Coq__2.vec -> E.coq_A Coq__2.vec -> E.coq_A
        Coq__2.vec

      val solveEqList : int -> E.coq_A list list -> E.coq_A list -> E.coq_A list
     end

    val solveEqNoCheck :
      int -> E.coq_A Coq__2.vec Coq__2.vec -> E.coq_A Coq__2.vec -> E.coq_A
      Coq__2.vec

    val solveEqListNoCheck :
      int -> E.coq_A list list -> E.coq_A list -> E.coq_A list

    val minvElement :
      int -> E.coq_A Coq__2.vec Coq__2.vec -> fin -> fin -> E.coq_A

    val minv1 : E.coq_A Coq__2.vec Coq__2.vec -> E.coq_A Coq__2.vec Coq__2.vec

    val minv2 : E.coq_A Coq__2.vec Coq__2.vec -> E.coq_A Coq__2.vec Coq__2.vec

    val minv3 : E.coq_A Coq__2.vec Coq__2.vec -> E.coq_A Coq__2.vec Coq__2.vec

    val minv4 : E.coq_A Coq__2.vec Coq__2.vec -> E.coq_A Coq__2.vec Coq__2.vec
   end

  module GE :
   sig
    module Minv_inst :
     sig
      module GENotations :
       sig
       end

      val minvtbleb : int -> E.coq_A Coq__2.vec Coq__2.vec -> bool

      val minvo :
        int -> E.coq_A Coq__2.vec Coq__2.vec -> E.coq_A Coq__2.vec Coq__2.vec
        option

      val minv :
        int -> E.coq_A Coq__2.vec Coq__2.vec -> E.coq_A Coq__2.vec Coq__2.vec
     end

    module MinvMore_inst :
     sig
      val minvtblebList : int -> E.coq_A list list -> bool

      val minvList : int -> E.coq_A list list -> E.coq_A list list

      val solveEq :
        int -> E.coq_A Coq__2.vec Coq__2.vec -> E.coq_A Coq__2.vec -> E.coq_A
        Coq__2.vec

      val solveEqList : int -> E.coq_A list list -> E.coq_A list -> E.coq_A list
     end
   end

  module OrthAM :
   sig
    module AM :
     sig
      module Minv_inst :
       sig
        module AMNotations :
         sig
         end

        val minvtbleb : int -> E.coq_A Coq__2.vec Coq__2.vec -> bool

        val minvo :
          int -> E.coq_A Coq__2.vec Coq__2.vec -> E.coq_A Coq__2.vec Coq__2.vec
          option

        val minv :
          int -> E.coq_A Coq__2.vec Coq__2.vec -> E.coq_A Coq__2.vec Coq__2.vec

        val minvNoCheck :
          int -> E.coq_A Coq__2.vec Coq__2.vec -> E.coq_A Coq__2.vec Coq__2.vec
       end

      module MinvMore_inst :
       sig
        val minvtblebList : int -> E.coq_A list list -> bool

        val minvList : int -> E.coq_A list list -> E.coq_A list list

        val solveEq :
          int -> E.coq_A Coq__2.vec Coq__2.vec -> E.coq_A Coq__2.vec -> E.coq_A
          Coq__2.vec

        val solveEqList : int -> E.coq_A list list -> E.coq_A list -> E.coq_A list
       end

      val solveEqNoCheck :
        int -> E.coq_A Coq__2.vec Coq__2.vec -> E.coq_A Coq__2.vec -> E.coq_A
        Coq__2.vec

      val solveEqListNoCheck :
        int -> E.coq_A list list -> E.coq_A list -> E.coq_A list

      val minvElement :
        int -> E.coq_A Coq__2.vec Coq__2.vec -> fin -> fin -> E.coq_A

      val minv1 : E.coq_A Coq__2.vec Coq__2.vec -> E.coq_A Coq__2.vec Coq__2.vec

      val minv2 : E.coq_A Coq__2.vec Coq__2.vec -> E.coq_A Coq__2.vec Coq__2.vec

      val minv3 : E.coq_A Coq__2.vec Coq__2.vec -> E.coq_A Coq__2.vec Coq__2.vec

      val minv4 : E.coq_A Coq__2.vec Coq__2.vec -> E.coq_A Coq__2.vec Coq__2.vec
     end

    type coq_GOn =
      E.coq_A Coq__2.vec Coq__2.vec
      (* singleton inductive, whose constructor was Build_GOn *)

    val coq_GOn_mat : int -> coq_GOn -> E.coq_A Coq__2.vec Coq__2.vec

    val mkGOn : int -> E.coq_A Coq__2.vec Coq__2.vec -> coq_GOn

    val coq_GOn_mul : int -> coq_GOn -> coq_GOn -> coq_GOn

    val coq_GOn_1 : int -> coq_GOn

    val coq_GOn_inv : int -> coq_GOn -> coq_GOn

    type coq_SOn =
      coq_GOn
      (* singleton inductive, whose constructor was Build_SOn *)

    val coq_SOn_GOn : int -> coq_SOn -> coq_GOn

    val mkSOn : int -> E.coq_A Coq__2.vec Coq__2.vec -> coq_SOn

    val coq_SOn_mul : int -> coq_SOn -> coq_SOn -> coq_SOn

    val coq_SOn_1 : int -> coq_SOn

    val coq_SOn_inv : int -> coq_SOn -> coq_SOn
   end

  val vproj : int -> vec -> vec -> vec

  val vperp : int -> vec -> vec -> vec

  val cramerRule : int -> mat -> vec -> vec

  val cramerRuleList : int -> E.coq_A list list -> E.coq_A list -> E.coq_A list

  val rowOps2mat : int -> E.coq_A rowOp list -> mat

  val rowOps2matInv : int -> E.coq_A rowOp list -> mat

  val minvtblebGE : int -> mat -> bool

  val minvoGE : int -> mat -> mat option

  val minvGE : int -> mat -> mat

  module MinvGENotations :
   sig
   end

  val minvtblebListGE : int -> E.coq_A list list -> bool

  val minvListGE : int -> E.coq_A list list -> E.coq_A list list

  val solveEqGE : int -> mat -> vec -> vec

  val solveEqListGE : int -> E.coq_A list list -> E.coq_A list -> E.coq_A list

  val minvtblebAM : int -> mat -> bool

  val minvoAM : int -> mat -> mat option

  val minvAM : int -> mat -> mat

  module MinvAMNotations :
   sig
   end

  val minvAM1 : mat -> mat

  val minvAM2 : mat -> mat

  val minvAM3 : mat -> mat

  val minvAM4 : mat -> mat

  val minvtblebListAM : int -> E.coq_A list list -> bool

  val minvListAM : int -> E.coq_A list list -> E.coq_A list list

  val solveEqAM : int -> mat -> vec -> vec

  val solveEqListAM : int -> E.coq_A list list -> E.coq_A list -> E.coq_A list

  val minvNoCheckAM : int -> mat -> mat

  val solveEqNoCheckAM : int -> mat -> vec -> vec

  val solveEqListNoCheckAM :
    int -> E.coq_A list list -> E.coq_A list -> E.coq_A list

  type coq_GOn = OrthAM.coq_GOn

  val coq_GOn_mat : int -> coq_GOn -> mat

  val mkGOn : int -> mat -> coq_GOn

  val coq_GOn_mul : int -> coq_GOn -> coq_GOn -> coq_GOn

  val coq_GOn_1 : int -> coq_GOn

  val coq_GOn_inv : int -> coq_GOn -> coq_GOn

  type coq_SOn = OrthAM.coq_SOn

  val coq_SOn_GOn : int -> coq_SOn -> coq_GOn

  val mkSOn : int -> mat -> coq_SOn

  val coq_SOn_mul : int -> coq_SOn -> coq_SOn -> coq_SOn

  val coq_SOn_1 : int -> coq_SOn

  val coq_SOn_inv : int -> coq_SOn -> coq_SOn

  val vlen : int -> vec -> RbaseSymbolsImpl.coq_R
 end

module MatrixTheoryR :
 sig
  type vec = NormedOrderedFieldElementTypeR.coq_A Coq__2.vec

  val veq_dec : int -> vec dec

  val v2f : int -> vec -> int -> NormedOrderedFieldElementTypeR.coq_A

  val f2v : int -> (int -> NormedOrderedFieldElementTypeR.coq_A) -> vec

  val v2l : int -> vec -> NormedOrderedFieldElementTypeR.coq_A list

  val l2v : int -> NormedOrderedFieldElementTypeR.coq_A list -> vec

  val mkvec1 : NormedOrderedFieldElementTypeR.coq_A -> vec

  val mkvec2 :
    NormedOrderedFieldElementTypeR.coq_A -> NormedOrderedFieldElementTypeR.coq_A
    -> vec

  val mkvec3 :
    NormedOrderedFieldElementTypeR.coq_A -> NormedOrderedFieldElementTypeR.coq_A
    -> NormedOrderedFieldElementTypeR.coq_A -> vec

  val mkvec4 :
    NormedOrderedFieldElementTypeR.coq_A -> NormedOrderedFieldElementTypeR.coq_A
    -> NormedOrderedFieldElementTypeR.coq_A ->
    NormedOrderedFieldElementTypeR.coq_A -> vec

  val vmap :
    int -> (NormedOrderedFieldElementTypeR.coq_A ->
    NormedOrderedFieldElementTypeR.coq_A) -> vec -> vec

  val vmap2 :
    int -> (NormedOrderedFieldElementTypeR.coq_A ->
    NormedOrderedFieldElementTypeR.coq_A -> NormedOrderedFieldElementTypeR.coq_A)
    -> vec -> vec -> vec

  val vrepeat : int -> NormedOrderedFieldElementTypeR.coq_A -> vec

  val vzero : int -> vec

  val vset : int -> vec -> fin -> NormedOrderedFieldElementTypeR.coq_A -> vec

  val vswap : int -> vec -> fin -> fin -> vec

  val vinsert : int -> vec -> fin -> NormedOrderedFieldElementTypeR.coq_A -> vec

  val vremove : int -> vec -> fin -> vec

  val vhead : int -> vec -> NormedOrderedFieldElementTypeR.coq_A

  val vtail : int -> vec -> NormedOrderedFieldElementTypeR.coq_A

  val vheadN : int -> int -> vec -> vec

  val vtailN : int -> int -> vec -> vec

  val vremoveH : int -> vec -> vec

  val vremoveT : int -> vec -> vec

  val vremoveHN : int -> int -> vec -> vec

  val vremoveTN : int -> int -> vec -> vec

  val vconsH : int -> NormedOrderedFieldElementTypeR.coq_A -> vec -> vec

  val vconsT : int -> vec -> NormedOrderedFieldElementTypeR.coq_A -> vec

  val vapp : int -> int -> vec -> vec -> vec

  val vmem_dec : int -> vec -> NormedOrderedFieldElementTypeR.coq_A -> bool

  val vmems_dec : int -> int -> vec -> vec -> bool

  val vequiv_dec : int -> int -> vec -> vec -> bool

  val vfoldl :
    int -> vec -> 'a1 -> ('a1 -> NormedOrderedFieldElementTypeR.coq_A -> 'a1) ->
    'a1

  val vfoldr :
    int -> vec -> 'a1 -> (NormedOrderedFieldElementTypeR.coq_A -> 'a1 -> 'a1) ->
    'a1

  type mat = NormedOrderedFieldElementTypeR.coq_A Coq__2.vec Coq__2.vec

  val cv2v : int -> mat -> vec

  val v2cv : int -> vec -> mat

  val rv2v : int -> mat -> vec

  val v2rv : int -> vec -> mat

  val f2m :
    int -> int -> (int -> int -> NormedOrderedFieldElementTypeR.coq_A) -> mat

  val m2f :
    int -> int -> mat -> int -> int -> NormedOrderedFieldElementTypeR.coq_A

  val l2m : int -> int -> NormedOrderedFieldElementTypeR.coq_A list list -> mat

  val m2l : int -> int -> mat -> NormedOrderedFieldElementTypeR.coq_A list list

  val m2rvl : int -> int -> mat -> vec list

  val rvl2m : int -> int -> vec list -> mat

  val m2cvl : int -> int -> mat -> vec list

  val cvl2m : int -> int -> vec list -> mat

  val mkmat_0_c : int -> mat

  val mkmat_r_0 : int -> mat

  val mkmat_1_1 : NormedOrderedFieldElementTypeR.coq_A -> mat

  val mkmat_1_c : int -> vec -> mat

  val mkmat_r_1 : int -> vec -> mat

  val mkmat_1_2 :
    NormedOrderedFieldElementTypeR.coq_A -> NormedOrderedFieldElementTypeR.coq_A
    -> mat

  val mkmat_2_1 :
    NormedOrderedFieldElementTypeR.coq_A -> NormedOrderedFieldElementTypeR.coq_A
    -> mat

  val mkmat_2_2 :
    NormedOrderedFieldElementTypeR.coq_A -> NormedOrderedFieldElementTypeR.coq_A
    -> NormedOrderedFieldElementTypeR.coq_A ->
    NormedOrderedFieldElementTypeR.coq_A -> mat

  val mkmat_1_3 :
    NormedOrderedFieldElementTypeR.coq_A -> NormedOrderedFieldElementTypeR.coq_A
    -> NormedOrderedFieldElementTypeR.coq_A -> mat

  val mkmat_3_1 :
    NormedOrderedFieldElementTypeR.coq_A -> NormedOrderedFieldElementTypeR.coq_A
    -> NormedOrderedFieldElementTypeR.coq_A -> mat

  val mkmat_3_3 :
    NormedOrderedFieldElementTypeR.coq_A -> NormedOrderedFieldElementTypeR.coq_A
    -> NormedOrderedFieldElementTypeR.coq_A ->
    NormedOrderedFieldElementTypeR.coq_A -> NormedOrderedFieldElementTypeR.coq_A
    -> NormedOrderedFieldElementTypeR.coq_A ->
    NormedOrderedFieldElementTypeR.coq_A -> NormedOrderedFieldElementTypeR.coq_A
    -> NormedOrderedFieldElementTypeR.coq_A -> mat

  val mkmat_1_4 :
    NormedOrderedFieldElementTypeR.coq_A -> NormedOrderedFieldElementTypeR.coq_A
    -> NormedOrderedFieldElementTypeR.coq_A ->
    NormedOrderedFieldElementTypeR.coq_A -> mat

  val mkmat_4_1 :
    NormedOrderedFieldElementTypeR.coq_A -> NormedOrderedFieldElementTypeR.coq_A
    -> NormedOrderedFieldElementTypeR.coq_A ->
    NormedOrderedFieldElementTypeR.coq_A -> mat

  val mkmat_4_4 :
    NormedOrderedFieldElementTypeR.coq_A -> NormedOrderedFieldElementTypeR.coq_A
    -> NormedOrderedFieldElementTypeR.coq_A ->
    NormedOrderedFieldElementTypeR.coq_A -> NormedOrderedFieldElementTypeR.coq_A
    -> NormedOrderedFieldElementTypeR.coq_A ->
    NormedOrderedFieldElementTypeR.coq_A -> NormedOrderedFieldElementTypeR.coq_A
    -> NormedOrderedFieldElementTypeR.coq_A ->
    NormedOrderedFieldElementTypeR.coq_A -> NormedOrderedFieldElementTypeR.coq_A
    -> NormedOrderedFieldElementTypeR.coq_A ->
    NormedOrderedFieldElementTypeR.coq_A -> NormedOrderedFieldElementTypeR.coq_A
    -> NormedOrderedFieldElementTypeR.coq_A ->
    NormedOrderedFieldElementTypeR.coq_A -> mat

  val mrow : int -> int -> mat -> fin -> vec

  val mcol : int -> int -> mat -> fin -> vec

  val mappr : int -> int -> int -> mat -> mat -> mat

  val mappc : int -> int -> int -> mat -> mat -> mat

  val mheadc : int -> int -> mat -> vec

  val mtailc : int -> int -> mat -> vec

  val mremovecH : int -> int -> mat -> mat

  val mremovecT : int -> int -> mat -> mat

  val mconsrH : int -> int -> vec -> mat -> mat

  val mconsrT : int -> int -> mat -> vec -> mat

  val mconscH : int -> int -> vec -> mat -> mat

  val mconscT : int -> int -> mat -> vec -> mat

  val mmap :
    int -> int -> (NormedOrderedFieldElementTypeR.coq_A ->
    NormedOrderedFieldElementTypeR.coq_A) -> mat -> mat

  val mmap2 :
    int -> int -> (NormedOrderedFieldElementTypeR.coq_A ->
    NormedOrderedFieldElementTypeR.coq_A -> NormedOrderedFieldElementTypeR.coq_A)
    -> mat -> mat -> mat

  val msetr : int -> int -> mat -> vec -> fin -> mat

  val msetc : int -> int -> mat -> vec -> fin -> mat

  val mtrans : int -> int -> mat -> mat

  val mdiagMk : int -> vec -> mat

  val mat0 : int -> int -> mat

  val vsum : int -> vec -> NormedOrderedFieldElementTypeR.coq_A

  val vadd : int -> vec -> vec -> vec

  val madd : int -> int -> mat -> mat -> mat

  val veye : int -> fin -> vec

  val veyes : int -> NormedOrderedFieldElementTypeR.coq_A Coq__2.vec Coq__2.vec

  val vopp : int -> vec -> vec

  val vcmul : int -> NormedOrderedFieldElementTypeR.coq_A -> vec -> vec

  val vdot : int -> vec -> vec -> NormedOrderedFieldElementTypeR.coq_A

  val mat1 : int -> mat

  val mtrace : int -> mat -> NormedOrderedFieldElementTypeR.coq_A

  val mopp : int -> int -> mat -> mat

  val mcmul : int -> int -> NormedOrderedFieldElementTypeR.coq_A -> mat -> mat

  val mmul : int -> int -> int -> mat -> mat -> mat

  val mmulv : int -> int -> mat -> vec -> vec

  val mvmul : int -> int -> vec -> mat -> vec

  val mdet : int -> mat -> NormedOrderedFieldElementTypeR.coq_A

  val mdet1 : mat -> NormedOrderedFieldElementTypeR.coq_A

  val mdet2 : mat -> NormedOrderedFieldElementTypeR.coq_A

  val mdet3 : mat -> NormedOrderedFieldElementTypeR.coq_A

  val madj : int -> mat -> mat

  module AM :
   sig
    module Minv_inst :
     sig
      module AMNotations :
       sig
       end

      val minvtbleb :
        int -> NormedOrderedFieldElementTypeR.coq_A Coq__2.vec Coq__2.vec -> bool

      val minvo :
        int -> NormedOrderedFieldElementTypeR.coq_A Coq__2.vec Coq__2.vec ->
        NormedOrderedFieldElementTypeR.coq_A Coq__2.vec Coq__2.vec option

      val minv :
        int -> NormedOrderedFieldElementTypeR.coq_A Coq__2.vec Coq__2.vec ->
        NormedOrderedFieldElementTypeR.coq_A Coq__2.vec Coq__2.vec

      val minvNoCheck :
        int -> NormedOrderedFieldElementTypeR.coq_A Coq__2.vec Coq__2.vec ->
        NormedOrderedFieldElementTypeR.coq_A Coq__2.vec Coq__2.vec
     end

    module MinvMore_inst :
     sig
      val minvtblebList :
        int -> NormedOrderedFieldElementTypeR.coq_A list list -> bool

      val minvList :
        int -> NormedOrderedFieldElementTypeR.coq_A list list ->
        NormedOrderedFieldElementTypeR.coq_A list list

      val solveEq :
        int -> NormedOrderedFieldElementTypeR.coq_A Coq__2.vec Coq__2.vec ->
        NormedOrderedFieldElementTypeR.coq_A Coq__2.vec ->
        NormedOrderedFieldElementTypeR.coq_A Coq__2.vec

      val solveEqList :
        int -> NormedOrderedFieldElementTypeR.coq_A list list ->
        NormedOrderedFieldElementTypeR.coq_A list ->
        NormedOrderedFieldElementTypeR.coq_A list
     end

    val solveEqNoCheck :
      int -> NormedOrderedFieldElementTypeR.coq_A Coq__2.vec Coq__2.vec ->
      NormedOrderedFieldElementTypeR.coq_A Coq__2.vec ->
      NormedOrderedFieldElementTypeR.coq_A Coq__2.vec

    val solveEqListNoCheck :
      int -> NormedOrderedFieldElementTypeR.coq_A list list ->
      NormedOrderedFieldElementTypeR.coq_A list ->
      NormedOrderedFieldElementTypeR.coq_A list

    val minvElement :
      int -> NormedOrderedFieldElementTypeR.coq_A Coq__2.vec Coq__2.vec -> fin ->
      fin -> NormedOrderedFieldElementTypeR.coq_A

    val minv1 :
      NormedOrderedFieldElementTypeR.coq_A Coq__2.vec Coq__2.vec ->
      NormedOrderedFieldElementTypeR.coq_A Coq__2.vec Coq__2.vec

    val minv2 :
      NormedOrderedFieldElementTypeR.coq_A Coq__2.vec Coq__2.vec ->
      NormedOrderedFieldElementTypeR.coq_A Coq__2.vec Coq__2.vec

    val minv3 :
      NormedOrderedFieldElementTypeR.coq_A Coq__2.vec Coq__2.vec ->
      NormedOrderedFieldElementTypeR.coq_A Coq__2.vec Coq__2.vec

    val minv4 :
      NormedOrderedFieldElementTypeR.coq_A Coq__2.vec Coq__2.vec ->
      NormedOrderedFieldElementTypeR.coq_A Coq__2.vec Coq__2.vec
   end

  module GE :
   sig
    module Minv_inst :
     sig
      module GENotations :
       sig
       end

      val minvtbleb :
        int -> NormedOrderedFieldElementTypeR.coq_A Coq__2.vec Coq__2.vec -> bool

      val minvo :
        int -> NormedOrderedFieldElementTypeR.coq_A Coq__2.vec Coq__2.vec ->
        NormedOrderedFieldElementTypeR.coq_A Coq__2.vec Coq__2.vec option

      val minv :
        int -> NormedOrderedFieldElementTypeR.coq_A Coq__2.vec Coq__2.vec ->
        NormedOrderedFieldElementTypeR.coq_A Coq__2.vec Coq__2.vec
     end

    module MinvMore_inst :
     sig
      val minvtblebList :
        int -> NormedOrderedFieldElementTypeR.coq_A list list -> bool

      val minvList :
        int -> NormedOrderedFieldElementTypeR.coq_A list list ->
        NormedOrderedFieldElementTypeR.coq_A list list

      val solveEq :
        int -> NormedOrderedFieldElementTypeR.coq_A Coq__2.vec Coq__2.vec ->
        NormedOrderedFieldElementTypeR.coq_A Coq__2.vec ->
        NormedOrderedFieldElementTypeR.coq_A Coq__2.vec

      val solveEqList :
        int -> NormedOrderedFieldElementTypeR.coq_A list list ->
        NormedOrderedFieldElementTypeR.coq_A list ->
        NormedOrderedFieldElementTypeR.coq_A list
     end
   end

  module OrthAM :
   sig
    module AM :
     sig
      module Minv_inst :
       sig
        module AMNotations :
         sig
         end

        val minvtbleb :
          int -> NormedOrderedFieldElementTypeR.coq_A Coq__2.vec Coq__2.vec ->
          bool

        val minvo :
          int -> NormedOrderedFieldElementTypeR.coq_A Coq__2.vec Coq__2.vec ->
          NormedOrderedFieldElementTypeR.coq_A Coq__2.vec Coq__2.vec option

        val minv :
          int -> NormedOrderedFieldElementTypeR.coq_A Coq__2.vec Coq__2.vec ->
          NormedOrderedFieldElementTypeR.coq_A Coq__2.vec Coq__2.vec

        val minvNoCheck :
          int -> NormedOrderedFieldElementTypeR.coq_A Coq__2.vec Coq__2.vec ->
          NormedOrderedFieldElementTypeR.coq_A Coq__2.vec Coq__2.vec
       end

      module MinvMore_inst :
       sig
        val minvtblebList :
          int -> NormedOrderedFieldElementTypeR.coq_A list list -> bool

        val minvList :
          int -> NormedOrderedFieldElementTypeR.coq_A list list ->
          NormedOrderedFieldElementTypeR.coq_A list list

        val solveEq :
          int -> NormedOrderedFieldElementTypeR.coq_A Coq__2.vec Coq__2.vec ->
          NormedOrderedFieldElementTypeR.coq_A Coq__2.vec ->
          NormedOrderedFieldElementTypeR.coq_A Coq__2.vec

        val solveEqList :
          int -> NormedOrderedFieldElementTypeR.coq_A list list ->
          NormedOrderedFieldElementTypeR.coq_A list ->
          NormedOrderedFieldElementTypeR.coq_A list
       end

      val solveEqNoCheck :
        int -> NormedOrderedFieldElementTypeR.coq_A Coq__2.vec Coq__2.vec ->
        NormedOrderedFieldElementTypeR.coq_A Coq__2.vec ->
        NormedOrderedFieldElementTypeR.coq_A Coq__2.vec

      val solveEqListNoCheck :
        int -> NormedOrderedFieldElementTypeR.coq_A list list ->
        NormedOrderedFieldElementTypeR.coq_A list ->
        NormedOrderedFieldElementTypeR.coq_A list

      val minvElement :
        int -> NormedOrderedFieldElementTypeR.coq_A Coq__2.vec Coq__2.vec -> fin
        -> fin -> NormedOrderedFieldElementTypeR.coq_A

      val minv1 :
        NormedOrderedFieldElementTypeR.coq_A Coq__2.vec Coq__2.vec ->
        NormedOrderedFieldElementTypeR.coq_A Coq__2.vec Coq__2.vec

      val minv2 :
        NormedOrderedFieldElementTypeR.coq_A Coq__2.vec Coq__2.vec ->
        NormedOrderedFieldElementTypeR.coq_A Coq__2.vec Coq__2.vec

      val minv3 :
        NormedOrderedFieldElementTypeR.coq_A Coq__2.vec Coq__2.vec ->
        NormedOrderedFieldElementTypeR.coq_A Coq__2.vec Coq__2.vec

      val minv4 :
        NormedOrderedFieldElementTypeR.coq_A Coq__2.vec Coq__2.vec ->
        NormedOrderedFieldElementTypeR.coq_A Coq__2.vec Coq__2.vec
     end

    type coq_GOn =
      NormedOrderedFieldElementTypeR.coq_A Coq__2.vec Coq__2.vec
      (* singleton inductive, whose constructor was Build_GOn *)

    val coq_GOn_mat :
      int -> coq_GOn -> NormedOrderedFieldElementTypeR.coq_A Coq__2.vec Coq__2.vec

    val mkGOn :
      int -> NormedOrderedFieldElementTypeR.coq_A Coq__2.vec Coq__2.vec -> coq_GOn

    val coq_GOn_mul : int -> coq_GOn -> coq_GOn -> coq_GOn

    val coq_GOn_1 : int -> coq_GOn

    val coq_GOn_inv : int -> coq_GOn -> coq_GOn

    type coq_SOn =
      coq_GOn
      (* singleton inductive, whose constructor was Build_SOn *)

    val coq_SOn_GOn : int -> coq_SOn -> coq_GOn

    val mkSOn :
      int -> NormedOrderedFieldElementTypeR.coq_A Coq__2.vec Coq__2.vec -> coq_SOn

    val coq_SOn_mul : int -> coq_SOn -> coq_SOn -> coq_SOn

    val coq_SOn_1 : int -> coq_SOn

    val coq_SOn_inv : int -> coq_SOn -> coq_SOn
   end

  val vproj : int -> vec -> vec -> vec

  val vperp : int -> vec -> vec -> vec

  val cramerRule : int -> mat -> vec -> vec

  val cramerRuleList :
    int -> NormedOrderedFieldElementTypeR.coq_A list list ->
    NormedOrderedFieldElementTypeR.coq_A list ->
    NormedOrderedFieldElementTypeR.coq_A list

  val rowOps2mat : int -> NormedOrderedFieldElementTypeR.coq_A rowOp list -> mat

  val rowOps2matInv :
    int -> NormedOrderedFieldElementTypeR.coq_A rowOp list -> mat

  val minvtblebGE : int -> mat -> bool

  val minvoGE : int -> mat -> mat option

  val minvGE : int -> mat -> mat

  module MinvGENotations :
   sig
   end

  val minvtblebListGE :
    int -> NormedOrderedFieldElementTypeR.coq_A list list -> bool

  val minvListGE :
    int -> NormedOrderedFieldElementTypeR.coq_A list list ->
    NormedOrderedFieldElementTypeR.coq_A list list

  val solveEqGE : int -> mat -> vec -> vec

  val solveEqListGE :
    int -> NormedOrderedFieldElementTypeR.coq_A list list ->
    NormedOrderedFieldElementTypeR.coq_A list ->
    NormedOrderedFieldElementTypeR.coq_A list

  val minvtblebAM : int -> mat -> bool

  val minvoAM : int -> mat -> mat option

  val minvAM : int -> mat -> mat

  module MinvAMNotations :
   sig
   end

  val minvAM1 : mat -> mat

  val minvAM2 : mat -> mat

  val minvAM3 : mat -> mat

  val minvAM4 : mat -> mat

  val minvtblebListAM :
    int -> NormedOrderedFieldElementTypeR.coq_A list list -> bool

  val minvListAM :
    int -> NormedOrderedFieldElementTypeR.coq_A list list ->
    NormedOrderedFieldElementTypeR.coq_A list list

  val solveEqAM : int -> mat -> vec -> vec

  val solveEqListAM :
    int -> NormedOrderedFieldElementTypeR.coq_A list list ->
    NormedOrderedFieldElementTypeR.coq_A list ->
    NormedOrderedFieldElementTypeR.coq_A list

  val minvNoCheckAM : int -> mat -> mat

  val solveEqNoCheckAM : int -> mat -> vec -> vec

  val solveEqListNoCheckAM :
    int -> NormedOrderedFieldElementTypeR.coq_A list list ->
    NormedOrderedFieldElementTypeR.coq_A list ->
    NormedOrderedFieldElementTypeR.coq_A list

  type coq_GOn = OrthAM.coq_GOn

  val coq_GOn_mat : int -> coq_GOn -> mat

  val mkGOn : int -> mat -> coq_GOn

  val coq_GOn_mul : int -> coq_GOn -> coq_GOn -> coq_GOn

  val coq_GOn_1 : int -> coq_GOn

  val coq_GOn_inv : int -> coq_GOn -> coq_GOn

  type coq_SOn = OrthAM.coq_SOn

  val coq_SOn_GOn : int -> coq_SOn -> coq_GOn

  val mkSOn : int -> mat -> coq_SOn

  val coq_SOn_mul : int -> coq_SOn -> coq_SOn -> coq_SOn

  val coq_SOn_1 : int -> coq_SOn

  val coq_SOn_inv : int -> coq_SOn -> coq_SOn

  val vlen : int -> vec -> RbaseSymbolsImpl.coq_R
 end
