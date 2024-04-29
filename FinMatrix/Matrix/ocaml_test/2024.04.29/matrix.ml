
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



(** val pred : int -> int **)

let pred = fun n -> Stdlib.max 0 (n-1)

module Coq__1 = struct
 (** val add : int -> int -> int **)

 let rec add = (+)
end
include Coq__1

(** val sub : int -> int -> int **)

let rec sub = fun n m -> Stdlib.max 0 (n-m)

(** val even : int -> bool **)

let rec even n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> true)
    (fun n0 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> false)
      (fun n' -> even n')
      n0)
    n

(** val odd : int -> bool **)

let odd n =
  negb (even n)

type reflect =
| ReflectT
| ReflectF

module Nat =
 struct
  (** val add : int -> int -> int **)

  let rec add n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> m)
      (fun p -> Stdlib.Int.succ (add p m))
      n

  (** val mul : int -> int -> int **)

  let rec mul n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun p -> add m (mul p m))
      n

  (** val ltb : int -> int -> bool **)

  let ltb n m =
    (<=) (Stdlib.Int.succ n) m

  (** val even : int -> bool **)

  let rec even n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> true)
      (fun n0 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> false)
        (fun n' -> even n')
        n0)
      n

  (** val pow : int -> int -> int **)

  let rec pow n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Stdlib.Int.succ 0)
      (fun m0 -> mul n (pow n m0))
      m
 end

(** val nth : int -> 'a1 list -> 'a1 -> 'a1 **)

let rec nth n l default =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> match l with
              | [] -> default
              | x :: _ -> x)
    (fun m -> match l with
              | [] -> default
              | _ :: t -> nth m t default)
    n

(** val concat : 'a1 list list -> 'a1 list **)

let rec concat = function
| [] -> []
| x :: l0 -> app x (concat l0)

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t -> (f a) :: (map f t)

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | [] -> a0
  | b :: t -> fold_left f t (f a0 b)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b :: t -> f b (fold_right f a0 t)

(** val seq : int -> int -> int list **)

let rec seq start len =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun len0 -> start :: (seq (Stdlib.Int.succ start) len0))
    len

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos =
 struct
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
 end

module Coq_Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XI (add p q0)
       | XO q0 -> XO (add p q0)
       | XH -> XI p)
    | XH -> (match y with
             | XI q0 -> XO (succ q0)
             | XO q0 -> XI q0
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XI (add_carry p q0)
       | XO q0 -> XO (add_carry p q0)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q0 -> XI (succ q0)
       | XO q0 -> XO (succ q0)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos (XO p)
  | x0 -> x0

  (** val double_pred_mask : positive -> mask **)

  let double_pred_mask = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pred_double p))
  | XH -> IsNul

  (** val sub_mask : positive -> positive -> mask **)

  let rec sub_mask x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> double_mask (sub_mask p q0)
       | XO q0 -> succ_double_mask (sub_mask p q0)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q0 -> succ_double_mask (sub_mask_carry p q0)
       | XO q0 -> double_mask (sub_mask p q0)
       | XH -> IsPos (pred_double p))
    | XH -> (match y with
             | XH -> IsNul
             | _ -> IsNeg)

  (** val sub_mask_carry : positive -> positive -> mask **)

  and sub_mask_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> succ_double_mask (sub_mask_carry p q0)
       | XO q0 -> double_mask (sub_mask p q0)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q0 -> double_mask (sub_mask_carry p q0)
       | XO q0 -> succ_double_mask (sub_mask_carry p q0)
       | XH -> double_pred_mask p)
    | XH -> IsNeg

  (** val sub : positive -> positive -> positive **)

  let sub x y =
    match sub_mask x y with
    | IsPos z0 -> z0
    | _ -> XH

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

  let rec iter f x = function
  | XI n' -> f (iter f (iter f x n') n')
  | XO n' -> iter f (iter f x n') n'
  | XH -> f x

  (** val pow : positive -> positive -> positive **)

  let pow x =
    iter (mul x) XH

  (** val size_nat : positive -> int **)

  let rec size_nat = function
  | XI p0 -> Stdlib.Int.succ (size_nat p0)
  | XO p0 -> Stdlib.Int.succ (size_nat p0)
  | XH -> Stdlib.Int.succ 0

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> compare_cont r p q0
       | XO q0 -> compare_cont Gt p q0
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q0 -> compare_cont Lt p q0
       | XO q0 -> compare_cont r p q0
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val ggcdn :
      int -> positive -> positive -> positive * (positive * positive) **)

  let rec ggcdn n a b =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> (XH, (a, b)))
      (fun n0 ->
      match a with
      | XI a' ->
        (match b with
         | XI b' ->
           (match compare a' b' with
            | Eq -> (a, (XH, XH))
            | Lt ->
              let (g, p) = ggcdn n0 (sub b' a') a in
              let (ba, aa) = p in (g, (aa, (add aa (XO ba))))
            | Gt ->
              let (g, p) = ggcdn n0 (sub a' b') b in
              let (ab, bb) = p in (g, ((add bb (XO ab)), bb)))
         | XO b0 ->
           let (g, p) = ggcdn n0 a b0 in let (aa, bb) = p in (g, (aa, (XO bb)))
         | XH -> (XH, (a, XH)))
      | XO a0 ->
        (match b with
         | XI _ ->
           let (g, p) = ggcdn n0 a0 b in let (aa, bb) = p in (g, ((XO aa), bb))
         | XO b0 -> let (g, p) = ggcdn n0 a0 b0 in ((XO g), p)
         | XH -> (XH, (a, XH)))
      | XH -> (XH, (XH, b)))
      n

  (** val ggcd : positive -> positive -> positive * (positive * positive) **)

  let ggcd a b =
    ggcdn (Coq__1.add (size_nat a) (size_nat b)) a b

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a

  (** val to_nat : positive -> int **)

  let to_nat x =
    iter_op Coq__1.add x (Stdlib.Int.succ 0)

  (** val of_nat : int -> positive **)

  let rec of_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> XH)
      (fun x ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> XH)
        (fun _ -> succ (of_nat x))
        x)
      n

  (** val of_succ_nat : int -> positive **)

  let rec of_succ_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> XH)
      (fun x -> succ (of_succ_nat x))
      n
 end

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Coq_Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Coq_Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> double (pos_sub p q0)
       | XO q0 -> succ_double (pos_sub p q0)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q0 -> pred_double (pos_sub p q0)
       | XO q0 -> double (pos_sub p q0)
       | XH -> Zpos (Coq_Pos.pred_double p))
    | XH ->
      (match y with
       | XI q0 -> Zneg (XO q0)
       | XO q0 -> Zneg (Coq_Pos.pred_double q0)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Coq_Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Coq_Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val sub : z -> z -> z **)

  let sub m n =
    add m (opp n)

  (** val mul : z -> z -> z **)

  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Coq_Pos.mul x' y')
       | Zneg y' -> Zneg (Coq_Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Coq_Pos.mul x' y')
       | Zneg y' -> Zpos (Coq_Pos.mul x' y'))

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Coq_Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Coq_Pos.compare x' y')
       | _ -> Lt)

  (** val sgn : z -> z **)

  let sgn = function
  | Z0 -> Z0
  | Zpos _ -> Zpos XH
  | Zneg _ -> Zneg XH

  (** val leb : z -> z -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : z -> z -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val max : z -> z -> z **)

  let max n m =
    match compare n m with
    | Lt -> m
    | _ -> n

  (** val min : z -> z -> z **)

  let min n m =
    match compare n m with
    | Gt -> m
    | _ -> n

  (** val abs : z -> z **)

  let abs = function
  | Zneg p -> Zpos p
  | x -> x

  (** val to_nat : z -> int **)

  let to_nat = function
  | Zpos p -> Coq_Pos.to_nat p
  | _ -> 0

  (** val of_nat : int -> z **)

  let of_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Z0)
      (fun n0 -> Zpos (Coq_Pos.of_succ_nat n0))
      n

  (** val to_pos : z -> positive **)

  let to_pos = function
  | Zpos p -> p
  | _ -> XH

  (** val pos_div_eucl : positive -> z -> z * z **)

  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let (q0, r) = pos_div_eucl a' b in
      let r' = add (mul (Zpos (XO XH)) r) (Zpos XH) in
      if ltb r' b
      then ((mul (Zpos (XO XH)) q0), r')
      else ((add (mul (Zpos (XO XH)) q0) (Zpos XH)), (sub r' b))
    | XO a' ->
      let (q0, r) = pos_div_eucl a' b in
      let r' = mul (Zpos (XO XH)) r in
      if ltb r' b
      then ((mul (Zpos (XO XH)) q0), r')
      else ((add (mul (Zpos (XO XH)) q0) (Zpos XH)), (sub r' b))
    | XH -> if leb (Zpos (XO XH)) b then (Z0, (Zpos XH)) else ((Zpos XH), Z0)

  (** val div_eucl : z -> z -> z * z **)

  let div_eucl a b =
    match a with
    | Z0 -> (Z0, Z0)
    | Zpos a' ->
      (match b with
       | Z0 -> (Z0, a)
       | Zpos _ -> pos_div_eucl a' b
       | Zneg b' ->
         let (q0, r) = pos_div_eucl a' (Zpos b') in
         (match r with
          | Z0 -> ((opp q0), Z0)
          | _ -> ((opp (add q0 (Zpos XH))), (add b r))))
    | Zneg a' ->
      (match b with
       | Z0 -> (Z0, a)
       | Zpos _ ->
         let (q0, r) = pos_div_eucl a' b in
         (match r with
          | Z0 -> ((opp q0), Z0)
          | _ -> ((opp (add q0 (Zpos XH))), (sub b r)))
       | Zneg b' -> let (q0, r) = pos_div_eucl a' (Zpos b') in (q0, (opp r)))

  (** val div : z -> z -> z **)

  let div a b =
    let (q0, _) = div_eucl a b in q0

  (** val ggcd : z -> z -> z * (z * z) **)

  let ggcd a b =
    match a with
    | Z0 -> ((abs b), (Z0, (sgn b)))
    | Zpos a0 ->
      (match b with
       | Z0 -> ((abs a), ((sgn a), Z0))
       | Zpos b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p in ((Zpos g), ((Zpos aa), (Zpos bb)))
       | Zneg b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p in ((Zpos g), ((Zpos aa), (Zneg bb))))
    | Zneg a0 ->
      (match b with
       | Z0 -> ((abs a), ((sgn a), Z0))
       | Zpos b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p in ((Zpos g), ((Zneg aa), (Zpos bb)))
       | Zneg b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p in ((Zpos g), ((Zneg aa), (Zneg bb))))
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

module RbaseSymbolsImpl =
 struct
  type coq_R = float

  (** val coq_Rabst : cReal -> dReal **)

  let coq_Rabst = __

  (** val coq_Rrepr : dReal -> cReal **)

  let coq_Rrepr = __

  (** val coq_Rquot1 : __ **)

  let coq_Rquot1 =
    __

  (** val coq_Rquot2 : __ **)

  let coq_Rquot2 =
    __

  (** val coq_R0 : coq_R **)

  let coq_R0 = 0.0

  (** val coq_R1 : coq_R **)

  let coq_R1 = 1.0

  (** val coq_Rplus : coq_R -> coq_R -> coq_R **)

  let coq_Rplus = (+.)

  (** val coq_Rmult : coq_R -> coq_R -> coq_R **)

  let coq_Rmult = ( *. )

  (** val coq_Ropp : coq_R -> coq_R **)

  let coq_Ropp = fun a -> (0.0 -. a)

  type coq_Rlt = __

  (** val coq_R0_def : __ **)

  let coq_R0_def =
    __

  (** val coq_R1_def : __ **)

  let coq_R1_def =
    __

  (** val coq_Rplus_def : __ **)

  let coq_Rplus_def =
    __

  (** val coq_Rmult_def : __ **)

  let coq_Rmult_def =
    __

  (** val coq_Ropp_def : __ **)

  let coq_Ropp_def =
    __

  (** val coq_Rlt_def : __ **)

  let coq_Rlt_def =
    __
 end

(** val iPR_2 : positive -> RbaseSymbolsImpl.coq_R **)

let rec iPR_2 = function
| XI p0 ->
  RbaseSymbolsImpl.coq_Rmult
    (RbaseSymbolsImpl.coq_Rplus RbaseSymbolsImpl.coq_R1 RbaseSymbolsImpl.coq_R1)
    (RbaseSymbolsImpl.coq_Rplus RbaseSymbolsImpl.coq_R1 (iPR_2 p0))
| XO p0 ->
  RbaseSymbolsImpl.coq_Rmult
    (RbaseSymbolsImpl.coq_Rplus RbaseSymbolsImpl.coq_R1 RbaseSymbolsImpl.coq_R1)
    (iPR_2 p0)
| XH -> RbaseSymbolsImpl.coq_Rplus RbaseSymbolsImpl.coq_R1 RbaseSymbolsImpl.coq_R1

(** val iPR : positive -> RbaseSymbolsImpl.coq_R **)

let iPR = function
| XI p0 -> RbaseSymbolsImpl.coq_Rplus RbaseSymbolsImpl.coq_R1 (iPR_2 p0)
| XO p0 -> iPR_2 p0
| XH -> RbaseSymbolsImpl.coq_R1

(** val iZR : z -> RbaseSymbolsImpl.coq_R **)

let iZR = function
| Z0 -> RbaseSymbolsImpl.coq_R0
| Zpos n -> iPR n
| Zneg n -> RbaseSymbolsImpl.coq_Ropp (iPR n)

(** val total_order_T :
    RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool option **)

let total_order_T = fun r1 r2 ->
  let c = Float.compare r1 r2 in
  if c < 0 then Some true
  else (if c = 0 then None else Some false)

module type RinvSig =
 sig
  val coq_Rinv : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R
 end

module RinvImpl =
 struct
  (** val coq_Rinv : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

  let coq_Rinv = fun a -> (1.0 /. a)

  (** val coq_Rinv_def : __ **)

  let coq_Rinv_def =
    __
 end

(** val req_dec_T : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool **)

let req_dec_T = fun r1 r2 ->
  let c = Float.compare r1 r2 in
  if c = 0 then true
  else false

(** val rlt_dec : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool **)

let rlt_dec r1 r2 =
  let s = total_order_T r1 r2 in (match s with
                                  | Some s0 -> s0
                                  | None -> false)

(** val rle_dec : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool **)

let rle_dec r1 r2 =
  let s = rlt_dec r2 r1 in if s then false else true

(** val rlt_le_dec : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool **)

let rlt_le_dec =
  rlt_dec

(** val rle_lt_dec : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool **)

let rle_lt_dec =
  rle_dec

(** val id : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

let id x =
  x

(** val sqrt : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

let sqrt = Float.sqrt

type 'a dec =
  'a -> 'a -> bool
  (* singleton inductive, whose constructor was Build_Dec *)

(** val aeqdec : 'a1 dec -> 'a1 -> 'a1 -> bool **)

let aeqdec aeqDec =
  aeqDec

(** val acmpb : 'a1 dec -> 'a1 -> 'a1 -> bool **)

let acmpb hDec a b =
  if hDec a b then true else false

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

(** val r_eq_Dec : RbaseSymbolsImpl.coq_R dec **)

let r_eq_Dec =
  req_dec_T

(** val r_le_Dec : RbaseSymbolsImpl.coq_R dec **)

let r_le_Dec =
  rle_lt_dec

(** val r_lt_Dec : RbaseSymbolsImpl.coq_R dec **)

let r_lt_Dec =
  rlt_le_dec

(** val rleb : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool **)

let rleb r1 r2 =
  acmpb r_le_Dec r1 r2

(** val rltb : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool **)

let rltb r1 r2 =
  acmpb r_lt_Dec r1 r2

(** val rltb_reflect :
    RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> reflect **)

let rltb_reflect x y =
  let s = r_lt_Dec x y in if s then ReflectT else ReflectF

(** val rleb_reflect :
    RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> reflect **)

let rleb_reflect x y =
  let s = r_le_Dec x y in if s then ReflectT else ReflectF

(** val r_Order : RbaseSymbolsImpl.coq_R order **)

let r_Order =
  { lt_cases = (fun a b ->
    let s = total_order_T a b in
    (match s with
     | Some s0 -> if s0 then Some true else None
     | None -> Some false)); ltb_reflect = rltb_reflect; leb_reflect =
    rleb_reflect }

(** val r_ConvertToR : RbaseSymbolsImpl.coq_R convertToR **)

let r_ConvertToR =
  r_Order

(** val nat_eq_Dec : int dec **)

let nat_eq_Dec =
  (=)

(** val nat_lt_Dec : int dec **)

let nat_lt_Dec =
  (<)

type fin = int
  (* singleton inductive, whose constructor was Fin *)

(** val fin2nat : int -> fin -> int **)

let fin2nat _ f =
  f

(** val fin0 : int -> fin **)

let fin0 _ =
  0

(** val nat2finS : int -> int -> fin **)

let nat2finS n i =
  let s = nat_lt_Dec i (Stdlib.Int.succ n) in if s then i else fin0 n

(** val nat2fin : int -> int -> fin **)

let nat2fin _ i =
  i

(** val fin2SuccRange : int -> fin -> fin **)

let fin2SuccRange n i =
  nat2finS n (fin2nat n i)

(** val fin2PredRange : int -> fin -> fin **)

let fin2PredRange n i =
  nat2fin n (fin2nat (Stdlib.Int.succ n) i)

(** val fin2AddRangeR : int -> int -> fin -> fin **)

let fin2AddRangeR m n i =
  nat2fin (add m n) (fin2nat m i)

(** val fin2AddRangeR' : int -> int -> fin -> fin **)

let fin2AddRangeR' m n i =
  nat2fin m (fin2nat (add m n) i)

(** val fin2AddRangeAddL : int -> int -> fin -> fin **)

let fin2AddRangeAddL m n i =
  nat2fin (add m n) (add m (fin2nat n i))

(** val fin2AddRangeAddL' : int -> int -> fin -> fin **)

let fin2AddRangeAddL' m n i =
  nat2fin n (sub (fin2nat (add m n) i) m)

(** val fin2PredRangePred : int -> fin -> fin **)

let fin2PredRangePred n i =
  nat2fin n (pred (fin2nat (Stdlib.Int.succ n) i))

(** val fin2SuccRangeSucc : int -> fin -> fin **)

let fin2SuccRangeSucc n i =
  nat2fin (Stdlib.Int.succ n) (Stdlib.Int.succ (fin2nat n i))

(** val finseq : int -> fin list **)

let finseq n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun n0 -> map (nat2finS n0) (seq 0 n))
    n

(** val seqfoldl : (int -> 'a1) -> int -> 'a2 -> ('a2 -> 'a1 -> 'a2) -> 'a2 **)

let rec seqfoldl s n b f =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> b)
    (fun n' -> seqfoldl s n' (f b (s n')) f)
    n

(** val seqfoldr : (int -> 'a1) -> int -> 'a2 -> ('a1 -> 'a2 -> 'a2) -> 'a2 **)

let rec seqfoldr s n b g =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> b)
    (fun n' -> seqfoldr s n' (g (s n') b) g)
    n

(** val seqsumAux : ('a1 -> 'a1 -> 'a1) -> int -> (int -> 'a1) -> 'a1 -> 'a1 **)

let rec seqsumAux aadd n f acc =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> acc)
    (fun n' -> seqsumAux aadd n' f (aadd (f n') acc))
    n

(** val seqsum : ('a1 -> 'a1 -> 'a1) -> 'a1 -> int -> (int -> 'a1) -> 'a1 **)

let seqsum aadd azero n f =
  seqsumAux aadd n f azero

(** val seqprodAux : ('a1 -> 'a1 -> 'a1) -> int -> (int -> 'a1) -> 'a1 -> 'a1 **)

let rec seqprodAux amul n f acc =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> acc)
    (fun n' -> seqprodAux amul n' f (amul (f n') acc))
    n

(** val seqprod : ('a1 -> 'a1 -> 'a1) -> 'a1 -> int -> (int -> 'a1) -> 'a1 **)

let seqprod amul aone n f =
  seqprodAux amul n f aone

module Coq__2 = struct
 type 'a vec = fin -> 'a
end
include Coq__2

(** val veq_dec : int -> 'a1 dec -> 'a1 vec dec **)

let rec veq_dec n aeqDec a b =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> true)
    (fun n0 ->
    let s =
      veq_dec n0 aeqDec (fun i -> a (nat2finS n0 (fin2nat n0 i))) (fun i ->
        b (nat2finS n0 (fin2nat n0 i)))
    in
    if s then aeqdec aeqDec (a (nat2finS n0 n0)) (b (nat2finS n0 n0)) else false)
    n

(** val vrepeat : int -> 'a1 -> 'a1 vec **)

let vrepeat _ a _ =
  a

(** val vzero : 'a1 -> int -> 'a1 vec **)

let vzero azero n =
  vrepeat n azero

(** val f2v : int -> (int -> 'a1) -> 'a1 vec **)

let f2v n f i =
  f (fin2nat n i)

(** val v2f : 'a1 -> int -> 'a1 vec -> int -> 'a1 **)

let v2f azero n a i =
  if nat_lt_Dec i n then a (nat2fin n i) else azero

module Coq__8 = struct
 (** val l2v : 'a1 -> int -> 'a1 list -> 'a1 vec **)

 let l2v azero n l i =
   nth (fin2nat n i) l azero
end
include Coq__8

module Coq__9 = struct
 (** val v2l : int -> 'a1 vec -> 'a1 list **)

 let v2l n a =
   map a (finseq n)
end
include Coq__9

(** val mkvec1 : 'a1 -> 'a1 -> 'a1 vec **)

let mkvec1 azero a1 =
  l2v azero (Stdlib.Int.succ 0) (a1 :: [])

(** val mkvec2 : 'a1 -> 'a1 -> 'a1 -> 'a1 vec **)

let mkvec2 azero a1 a2 =
  l2v azero (Stdlib.Int.succ (Stdlib.Int.succ 0)) (a1 :: (a2 :: []))

(** val mkvec3 : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 vec **)

let mkvec3 azero a1 a2 a3 =
  l2v azero (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
    (a1 :: (a2 :: (a3 :: [])))

(** val mkvec4 : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 vec **)

let mkvec4 azero a1 a2 a3 a4 =
  l2v azero (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))) (a1 :: (a2 :: (a3 :: (a4 :: []))))

module Coq__3 = struct
 (** val vmap : ('a1 -> 'a2) -> int -> 'a1 vec -> 'a2 vec **)

 let vmap f _ a i =
   f (a i)
end
include Coq__3

module Coq__4 = struct
 (** val vmap2 : ('a1 -> 'a2 -> 'a3) -> int -> 'a1 vec -> 'a2 vec -> 'a3 vec **)

 let vmap2 f _ a b i =
   f (a i) (b i)
end
include Coq__4

(** val veye : 'a1 -> 'a1 -> int -> fin -> 'a1 vec **)

let veye azero aone n i j =
  if nat_eq_Dec (fin2nat n i) (fin2nat n j) then aone else azero

(** val veyes : 'a1 -> 'a1 -> int -> 'a1 vec vec **)

let veyes =
  veye

(** val vhead : int -> 'a1 vec -> 'a1 **)

let vhead n a =
  a (fin0 n)

(** val vtail : int -> 'a1 vec -> 'a1 **)

let vtail n a =
  a (nat2finS n n)

(** val vheadN : int -> int -> 'a1 vec -> 'a1 vec **)

let vheadN m n a i =
  a (fin2AddRangeR m n i)

(** val vtailN : int -> int -> 'a1 vec -> 'a1 vec **)

let vtailN m n a i =
  a (fin2AddRangeAddL m n i)

(** val vset : int -> 'a1 vec -> fin -> 'a1 -> 'a1 vec **)

let vset n a i x j =
  if nat_eq_Dec (fin2nat n j) (fin2nat n i) then x else a j

(** val vswap : int -> 'a1 vec -> fin -> fin -> 'a1 vec **)

let vswap n a i j k =
  if nat_eq_Dec (fin2nat n k) (fin2nat n i)
  then a j
  else if nat_eq_Dec (fin2nat n k) (fin2nat n j) then a i else a k

(** val vinsert : int -> 'a1 vec -> fin -> 'a1 -> 'a1 vec **)

let vinsert n a i x j =
  let s =
    nat_lt_Dec (fin2nat (Stdlib.Int.succ n) j) (fin2nat (Stdlib.Int.succ n) i)
  in
  if s
  then a (fin2PredRange n j)
  else let s0 =
         nat_eq_Dec (fin2nat (Stdlib.Int.succ n) j)
           (fin2nat (Stdlib.Int.succ n) i)
       in
       if s0 then x else a (fin2PredRangePred n j)

(** val vremove : int -> 'a1 vec -> fin -> 'a1 vec **)

let vremove n a i j =
  if nat_lt_Dec (fin2nat n j) (fin2nat (Stdlib.Int.succ n) i)
  then a (fin2SuccRange n j)
  else a (fin2SuccRangeSucc n j)

(** val vremoveH : int -> 'a1 vec -> 'a1 vec **)

let vremoveH n a i =
  a (fin2SuccRangeSucc n i)

(** val vremoveT : int -> 'a1 vec -> 'a1 vec **)

let vremoveT n a i =
  a (fin2SuccRange n i)

(** val vremoveHN : int -> int -> 'a1 vec -> 'a1 vec **)

let vremoveHN m n a i =
  a (fin2AddRangeAddL m n i)

(** val vremoveTN : int -> int -> 'a1 vec -> 'a1 vec **)

let vremoveTN m n a i =
  a (fin2AddRangeR m n i)

(** val vconsH : int -> 'a1 -> 'a1 vec -> 'a1 vec **)

let vconsH n x a i =
  let s = nat_eq_Dec (fin2nat (Stdlib.Int.succ n) i) 0 in
  if s then x else a (fin2PredRangePred n i)

(** val vconsT : int -> 'a1 vec -> 'a1 -> 'a1 vec **)

let vconsT n a x i =
  let s = nat_lt_Dec (fin2nat (Stdlib.Int.succ n) i) n in
  if s then a (fin2PredRange n i) else x

(** val vapp : int -> int -> 'a1 vec -> 'a1 vec -> 'a1 vec **)

let vapp n m a b i =
  let s = nat_lt_Dec (fin2nat (add n m) i) n in
  if s then a (fin2AddRangeR' n m i) else b (fin2AddRangeAddL' n m i)

(** val vmem_dec : 'a1 dec -> int -> 'a1 vec -> 'a1 -> bool **)

let rec vmem_dec aeqDec n a x =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> false)
    (fun n0 ->
    let s = aeqdec aeqDec (vhead n0 a) x in
    if s then true else vmem_dec aeqDec n0 (vremoveH n0 a) x)
    n

(** val vmems_dec : 'a1 dec -> int -> int -> 'a1 vec -> 'a1 vec -> bool **)

let rec vmems_dec aeqDec r s a b =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> true)
    (fun n ->
    let iHr = vmems_dec aeqDec n s (vremoveH n a) b in
    if iHr then vmem_dec aeqDec s b (vhead n a) else false)
    r

(** val vequiv_dec : 'a1 dec -> int -> int -> 'a1 vec -> 'a1 vec -> bool **)

let vequiv_dec aeqDec r s a b =
  let s0 = vmems_dec aeqDec r s a b in
  if s0 then vmems_dec aeqDec s r b a else false

(** val vfoldl : 'a1 -> int -> 'a1 vec -> 'a2 -> ('a2 -> 'a1 -> 'a2) -> 'a2 **)

let vfoldl azero n a x f =
  seqfoldl (v2f azero n a) n x f

(** val vfoldr : 'a1 -> int -> 'a1 vec -> 'a2 -> ('a1 -> 'a2 -> 'a2) -> 'a2 **)

let vfoldr azero n a x f =
  seqfoldr (v2f azero n a) n x f

(** val vsum : ('a1 -> 'a1 -> 'a1) -> 'a1 -> int -> 'a1 vec -> 'a1 **)

let vsum aadd azero n a =
  seqsum aadd azero n (v2f azero n a)

(** val vadd : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 vec -> 'a1 vec -> 'a1 vec **)

let vadd =
  vmap2

(** val vopp : ('a1 -> 'a1) -> int -> 'a1 vec -> 'a1 vec **)

let vopp =
  vmap

(** val vcmul : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 -> 'a1 vec -> 'a1 vec **)

let vcmul amul n x a =
  vmap (fun y -> amul x y) n a

(** val vdot :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> int -> 'a1 vec -> 'a1
    vec -> 'a1 **)

let vdot aadd azero amul n a b =
  vsum aadd azero n (vmap2 amul n a b)

(** val vlen :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 ->
    RbaseSymbolsImpl.coq_R) -> int -> 'a1 vec -> RbaseSymbolsImpl.coq_R **)

let vlen aadd azero amul a2r0 n a =
  sqrt (a2r0 (vdot aadd azero amul n a a))

(** val vproj :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> int ->
    'a1 vec -> 'a1 vec -> 'a1 vec **)

let vproj aadd azero amul ainv n a b =
  vcmul amul n
    (amul (vdot aadd azero amul n a b) (ainv (vdot aadd azero amul n b b))) b

(** val vperp :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 ->
    'a1) -> int -> 'a1 vec -> 'a1 vec -> 'a1 vec **)

let vperp aadd azero aopp amul ainv n a b =
  vadd aadd n a (vopp aopp n (vproj aadd azero amul ainv n a b))

(** val mrow : int -> int -> 'a1 vec vec -> fin -> 'a1 vec **)

let mrow _ _ m =
  m

(** val mcol : int -> int -> 'a1 vec vec -> fin -> 'a1 vec **)

let mcol _ _ m j i =
  m i j

module Coq__12 = struct
 (** val mtrans : int -> int -> 'a1 vec vec -> 'a1 vec vec **)

 let mtrans _ _ m i j =
   m j i
end
include Coq__12

(** val mheadc : int -> int -> 'a1 vec vec -> 'a1 vec **)

let mheadc _ c m i =
  vhead c (m i)

(** val mtailc : int -> int -> 'a1 vec vec -> 'a1 vec **)

let mtailc _ c m i =
  vtail c (m i)

(** val cv2v : int -> 'a1 vec vec -> 'a1 vec **)

let cv2v _ m i =
  m i (fin0 0)

(** val v2cv : int -> 'a1 vec -> 'a1 vec vec **)

let v2cv _ a i _ =
  a i

(** val rv2v : int -> 'a1 vec vec -> 'a1 vec **)

let rv2v _ m i =
  m (fin0 0) i

(** val v2rv : int -> 'a1 vec -> 'a1 vec vec **)

let v2rv _ a _ =
  a

(** val mat0 : 'a1 -> int -> int -> 'a1 vec vec **)

let mat0 azero _ _ _ _ =
  azero

(** val m2rvl : int -> int -> 'a1 vec vec -> 'a1 vec list **)

let m2rvl r _ m =
  map m (finseq r)

(** val rvl2m : 'a1 -> int -> int -> 'a1 vec list -> 'a1 vec vec **)

let rvl2m azero r c l i =
  nth (fin2nat r i) l (vzero azero c)

(** val m2cvl : int -> int -> 'a1 vec vec -> 'a1 vec list **)

let m2cvl _ c m =
  map (fun i j -> m j i) (finseq c)

(** val cvl2m : 'a1 -> int -> int -> 'a1 vec list -> 'a1 vec vec **)

let cvl2m azero r c l i j =
  nth (fin2nat c j) l (vzero azero r) i

(** val f2m : int -> int -> (int -> int -> 'a1) -> 'a1 vec vec **)

let f2m r c f =
  f2v r (fun i -> f2v c (f i))

(** val m2f : 'a1 -> int -> int -> 'a1 vec vec -> int -> int -> 'a1 **)

let m2f azero r c m i =
  v2f azero c (v2f (vzero azero c) r m i)

module Coq__6 = struct
 (** val m2l : int -> int -> 'a1 vec vec -> 'a1 list list **)

 let m2l r c m =
   map (v2l c) (v2l r m)
end
include Coq__6

module Coq__5 = struct
 (** val l2m : 'a1 -> int -> int -> 'a1 list list -> 'a1 vec vec **)

 let l2m azero r c d =
   l2v (vzero azero c) r (map (l2v azero c) d)
end
include Coq__5

(** val mappr :
    'a1 -> int -> int -> int -> 'a1 vec vec -> 'a1 vec vec -> 'a1 vec vec **)

let mappr azero r1 r2 c m n =
  f2m (add r1 r2) c (fun i j ->
    if nat_lt_Dec i r1
    then m2f azero r1 c m i j
    else m2f azero r2 c n (sub i r1) j)

(** val mappc :
    'a1 -> int -> int -> int -> 'a1 vec vec -> 'a1 vec vec -> 'a1 vec vec **)

let mappc azero r c1 c2 m n =
  f2m r (add c1 c2) (fun i j ->
    if nat_lt_Dec j c1
    then m2f azero r c1 m i j
    else m2f azero r c2 n i (sub j c1))

(** val mkmat_0_c : 'a1 -> int -> 'a1 vec vec **)

let mkmat_0_c azero c =
  vzero (vzero azero c) 0

(** val mkmat_r_0 : 'a1 -> int -> 'a1 vec vec **)

let mkmat_r_0 azero r =
  vzero (vzero azero 0) r

(** val mkmat_1_c : int -> 'a1 vec -> 'a1 vec vec **)

let mkmat_1_c _ a _ =
  a

(** val mkmat_r_1 : int -> 'a1 vec -> 'a1 vec vec **)

let mkmat_r_1 _ a i _ =
  a i

(** val mkmat_1_1 : 'a1 -> 'a1 -> 'a1 vec vec **)

let mkmat_1_1 azero a11 =
  l2m azero (Stdlib.Int.succ 0) (Stdlib.Int.succ 0) ((a11 :: []) :: [])

(** val mkmat_1_2 : 'a1 -> 'a1 -> 'a1 -> 'a1 vec vec **)

let mkmat_1_2 azero a11 a12 =
  l2m azero (Stdlib.Int.succ 0) (Stdlib.Int.succ (Stdlib.Int.succ 0))
    ((a11 :: (a12 :: [])) :: [])

(** val mkmat_2_1 : 'a1 -> 'a1 -> 'a1 -> 'a1 vec vec **)

let mkmat_2_1 azero a11 a21 =
  l2m azero (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ 0)
    ((a11 :: []) :: ((a21 :: []) :: []))

(** val mkmat_2_2 : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 vec vec **)

let mkmat_2_2 azero a11 a12 a21 a22 =
  l2m azero (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
    (Stdlib.Int.succ 0)) ((a11 :: (a12 :: [])) :: ((a21 :: (a22 :: [])) :: []))

(** val mkmat_1_3 : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 vec vec **)

let mkmat_1_3 azero a11 a12 a13 =
  l2m azero (Stdlib.Int.succ 0) (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))) ((a11 :: (a12 :: (a13 :: []))) :: [])

(** val mkmat_3_1 : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 vec vec **)

let mkmat_3_1 azero a11 a21 a31 =
  l2m azero (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
    (Stdlib.Int.succ 0) ((a11 :: []) :: ((a21 :: []) :: ((a31 :: []) :: [])))

(** val mkmat_3_3 :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 vec
    vec **)

let mkmat_3_3 azero a11 a12 a13 a21 a22 a23 a31 a32 a33 =
  l2m azero (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
    ((a11 :: (a12 :: (a13 :: []))) :: ((a21 :: (a22 :: (a23 :: []))) :: ((a31 :: (a32 :: (a33 :: []))) :: [])))

(** val mkmat_1_4 : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 vec vec **)

let mkmat_1_4 azero a11 a12 a13 a14 =
  l2m azero (Stdlib.Int.succ 0) (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))
    ((a11 :: (a12 :: (a13 :: (a14 :: [])))) :: [])

(** val mkmat_4_1 : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 vec vec **)

let mkmat_4_1 azero a11 a21 a31 a41 =
  l2m azero (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))) (Stdlib.Int.succ 0)
    ((a11 :: []) :: ((a21 :: []) :: ((a31 :: []) :: ((a41 :: []) :: []))))

(** val mkmat_4_4 :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 vec vec **)

let mkmat_4_4 azero a11 a12 a13 a14 a21 a22 a23 a24 a31 a32 a33 a34 a41 a42 a43 a44 =
  l2m azero (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))
    ((a11 :: (a12 :: (a13 :: (a14 :: [])))) :: ((a21 :: (a22 :: (a23 :: (a24 :: [])))) :: ((a31 :: (a32 :: (a33 :: (a34 :: [])))) :: ((a41 :: (a42 :: (a43 :: (a44 :: [])))) :: []))))

(** val mdiagMk : 'a1 -> int -> 'a1 vec -> 'a1 vec vec **)

let mdiagMk azero n a i j =
  if nat_eq_Dec (fin2nat n i) (fin2nat n j) then a i else azero

(** val msetr : int -> int -> 'a1 vec vec -> 'a1 vec -> fin -> 'a1 vec vec **)

let msetr r _ m a i0 i j =
  if nat_eq_Dec (fin2nat r i) (fin2nat r i0) then a j else m i j

(** val msetc : int -> int -> 'a1 vec vec -> 'a1 vec -> fin -> 'a1 vec vec **)

let msetc _ c m a j0 i j =
  if nat_eq_Dec (fin2nat c j) (fin2nat c j0) then a i else m i j

(** val mremovecH : int -> int -> 'a1 vec vec -> 'a1 vec vec **)

let mremovecH _ c m i =
  vremoveH c (m i)

(** val mremovecT : int -> int -> 'a1 vec vec -> 'a1 vec vec **)

let mremovecT _ c m i =
  vremoveT c (m i)

(** val mconsrH : int -> int -> 'a1 vec -> 'a1 vec vec -> 'a1 vec vec **)

let mconsrH r _ a m =
  vconsH r a m

(** val mconsrT : int -> int -> 'a1 vec vec -> 'a1 vec -> 'a1 vec vec **)

let mconsrT r _ m a =
  vconsT r m a

(** val mconscH : int -> int -> 'a1 vec -> 'a1 vec vec -> 'a1 vec vec **)

let mconscH r c a m =
  vmap2 (vconsH c) r a m

(** val mconscT : int -> int -> 'a1 vec vec -> 'a1 vec -> 'a1 vec vec **)

let mconscT r c m a =
  vmap2 (vconsT c) r m a

(** val madd :
    ('a1 -> 'a1 -> 'a1) -> int -> int -> 'a1 vec vec -> 'a1 vec vec -> 'a1 vec vec **)

let madd aadd r c m n =
  vmap2 (vmap2 aadd c) r m n

module Coq__11 = struct
 (** val mat1 : 'a1 -> 'a1 -> int -> 'a1 vec vec **)

 let mat1 azero aone n i j =
   if nat_eq_Dec (fin2nat n i) (fin2nat n j) then aone else azero
end
include Coq__11

(** val mtrace : ('a1 -> 'a1 -> 'a1) -> 'a1 -> int -> 'a1 vec vec -> 'a1 **)

let mtrace aadd azero n m =
  vsum aadd azero n (fun i -> m i i)

(** val mopp : ('a1 -> 'a1) -> int -> int -> 'a1 vec vec -> 'a1 vec vec **)

let mopp aopp r c m =
  vmap (vmap aopp c) r m

(** val mcmul :
    ('a1 -> 'a1 -> 'a1) -> int -> int -> 'a1 -> 'a1 vec vec -> 'a1 vec vec **)

let mcmul amul r c a m =
  vmap (vmap (amul a) c) r m

module Coq__10 = struct
 (** val mmul :
     ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> int -> int -> int ->
     'a1 vec vec -> 'a1 vec vec -> 'a1 vec vec **)

 let mmul aadd azero amul _ c _ m n i j =
   vdot aadd azero amul c (m i) (fun k -> n k j)
end
include Coq__10

module Coq__7 = struct
 (** val mmulv :
     ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> int -> int -> 'a1 vec
     vec -> 'a1 vec -> 'a1 vec **)

 let mmulv aadd azero amul _ c m a i =
   vdot aadd azero amul c (m i) a
end
include Coq__7

(** val mvmul :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> int -> int -> 'a1 vec ->
    'a1 vec vec -> 'a1 vec **)

let mvmul aadd azero amul r c a m i =
  vdot aadd azero amul r a (mcol r c m i)

(** val mrowScale :
    ('a1 -> 'a1 -> 'a1) -> int -> fin -> 'a1 -> 'a1 vec vec -> 'a1 vec vec **)

let mrowScale amul n x c m i j =
  if nat_eq_Dec (fin2nat n i) (fin2nat n x) then amul c (m i j) else m i j

(** val mrowAdd :
    ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> int -> fin -> fin -> 'a1 -> 'a1
    vec vec -> 'a1 vec vec **)

let mrowAdd aadd amul n x y c m i j =
  if nat_eq_Dec (fin2nat n i) (fin2nat n x)
  then aadd (m i j) (amul c (m y j))
  else m i j

(** val mrowSwap : int -> fin -> fin -> 'a1 vec vec -> 'a1 vec vec **)

let mrowSwap n x y m i j =
  if nat_eq_Dec (fin2nat n i) (fin2nat n x)
  then m y j
  else if nat_eq_Dec (fin2nat n i) (fin2nat n y) then m x j else m i j

module Coq_method3 =
 struct
  (** val permOne : 'a1 -> 'a1 list -> 'a1 list list **)

  let rec permOne a l = match l with
  | [] -> (a :: []) :: []
  | hl :: tl -> (a :: l) :: (map (fun x -> hl :: x) (permOne a tl))

  (** val perm : 'a1 list -> 'a1 list list **)

  let rec perm = function
  | [] -> [] :: []
  | hl :: tl -> concat (map (permOne hl) (perm tl))
 end

(** val ronum1 : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> int **)

let ronum1 altb a l =
  fold_left (fun n b -> add n (if altb b a then Stdlib.Int.succ 0 else 0)) l 0

(** val ronum : ('a1 -> 'a1 -> bool) -> 'a1 list -> int **)

let rec ronum altb = function
| [] -> 0
| x :: l' -> add (ronum1 altb x l') (ronum altb l')

(** val mdet :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 ->
    int -> 'a1 vec vec -> 'a1 **)

let mdet aadd azero aopp amul aone n m =
  let colIds = Coq_method3.perm (seq 0 n) in
  let item = fun l ->
    let x = seqprod amul aone n (fun i -> m2f azero n n m i (nth i l 0)) in
    if odd (ronum Nat.ltb l) then aopp x else x
  in
  fold_left aadd (map item colIds) azero

(** val mdet1 : 'a1 vec vec -> 'a1 **)

let mdet1 m =
  m (nat2finS 0 0) (nat2finS 0 0)

(** val mdet2 :
    ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 vec vec ->
    'a1 **)

let mdet2 aadd aopp amul m =
  aadd
    (amul (m (nat2finS (Stdlib.Int.succ 0) 0) (nat2finS (Stdlib.Int.succ 0) 0))
      (m (nat2finS (Stdlib.Int.succ 0) (Stdlib.Int.succ 0))
        (nat2finS (Stdlib.Int.succ 0) (Stdlib.Int.succ 0))))
    (aopp
      (amul
        (m (nat2finS (Stdlib.Int.succ 0) 0)
          (nat2finS (Stdlib.Int.succ 0) (Stdlib.Int.succ 0)))
        (m (nat2finS (Stdlib.Int.succ 0) (Stdlib.Int.succ 0))
          (nat2finS (Stdlib.Int.succ 0) 0))))

(** val mdet3 :
    ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 vec vec ->
    'a1 **)

let mdet3 aadd aopp amul m =
  aadd
    (aadd
      (aadd
        (aadd
          (aadd
            (amul
              (amul
                (m (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) 0)
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) 0))
                (m
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0))
                    (Stdlib.Int.succ 0))
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0))
                    (Stdlib.Int.succ 0))))
              (m
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
                  (Stdlib.Int.succ 0)))
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
                  (Stdlib.Int.succ 0)))))
            (aopp
              (amul
                (amul
                  (m (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) 0)
                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) 0))
                  (m
                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0))
                      (Stdlib.Int.succ 0))
                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0))
                      (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
                (m
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0))
                    (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0))
                    (Stdlib.Int.succ 0))))))
          (aopp
            (amul
              (amul
                (m (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) 0)
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0))
                    (Stdlib.Int.succ 0)))
                (m
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0))
                    (Stdlib.Int.succ 0))
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) 0)))
              (m
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
                  (Stdlib.Int.succ 0)))
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
                  (Stdlib.Int.succ 0)))))))
        (amul
          (amul
            (m (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) 0)
              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ 0)))
            (m
              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ 0))
              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
                (Stdlib.Int.succ 0)))))
          (m
            (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
              (Stdlib.Int.succ 0)))
            (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) 0))))
      (amul
        (amul
          (m (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) 0)
            (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
              (Stdlib.Int.succ 0))))
          (m (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ 0))
            (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) 0)))
        (m
          (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
            (Stdlib.Int.succ 0)))
          (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ 0)))))
    (aopp
      (amul
        (amul
          (m (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) 0)
            (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
              (Stdlib.Int.succ 0))))
          (m (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ 0))
            (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ 0))))
        (m
          (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
            (Stdlib.Int.succ 0)))
          (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) 0))))

(** val mdet4 :
    ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 vec vec ->
    'a1 **)

let mdet4 aadd aopp amul m =
  aadd
    (aadd
      (aadd
        (aadd
          (aadd
            (aadd
              (aadd
                (aadd
                  (aadd
                    (aadd
                      (aadd
                        (aadd
                          (aadd
                            (aadd
                              (aadd
                                (aadd
                                  (aadd
                                    (aadd
                                      (aadd
                                        (aadd
                                          (aadd
                                            (aadd
                                              (aadd
                                                (amul
                                                  (amul
                                                    (amul
                                                      (m
                                                        (nat2finS
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ 0))) 0)
                                                        (nat2finS
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ 0))) 0))
                                                      (m
                                                        (nat2finS
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ 0)))
                                                          (Stdlib.Int.succ 0))
                                                        (nat2finS
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ 0)))
                                                          (Stdlib.Int.succ 0))))
                                                    (m
                                                      (nat2finS (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ 0)))
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ 0)))
                                                      (nat2finS (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ 0)))
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ 0)))))
                                                  (m
                                                    (nat2finS (Stdlib.Int.succ
                                                      (Stdlib.Int.succ
                                                      (Stdlib.Int.succ 0)))
                                                      (Stdlib.Int.succ
                                                      (Stdlib.Int.succ
                                                      (Stdlib.Int.succ 0))))
                                                    (nat2finS (Stdlib.Int.succ
                                                      (Stdlib.Int.succ
                                                      (Stdlib.Int.succ 0)))
                                                      (Stdlib.Int.succ
                                                      (Stdlib.Int.succ
                                                      (Stdlib.Int.succ 0))))))
                                                (aopp
                                                  (amul
                                                    (amul
                                                      (amul
                                                        (m
                                                          (nat2finS
                                                            (Stdlib.Int.succ
                                                            (Stdlib.Int.succ
                                                            (Stdlib.Int.succ 0)))
                                                            0)
                                                          (nat2finS
                                                            (Stdlib.Int.succ
                                                            (Stdlib.Int.succ
                                                            (Stdlib.Int.succ 0)))
                                                            0))
                                                        (m
                                                          (nat2finS
                                                            (Stdlib.Int.succ
                                                            (Stdlib.Int.succ
                                                            (Stdlib.Int.succ 0)))
                                                            (Stdlib.Int.succ 0))
                                                          (nat2finS
                                                            (Stdlib.Int.succ
                                                            (Stdlib.Int.succ
                                                            (Stdlib.Int.succ 0)))
                                                            (Stdlib.Int.succ 0))))
                                                      (m
                                                        (nat2finS
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ 0)))
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ 0)))
                                                        (nat2finS
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ 0)))
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ 0))))))
                                                    (m
                                                      (nat2finS (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ 0)))
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ 0))))
                                                      (nat2finS (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ 0)))
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ 0)))))))
                                              (aopp
                                                (amul
                                                  (amul
                                                    (amul
                                                      (m
                                                        (nat2finS
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ 0))) 0)
                                                        (nat2finS
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ 0))) 0))
                                                      (m
                                                        (nat2finS
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ 0)))
                                                          (Stdlib.Int.succ 0))
                                                        (nat2finS
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ 0)))
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ 0)))))
                                                    (m
                                                      (nat2finS (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ 0)))
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ 0)))
                                                      (nat2finS (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ 0)))
                                                        (Stdlib.Int.succ 0))))
                                                  (m
                                                    (nat2finS (Stdlib.Int.succ
                                                      (Stdlib.Int.succ
                                                      (Stdlib.Int.succ 0)))
                                                      (Stdlib.Int.succ
                                                      (Stdlib.Int.succ
                                                      (Stdlib.Int.succ 0))))
                                                    (nat2finS (Stdlib.Int.succ
                                                      (Stdlib.Int.succ
                                                      (Stdlib.Int.succ 0)))
                                                      (Stdlib.Int.succ
                                                      (Stdlib.Int.succ
                                                      (Stdlib.Int.succ 0))))))))
                                            (amul
                                              (amul
                                                (amul
                                                  (m
                                                    (nat2finS (Stdlib.Int.succ
                                                      (Stdlib.Int.succ
                                                      (Stdlib.Int.succ 0))) 0)
                                                    (nat2finS (Stdlib.Int.succ
                                                      (Stdlib.Int.succ
                                                      (Stdlib.Int.succ 0))) 0))
                                                  (m
                                                    (nat2finS (Stdlib.Int.succ
                                                      (Stdlib.Int.succ
                                                      (Stdlib.Int.succ 0)))
                                                      (Stdlib.Int.succ 0))
                                                    (nat2finS (Stdlib.Int.succ
                                                      (Stdlib.Int.succ
                                                      (Stdlib.Int.succ 0)))
                                                      (Stdlib.Int.succ
                                                      (Stdlib.Int.succ 0)))))
                                                (m
                                                  (nat2finS (Stdlib.Int.succ
                                                    (Stdlib.Int.succ
                                                    (Stdlib.Int.succ 0)))
                                                    (Stdlib.Int.succ
                                                    (Stdlib.Int.succ 0)))
                                                  (nat2finS (Stdlib.Int.succ
                                                    (Stdlib.Int.succ
                                                    (Stdlib.Int.succ 0)))
                                                    (Stdlib.Int.succ
                                                    (Stdlib.Int.succ
                                                    (Stdlib.Int.succ 0))))))
                                              (m
                                                (nat2finS (Stdlib.Int.succ
                                                  (Stdlib.Int.succ
                                                  (Stdlib.Int.succ 0)))
                                                  (Stdlib.Int.succ
                                                  (Stdlib.Int.succ
                                                  (Stdlib.Int.succ 0))))
                                                (nat2finS (Stdlib.Int.succ
                                                  (Stdlib.Int.succ
                                                  (Stdlib.Int.succ 0)))
                                                  (Stdlib.Int.succ 0)))))
                                          (amul
                                            (amul
                                              (amul
                                                (m
                                                  (nat2finS (Stdlib.Int.succ
                                                    (Stdlib.Int.succ
                                                    (Stdlib.Int.succ 0))) 0)
                                                  (nat2finS (Stdlib.Int.succ
                                                    (Stdlib.Int.succ
                                                    (Stdlib.Int.succ 0))) 0))
                                                (m
                                                  (nat2finS (Stdlib.Int.succ
                                                    (Stdlib.Int.succ
                                                    (Stdlib.Int.succ 0)))
                                                    (Stdlib.Int.succ 0))
                                                  (nat2finS (Stdlib.Int.succ
                                                    (Stdlib.Int.succ
                                                    (Stdlib.Int.succ 0)))
                                                    (Stdlib.Int.succ
                                                    (Stdlib.Int.succ
                                                    (Stdlib.Int.succ 0))))))
                                              (m
                                                (nat2finS (Stdlib.Int.succ
                                                  (Stdlib.Int.succ
                                                  (Stdlib.Int.succ 0)))
                                                  (Stdlib.Int.succ
                                                  (Stdlib.Int.succ 0)))
                                                (nat2finS (Stdlib.Int.succ
                                                  (Stdlib.Int.succ
                                                  (Stdlib.Int.succ 0)))
                                                  (Stdlib.Int.succ 0))))
                                            (m
                                              (nat2finS (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))) (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))))
                                              (nat2finS (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))) (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0))))))
                                        (aopp
                                          (amul
                                            (amul
                                              (amul
                                                (m
                                                  (nat2finS (Stdlib.Int.succ
                                                    (Stdlib.Int.succ
                                                    (Stdlib.Int.succ 0))) 0)
                                                  (nat2finS (Stdlib.Int.succ
                                                    (Stdlib.Int.succ
                                                    (Stdlib.Int.succ 0))) 0))
                                                (m
                                                  (nat2finS (Stdlib.Int.succ
                                                    (Stdlib.Int.succ
                                                    (Stdlib.Int.succ 0)))
                                                    (Stdlib.Int.succ 0))
                                                  (nat2finS (Stdlib.Int.succ
                                                    (Stdlib.Int.succ
                                                    (Stdlib.Int.succ 0)))
                                                    (Stdlib.Int.succ
                                                    (Stdlib.Int.succ
                                                    (Stdlib.Int.succ 0))))))
                                              (m
                                                (nat2finS (Stdlib.Int.succ
                                                  (Stdlib.Int.succ
                                                  (Stdlib.Int.succ 0)))
                                                  (Stdlib.Int.succ
                                                  (Stdlib.Int.succ 0)))
                                                (nat2finS (Stdlib.Int.succ
                                                  (Stdlib.Int.succ
                                                  (Stdlib.Int.succ 0)))
                                                  (Stdlib.Int.succ
                                                  (Stdlib.Int.succ 0)))))
                                            (m
                                              (nat2finS (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))) (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))))
                                              (nat2finS (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))) (Stdlib.Int.succ 0))))))
                                      (aopp
                                        (amul
                                          (amul
                                            (amul
                                              (m
                                                (nat2finS (Stdlib.Int.succ
                                                  (Stdlib.Int.succ
                                                  (Stdlib.Int.succ 0))) 0)
                                                (nat2finS (Stdlib.Int.succ
                                                  (Stdlib.Int.succ
                                                  (Stdlib.Int.succ 0)))
                                                  (Stdlib.Int.succ 0)))
                                              (m
                                                (nat2finS (Stdlib.Int.succ
                                                  (Stdlib.Int.succ
                                                  (Stdlib.Int.succ 0)))
                                                  (Stdlib.Int.succ 0))
                                                (nat2finS (Stdlib.Int.succ
                                                  (Stdlib.Int.succ
                                                  (Stdlib.Int.succ 0))) 0)))
                                            (m
                                              (nat2finS (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))) (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0)))
                                              (nat2finS (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))) (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0)))))
                                          (m
                                            (nat2finS (Stdlib.Int.succ
                                              (Stdlib.Int.succ (Stdlib.Int.succ
                                              0))) (Stdlib.Int.succ
                                              (Stdlib.Int.succ (Stdlib.Int.succ
                                              0))))
                                            (nat2finS (Stdlib.Int.succ
                                              (Stdlib.Int.succ (Stdlib.Int.succ
                                              0))) (Stdlib.Int.succ
                                              (Stdlib.Int.succ (Stdlib.Int.succ
                                              0))))))))
                                    (amul
                                      (amul
                                        (amul
                                          (m
                                            (nat2finS (Stdlib.Int.succ
                                              (Stdlib.Int.succ (Stdlib.Int.succ
                                              0))) 0)
                                            (nat2finS (Stdlib.Int.succ
                                              (Stdlib.Int.succ (Stdlib.Int.succ
                                              0))) (Stdlib.Int.succ 0)))
                                          (m
                                            (nat2finS (Stdlib.Int.succ
                                              (Stdlib.Int.succ (Stdlib.Int.succ
                                              0))) (Stdlib.Int.succ 0))
                                            (nat2finS (Stdlib.Int.succ
                                              (Stdlib.Int.succ (Stdlib.Int.succ
                                              0))) 0)))
                                        (m
                                          (nat2finS (Stdlib.Int.succ
                                            (Stdlib.Int.succ (Stdlib.Int.succ
                                            0))) (Stdlib.Int.succ
                                            (Stdlib.Int.succ 0)))
                                          (nat2finS (Stdlib.Int.succ
                                            (Stdlib.Int.succ (Stdlib.Int.succ
                                            0))) (Stdlib.Int.succ
                                            (Stdlib.Int.succ (Stdlib.Int.succ
                                            0))))))
                                      (m
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ 0))))
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                                  (amul
                                    (amul
                                      (amul
                                        (m
                                          (nat2finS (Stdlib.Int.succ
                                            (Stdlib.Int.succ (Stdlib.Int.succ
                                            0))) 0)
                                          (nat2finS (Stdlib.Int.succ
                                            (Stdlib.Int.succ (Stdlib.Int.succ
                                            0))) (Stdlib.Int.succ 0)))
                                        (m
                                          (nat2finS (Stdlib.Int.succ
                                            (Stdlib.Int.succ (Stdlib.Int.succ
                                            0))) (Stdlib.Int.succ 0))
                                          (nat2finS (Stdlib.Int.succ
                                            (Stdlib.Int.succ (Stdlib.Int.succ
                                            0))) (Stdlib.Int.succ
                                            (Stdlib.Int.succ 0)))))
                                      (m
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          0)))
                                    (m
                                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ 0))))
                                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))
                                (aopp
                                  (amul
                                    (amul
                                      (amul
                                        (m
                                          (nat2finS (Stdlib.Int.succ
                                            (Stdlib.Int.succ (Stdlib.Int.succ
                                            0))) 0)
                                          (nat2finS (Stdlib.Int.succ
                                            (Stdlib.Int.succ (Stdlib.Int.succ
                                            0))) (Stdlib.Int.succ 0)))
                                        (m
                                          (nat2finS (Stdlib.Int.succ
                                            (Stdlib.Int.succ (Stdlib.Int.succ
                                            0))) (Stdlib.Int.succ 0))
                                          (nat2finS (Stdlib.Int.succ
                                            (Stdlib.Int.succ (Stdlib.Int.succ
                                            0))) (Stdlib.Int.succ
                                            (Stdlib.Int.succ 0)))))
                                      (m
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ 0))))))
                                    (m
                                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ 0))))
                                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ 0))) 0)))))
                              (aopp
                                (amul
                                  (amul
                                    (amul
                                      (m
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          0)
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          (Stdlib.Int.succ 0)))
                                      (m
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          (Stdlib.Int.succ 0))
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ 0))))))
                                    (m
                                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ
                                        (Stdlib.Int.succ 0)))
                                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ 0))) 0)))
                                  (m
                                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ 0))) (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ 0))))
                                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ 0))) (Stdlib.Int.succ
                                      (Stdlib.Int.succ 0)))))))
                            (amul
                              (amul
                                (amul
                                  (m
                                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ 0))) 0)
                                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0)))
                                  (m
                                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0))
                                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ 0))) (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                                (m
                                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ 0))) (Stdlib.Int.succ
                                    (Stdlib.Int.succ 0)))
                                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ 0))) (Stdlib.Int.succ
                                    (Stdlib.Int.succ 0)))))
                              (m
                                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ 0))) (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ 0))))
                                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ 0))) 0))))
                          (amul
                            (amul
                              (amul
                                (m
                                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ 0))) 0)
                                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ 0))) (Stdlib.Int.succ
                                    (Stdlib.Int.succ 0))))
                                (m
                                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0))
                                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ 0))) 0)))
                              (m
                                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ 0))) (Stdlib.Int.succ
                                  (Stdlib.Int.succ 0)))
                                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0))))
                            (m
                              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                (Stdlib.Int.succ 0))) (Stdlib.Int.succ
                                (Stdlib.Int.succ (Stdlib.Int.succ 0))))
                              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                (Stdlib.Int.succ 0))) (Stdlib.Int.succ
                                (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))
                        (aopp
                          (amul
                            (amul
                              (amul
                                (m
                                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ 0))) 0)
                                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ 0))) (Stdlib.Int.succ
                                    (Stdlib.Int.succ 0))))
                                (m
                                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0))
                                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ 0))) 0)))
                              (m
                                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ 0))) (Stdlib.Int.succ
                                  (Stdlib.Int.succ 0)))
                                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ 0))) (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                            (m
                              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                (Stdlib.Int.succ 0))) (Stdlib.Int.succ
                                (Stdlib.Int.succ (Stdlib.Int.succ 0))))
                              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0))))))
                      (aopp
                        (amul
                          (amul
                            (amul
                              (m
                                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ 0))) 0)
                                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ 0))) (Stdlib.Int.succ
                                  (Stdlib.Int.succ 0))))
                              (m
                                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0))
                                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0))))
                            (m
                              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                (Stdlib.Int.succ 0))) (Stdlib.Int.succ
                                (Stdlib.Int.succ 0)))
                              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                (Stdlib.Int.succ 0))) 0)))
                          (m
                            (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                              (Stdlib.Int.succ 0))) (Stdlib.Int.succ
                              (Stdlib.Int.succ (Stdlib.Int.succ 0))))
                            (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                              (Stdlib.Int.succ 0))) (Stdlib.Int.succ
                              (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))
                    (amul
                      (amul
                        (amul
                          (m
                            (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                              (Stdlib.Int.succ 0))) 0)
                            (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                              (Stdlib.Int.succ 0))) (Stdlib.Int.succ
                              (Stdlib.Int.succ 0))))
                          (m
                            (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                              (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0))
                            (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                              (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0))))
                        (m
                          (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ 0))) (Stdlib.Int.succ
                            (Stdlib.Int.succ 0)))
                          (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ 0))) (Stdlib.Int.succ
                            (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                      (m
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))))
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) 0))))
                  (amul
                    (amul
                      (amul
                        (m
                          (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ 0))) 0)
                          (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ 0))) (Stdlib.Int.succ
                            (Stdlib.Int.succ 0))))
                        (m
                          (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0))
                          (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ 0))) (Stdlib.Int.succ
                            (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                      (m
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                          0)))
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) 0)))
                    (m
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))))
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0)))))
                (aopp
                  (amul
                    (amul
                      (amul
                        (m
                          (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ 0))) 0)
                          (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ 0))) (Stdlib.Int.succ
                            (Stdlib.Int.succ 0))))
                        (m
                          (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0))
                          (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ 0))) (Stdlib.Int.succ
                            (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                      (m
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                          0)))
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0))))
                    (m
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))))
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) 0)))))
              (aopp
                (amul
                  (amul
                    (amul
                      (m
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) 0)
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0)))))
                      (m
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0))
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) 0)))
                    (m
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                        0)))
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0))))
                  (m
                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))))
                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))) (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))
            (amul
              (amul
                (amul
                  (m
                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))) 0)
                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0)))))
                  (m
                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))) (Stdlib.Int.succ 0))
                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))) 0)))
                (m
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
              (m
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (Stdlib.Int.succ 0)))))
          (amul
            (amul
              (amul
                (m
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) 0)
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
                (m
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ 0))
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ 0))))
              (m
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  0)))
            (m
              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))
              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
        (aopp
          (amul
            (amul
              (amul
                (m
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) 0)
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
                (m
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ 0))
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ 0))))
              (m
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
            (m
              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))
              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))) 0)))))
      (aopp
        (amul
          (amul
            (amul
              (m
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  0)
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
              (m
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (Stdlib.Int.succ 0))
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
            (m
              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                (Stdlib.Int.succ (Stdlib.Int.succ 0)))
              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))) 0)))
          (m
            (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
              (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))
            (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
              (Stdlib.Int.succ 0))))))
    (amul
      (amul
        (amul
          (m (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))) 0)
            (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
              (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
          (m
            (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
              (Stdlib.Int.succ 0))
            (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
              (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
        (m
          (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
            (Stdlib.Int.succ (Stdlib.Int.succ 0)))
          (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
            (Stdlib.Int.succ 0))))
      (m
        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))
        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))) 0)))

(** val msubmat : int -> 'a1 vec vec -> fin -> fin -> 'a1 vec vec **)

let msubmat n m i j i0 j0 =
  let i1 =
    if nat_lt_Dec (fin2nat n i0) (fin2nat (Stdlib.Int.succ n) i)
    then fin2SuccRange n i0
    else fin2SuccRangeSucc n i0
  in
  let j1 =
    if nat_lt_Dec (fin2nat n j0) (fin2nat (Stdlib.Int.succ n) j)
    then fin2SuccRange n j0
    else fin2SuccRangeSucc n j0
  in
  m i1 j1

(** val mdetEx :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 ->
    int -> 'a1 vec vec -> 'a1 **)

let rec mdetEx aadd azero aopp amul aone n m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> aone)
    (fun n' ->
    vsum aadd azero (Stdlib.Int.succ n') (fun j ->
      let a =
        if Nat.even (fin2nat (Stdlib.Int.succ n') j)
        then m (nat2finS n' 0) j
        else aopp (m (nat2finS n' 0) j)
      in
      let d = mdetEx aadd azero aopp amul aone n' (msubmat n' m (nat2finS n' 0) j)
      in
      amul a d))
    n

(** val mcofactorEx :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 ->
    int -> 'a1 vec vec -> fin -> fin -> 'a1 **)

let mcofactorEx aadd azero aopp amul aone n m i j =
  let x = mdetEx aadd azero aopp amul aone n (msubmat n m i j) in
  if Nat.even
       (add (fin2nat (Stdlib.Int.succ n) i) (fin2nat (Stdlib.Int.succ n) j))
  then x
  else aopp x

(** val madj :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 ->
    int -> 'a1 vec vec -> 'a1 vec vec **)

let madj aadd azero aopp amul aone n m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> m)
    (fun n' i j -> mcofactorEx aadd azero aopp amul aone n' m j i)
    n

(** val cramerRule :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 ->
    ('a1 -> 'a1) -> int -> 'a1 vec vec -> 'a1 vec -> 'a1 vec **)

let cramerRule aadd azero aopp amul aone ainv n c b i =
  amul (mdetEx aadd azero aopp amul aone n (msetc n n c b i))
    (ainv (mdetEx aadd azero aopp amul aone n c))

(** val cramerRuleList :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 ->
    ('a1 -> 'a1) -> int -> 'a1 list list -> 'a1 list -> 'a1 list **)

let cramerRuleList aadd azero aopp amul aone ainv n lC lb =
  let c = l2m azero n n lC in
  let b = l2v azero n lb in
  let x = cramerRule aadd azero aopp amul aone ainv n c b in v2l n x

module OrderedElementTypeR =
 struct
  (** val coq_Order : RbaseSymbolsImpl.coq_R order **)

  let coq_Order =
    r_Order
 end

module OrderedRingElementTypeR =
 struct
  (** val coq_Order : RbaseSymbolsImpl.coq_R order **)

  let coq_Order =
    OrderedElementTypeR.coq_Order

  (** val coq_OrderedARing : RbaseSymbolsImpl.coq_R orderedARing **)

  let coq_OrderedARing =
    coq_Order
 end

module OrderedFieldElementTypeR =
 struct
  (** val coq_Order : RbaseSymbolsImpl.coq_R order **)

  let coq_Order =
    OrderedElementTypeR.coq_Order

  (** val coq_OrderedARing : RbaseSymbolsImpl.coq_R orderedARing **)

  let coq_OrderedARing =
    OrderedRingElementTypeR.coq_OrderedARing

  (** val coq_OrderedAField : RbaseSymbolsImpl.coq_R orderedField **)

  let coq_OrderedAField =
    OrderedRingElementTypeR.coq_OrderedARing
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

module NormedOrderedFieldElementTypeR =
 struct
  type coq_A = RbaseSymbolsImpl.coq_R

  (** val coq_Azero : coq_A **)

  let coq_Azero =
    iZR Z0

  (** val coq_AeqDec : coq_A dec **)

  let coq_AeqDec =
    r_eq_Dec

  (** val coq_Aadd :
      RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

  let coq_Aadd =
    RbaseSymbolsImpl.coq_Rplus

  (** val coq_Aone : coq_A **)

  let coq_Aone =
    iZR (Zpos XH)

  (** val coq_Aopp : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

  let coq_Aopp =
    RbaseSymbolsImpl.coq_Ropp

  (** val coq_Amul :
      RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

  let coq_Amul =
    RbaseSymbolsImpl.coq_Rmult

  (** val coq_Ainv : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

  let coq_Ainv =
    RinvImpl.coq_Rinv

  (** val coq_Altb : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool **)

  let coq_Altb =
    rltb

  (** val coq_Aleb : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool **)

  let coq_Aleb =
    rleb

  (** val coq_Order : RbaseSymbolsImpl.coq_R order **)

  let coq_Order =
    OrderedFieldElementTypeR.coq_Order

  (** val coq_OrderedARing : RbaseSymbolsImpl.coq_R orderedARing **)

  let coq_OrderedARing =
    OrderedFieldElementTypeR.coq_OrderedARing

  (** val coq_OrderedAField : RbaseSymbolsImpl.coq_R orderedField **)

  let coq_OrderedAField =
    OrderedFieldElementTypeR.coq_OrderedAField

  (** val a2r : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

  let a2r =
    id

  (** val coq_ConvertToR : RbaseSymbolsImpl.coq_R convertToR **)

  let coq_ConvertToR =
    r_ConvertToR
 end

(** val minvtbleb :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 ->
    'a1 dec -> int -> 'a1 vec vec -> bool **)

let minvtbleb aadd azero aopp amul aone aeqDec n m =
  if aeqdec aeqDec (mdetEx aadd azero aopp amul aone n m) azero
  then false
  else true

(** val minvo :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 ->
    ('a1 -> 'a1) -> 'a1 dec -> int -> 'a1 vec vec -> 'a1 vec vec option **)

let minvo aadd azero aopp amul aone ainv aeqDec n m =
  if minvtbleb aadd azero aopp amul aone aeqDec n m
  then Some
         (mcmul amul n n (ainv (mdetEx aadd azero aopp amul aone n m))
           (madj aadd azero aopp amul aone n m))
  else None

(** val minv :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 ->
    ('a1 -> 'a1) -> 'a1 dec -> int -> 'a1 vec vec -> 'a1 vec vec **)

let minv aadd azero aopp amul aone ainv aeqDec n m =
  if minvtbleb aadd azero aopp amul aone aeqDec n m
  then mcmul amul n n (ainv (mdetEx aadd azero aopp amul aone n m))
         (madj aadd azero aopp amul aone n m)
  else mat1 azero aone n

(** val minvNoCheck :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 ->
    ('a1 -> 'a1) -> int -> 'a1 vec vec -> 'a1 vec vec **)

let minvNoCheck aadd azero aopp amul aone ainv n m =
  mcmul amul n n (ainv (mdetEx aadd azero aopp amul aone n m))
    (madj aadd azero aopp amul aone n m)

(** val minvElement :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 ->
    ('a1 -> 'a1) -> int -> 'a1 vec vec -> fin -> fin -> 'a1 **)

let minvElement aadd azero aopp amul aone ainv n m i j =
  amul (ainv (mdetEx aadd azero aopp amul aone (Stdlib.Int.succ n) m))
    (mcofactorEx aadd azero aopp amul aone n m j i)

(** val minv1 :
    'a1 -> ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> 'a1 vec vec -> 'a1 vec
    vec **)

let minv1 azero amul aone ainv m =
  l2m azero (Stdlib.Int.succ 0) (Stdlib.Int.succ 0)
    (((amul aone (ainv (m (nat2finS 0 0) (nat2finS 0 0)))) :: []) :: [])

(** val minv2 :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 ->
    'a1) -> 'a1 vec vec -> 'a1 vec vec **)

let minv2 aadd azero aopp amul ainv m =
  mcmul amul (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
    (Stdlib.Int.succ 0)) (ainv (mdet2 aadd aopp amul m))
    (l2m azero (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
      (Stdlib.Int.succ 0))
      (((m (nat2finS (Stdlib.Int.succ 0) (Stdlib.Int.succ 0))
          (nat2finS (Stdlib.Int.succ 0) (Stdlib.Int.succ 0))) :: ((aopp
                                                                    (m
                                                                      (nat2finS
                                                                        (Stdlib.Int.succ
                                                                        0) 0)
                                                                      (nat2finS
                                                                        (Stdlib.Int.succ
                                                                        0)
                                                                        (Stdlib.Int.succ
                                                                        0)))) :: [])) :: ((
      (aopp
        (m (nat2finS (Stdlib.Int.succ 0) (Stdlib.Int.succ 0))
          (nat2finS (Stdlib.Int.succ 0) 0))) :: ((m
                                                   (nat2finS (Stdlib.Int.succ 0)
                                                     0)
                                                   (nat2finS (Stdlib.Int.succ 0)
                                                     0)) :: [])) :: [])))

(** val minv3 :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 ->
    'a1) -> 'a1 vec vec -> 'a1 vec vec **)

let minv3 aadd azero aopp amul ainv m =
  mcmul amul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
    (ainv (mdet3 aadd aopp amul m))
    (l2m azero (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
      (((aadd
          (amul
            (m
              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ 0))
              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ 0)))
            (m
              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
                (Stdlib.Int.succ 0)))
              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
                (Stdlib.Int.succ 0)))))
          (aopp
            (amul
              (m
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
                  0))
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
                  (Stdlib.Int.succ 0))))
              (m
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
                  (Stdlib.Int.succ 0)))
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
                  0)))))) :: ((aopp
                                (aadd
                                  (amul
                                    (m
                                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                        0)) 0)
                                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                        0)) (Stdlib.Int.succ 0)))
                                    (m
                                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                        0)) (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                        0)) (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
                                  (aopp
                                    (amul
                                      (m
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ 0)) 0)
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ 0)) (Stdlib.Int.succ
                                          (Stdlib.Int.succ 0))))
                                      (m
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ 0)) (Stdlib.Int.succ
                                          (Stdlib.Int.succ 0)))
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ 0)) (Stdlib.Int.succ
                                          0))))))) :: ((aadd
                                                         (amul
                                                           (m
                                                             (nat2finS
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               0)) 0)
                                                             (nat2finS
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               0))
                                                               (Stdlib.Int.succ
                                                               0)))
                                                           (m
                                                             (nat2finS
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               0))
                                                               (Stdlib.Int.succ
                                                               0))
                                                             (nat2finS
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               0))
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               0)))))
                                                         (aopp
                                                           (amul
                                                             (m
                                                               (nat2finS
                                                                 (Stdlib.Int.succ
                                                                 (Stdlib.Int.succ
                                                                 0)) 0)
                                                               (nat2finS
                                                                 (Stdlib.Int.succ
                                                                 (Stdlib.Int.succ
                                                                 0))
                                                                 (Stdlib.Int.succ
                                                                 (Stdlib.Int.succ
                                                                 0))))
                                                             (m
                                                               (nat2finS
                                                                 (Stdlib.Int.succ
                                                                 (Stdlib.Int.succ
                                                                 0))
                                                                 (Stdlib.Int.succ
                                                                 0))
                                                               (nat2finS
                                                                 (Stdlib.Int.succ
                                                                 (Stdlib.Int.succ
                                                                 0))
                                                                 (Stdlib.Int.succ
                                                                 0)))))) :: []))) :: ((
      (aopp
        (aadd
          (amul
            (m
              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ 0))
              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) 0))
            (m
              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
                (Stdlib.Int.succ 0)))
              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
                (Stdlib.Int.succ 0)))))
          (aopp
            (amul
              (m
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
                  0))
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
                  (Stdlib.Int.succ 0))))
              (m
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
                  (Stdlib.Int.succ 0)))
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) 0)))))) :: (
      (aadd
        (amul
          (m (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) 0)
            (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) 0))
          (m
            (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
              (Stdlib.Int.succ 0)))
            (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
              (Stdlib.Int.succ 0)))))
        (aopp
          (amul
            (m (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) 0)
              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
                (Stdlib.Int.succ 0))))
            (m
              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
                (Stdlib.Int.succ 0)))
              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) 0))))) :: (
      (aopp
        (aadd
          (amul
            (m (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) 0)
              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) 0))
            (m
              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ 0))
              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
                (Stdlib.Int.succ 0)))))
          (aopp
            (amul
              (m (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) 0)
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
                  (Stdlib.Int.succ 0))))
              (m
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
                  0)) (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) 0)))))) :: []))) :: ((
      (aadd
        (amul
          (m (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ 0))
            (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) 0))
          (m
            (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
              (Stdlib.Int.succ 0)))
            (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ 0))))
        (aopp
          (amul
            (m
              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ 0))
              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ 0)))
            (m
              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
                (Stdlib.Int.succ 0)))
              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) 0))))) :: (
      (aopp
        (aadd
          (amul
            (m (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) 0)
              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) 0))
            (m
              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
                (Stdlib.Int.succ 0)))
              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ 0))))
          (aopp
            (amul
              (m (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) 0)
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
                  0)))
              (m
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
                  (Stdlib.Int.succ 0)))
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) 0)))))) :: (
      (aadd
        (amul
          (m (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) 0)
            (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) 0))
          (m (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ 0))
            (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ 0))))
        (aopp
          (amul
            (m (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) 0)
              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ 0)))
            (m
              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ 0))
              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ 0)) 0))))) :: []))) :: []))))

(** val minv4 :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 ->
    'a1) -> 'a1 vec vec -> 'a1 vec vec **)

let minv4 aadd azero aopp amul ainv m =
  mcmul amul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))) (ainv (mdet4 aadd aopp amul m))
    (l2m azero (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ 0)))) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ 0))))
      (((aadd
          (aadd
            (aadd
              (aadd
                (aadd
                  (amul
                    (amul
                      (m
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0))
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0)))
                      (m
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                          0)))
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                          0)))))
                    (m
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))))
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))))))
                  (aopp
                    (amul
                      (amul
                        (m
                          (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0))
                          (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0)))
                        (m
                          (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ 0))) (Stdlib.Int.succ
                            (Stdlib.Int.succ 0)))
                          (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ 0))) (Stdlib.Int.succ
                            (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                      (m
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))))
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                          0)))))))
                (aopp
                  (amul
                    (amul
                      (m
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0))
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                          0))))
                      (m
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                          0)))
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0))))
                    (m
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))))
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))))))))
              (amul
                (amul
                  (m
                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))) (Stdlib.Int.succ 0))
                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))) (Stdlib.Int.succ (Stdlib.Int.succ 0))))
                  (m
                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))) (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))))))
                (m
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ 0)))))
            (amul
              (amul
                (m
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ 0))
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
                (m
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ 0))))
              (m
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
          (aopp
            (amul
              (amul
                (m
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ 0))
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
                (m
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
              (m
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (Stdlib.Int.succ 0)))))) :: ((aopp
                                                 (aadd
                                                   (aadd
                                                     (aadd
                                                       (aadd
                                                         (aadd
                                                           (amul
                                                             (amul
                                                               (m
                                                                 (nat2finS
                                                                   (Stdlib.Int.succ
                                                                   (Stdlib.Int.succ
                                                                   (Stdlib.Int.succ
                                                                   0))) 0)
                                                                 (nat2finS
                                                                   (Stdlib.Int.succ
                                                                   (Stdlib.Int.succ
                                                                   (Stdlib.Int.succ
                                                                   0)))
                                                                   (Stdlib.Int.succ
                                                                   0)))
                                                               (m
                                                                 (nat2finS
                                                                   (Stdlib.Int.succ
                                                                   (Stdlib.Int.succ
                                                                   (Stdlib.Int.succ
                                                                   0)))
                                                                   (Stdlib.Int.succ
                                                                   (Stdlib.Int.succ
                                                                   0)))
                                                                 (nat2finS
                                                                   (Stdlib.Int.succ
                                                                   (Stdlib.Int.succ
                                                                   (Stdlib.Int.succ
                                                                   0)))
                                                                   (Stdlib.Int.succ
                                                                   (Stdlib.Int.succ
                                                                   0)))))
                                                             (m
                                                               (nat2finS
                                                                 (Stdlib.Int.succ
                                                                 (Stdlib.Int.succ
                                                                 (Stdlib.Int.succ
                                                                 0)))
                                                                 (Stdlib.Int.succ
                                                                 (Stdlib.Int.succ
                                                                 (Stdlib.Int.succ
                                                                 0))))
                                                               (nat2finS
                                                                 (Stdlib.Int.succ
                                                                 (Stdlib.Int.succ
                                                                 (Stdlib.Int.succ
                                                                 0)))
                                                                 (Stdlib.Int.succ
                                                                 (Stdlib.Int.succ
                                                                 (Stdlib.Int.succ
                                                                 0))))))
                                                           (aopp
                                                             (amul
                                                               (amul
                                                                 (m
                                                                   (nat2finS
                                                                     (Stdlib.Int.succ
                                                                     (Stdlib.Int.succ
                                                                     (Stdlib.Int.succ
                                                                     0))) 0)
                                                                   (nat2finS
                                                                     (Stdlib.Int.succ
                                                                     (Stdlib.Int.succ
                                                                     (Stdlib.Int.succ
                                                                     0)))
                                                                     (Stdlib.Int.succ
                                                                     0)))
                                                                 (m
                                                                   (nat2finS
                                                                     (Stdlib.Int.succ
                                                                     (Stdlib.Int.succ
                                                                     (Stdlib.Int.succ
                                                                     0)))
                                                                     (Stdlib.Int.succ
                                                                     (Stdlib.Int.succ
                                                                     0)))
                                                                   (nat2finS
                                                                     (Stdlib.Int.succ
                                                                     (Stdlib.Int.succ
                                                                     (Stdlib.Int.succ
                                                                     0)))
                                                                     (Stdlib.Int.succ
                                                                     (Stdlib.Int.succ
                                                                     (Stdlib.Int.succ
                                                                     0))))))
                                                               (m
                                                                 (nat2finS
                                                                   (Stdlib.Int.succ
                                                                   (Stdlib.Int.succ
                                                                   (Stdlib.Int.succ
                                                                   0)))
                                                                   (Stdlib.Int.succ
                                                                   (Stdlib.Int.succ
                                                                   (Stdlib.Int.succ
                                                                   0))))
                                                                 (nat2finS
                                                                   (Stdlib.Int.succ
                                                                   (Stdlib.Int.succ
                                                                   (Stdlib.Int.succ
                                                                   0)))
                                                                   (Stdlib.Int.succ
                                                                   (Stdlib.Int.succ
                                                                   0)))))))
                                                         (aopp
                                                           (amul
                                                             (amul
                                                               (m
                                                                 (nat2finS
                                                                   (Stdlib.Int.succ
                                                                   (Stdlib.Int.succ
                                                                   (Stdlib.Int.succ
                                                                   0))) 0)
                                                                 (nat2finS
                                                                   (Stdlib.Int.succ
                                                                   (Stdlib.Int.succ
                                                                   (Stdlib.Int.succ
                                                                   0)))
                                                                   (Stdlib.Int.succ
                                                                   (Stdlib.Int.succ
                                                                   0))))
                                                               (m
                                                                 (nat2finS
                                                                   (Stdlib.Int.succ
                                                                   (Stdlib.Int.succ
                                                                   (Stdlib.Int.succ
                                                                   0)))
                                                                   (Stdlib.Int.succ
                                                                   (Stdlib.Int.succ
                                                                   0)))
                                                                 (nat2finS
                                                                   (Stdlib.Int.succ
                                                                   (Stdlib.Int.succ
                                                                   (Stdlib.Int.succ
                                                                   0)))
                                                                   (Stdlib.Int.succ
                                                                   0))))
                                                             (m
                                                               (nat2finS
                                                                 (Stdlib.Int.succ
                                                                 (Stdlib.Int.succ
                                                                 (Stdlib.Int.succ
                                                                 0)))
                                                                 (Stdlib.Int.succ
                                                                 (Stdlib.Int.succ
                                                                 (Stdlib.Int.succ
                                                                 0))))
                                                               (nat2finS
                                                                 (Stdlib.Int.succ
                                                                 (Stdlib.Int.succ
                                                                 (Stdlib.Int.succ
                                                                 0)))
                                                                 (Stdlib.Int.succ
                                                                 (Stdlib.Int.succ
                                                                 (Stdlib.Int.succ
                                                                 0))))))))
                                                       (amul
                                                         (amul
                                                           (m
                                                             (nat2finS
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               0))) 0)
                                                             (nat2finS
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               0)))
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               0))))
                                                           (m
                                                             (nat2finS
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               0)))
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               0)))
                                                             (nat2finS
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               0)))
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               0))))))
                                                         (m
                                                           (nat2finS
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             0)))
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             0))))
                                                           (nat2finS
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             0)))
                                                             (Stdlib.Int.succ 0)))))
                                                     (amul
                                                       (amul
                                                         (m
                                                           (nat2finS
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             0))) 0)
                                                           (nat2finS
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             0)))
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             0)))))
                                                         (m
                                                           (nat2finS
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             0)))
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ 0)))
                                                           (nat2finS
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             0)))
                                                             (Stdlib.Int.succ 0))))
                                                       (m
                                                         (nat2finS
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ 0)))
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ 0))))
                                                         (nat2finS
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ 0)))
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ 0))))))
                                                   (aopp
                                                     (amul
                                                       (amul
                                                         (m
                                                           (nat2finS
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             0))) 0)
                                                           (nat2finS
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             0)))
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             0)))))
                                                         (m
                                                           (nat2finS
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             0)))
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ 0)))
                                                           (nat2finS
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             0)))
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ 0)))))
                                                       (m
                                                         (nat2finS
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ 0)))
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ 0))))
                                                         (nat2finS
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ 0)))
                                                           (Stdlib.Int.succ 0))))))) :: (
      (aadd
        (aadd
          (aadd
            (aadd
              (aadd
                (amul
                  (amul
                    (m
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) 0)
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0)))
                    (m
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0))
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                        0)))))
                  (m
                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))))
                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))))))
                (aopp
                  (amul
                    (amul
                      (m
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) 0)
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0)))
                      (m
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0))
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))))))
                    (m
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))))
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                        0)))))))
              (aopp
                (amul
                  (amul
                    (m
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) 0)
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                        0))))
                    (m
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0))
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0))))
                  (m
                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))))
                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))))))))
            (amul
              (amul
                (m
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) 0)
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ (Stdlib.Int.succ 0))))
                (m
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ 0))
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
              (m
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (Stdlib.Int.succ 0)))))
          (amul
            (amul
              (m
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  0)
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
              (m
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (Stdlib.Int.succ 0))
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (Stdlib.Int.succ 0))))
            (m
              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))
              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
        (aopp
          (amul
            (amul
              (m
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  0)
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
              (m
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (Stdlib.Int.succ 0))
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
            (m
              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))
              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                (Stdlib.Int.succ 0)))))) :: ((aopp
                                               (aadd
                                                 (aadd
                                                   (aadd
                                                     (aadd
                                                       (aadd
                                                         (amul
                                                           (amul
                                                             (m
                                                               (nat2finS
                                                                 (Stdlib.Int.succ
                                                                 (Stdlib.Int.succ
                                                                 (Stdlib.Int.succ
                                                                 0))) 0)
                                                               (nat2finS
                                                                 (Stdlib.Int.succ
                                                                 (Stdlib.Int.succ
                                                                 (Stdlib.Int.succ
                                                                 0)))
                                                                 (Stdlib.Int.succ
                                                                 0)))
                                                             (m
                                                               (nat2finS
                                                                 (Stdlib.Int.succ
                                                                 (Stdlib.Int.succ
                                                                 (Stdlib.Int.succ
                                                                 0)))
                                                                 (Stdlib.Int.succ
                                                                 0))
                                                               (nat2finS
                                                                 (Stdlib.Int.succ
                                                                 (Stdlib.Int.succ
                                                                 (Stdlib.Int.succ
                                                                 0)))
                                                                 (Stdlib.Int.succ
                                                                 (Stdlib.Int.succ
                                                                 0)))))
                                                           (m
                                                             (nat2finS
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               0)))
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               0)))
                                                             (nat2finS
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               0)))
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               0))))))
                                                         (aopp
                                                           (amul
                                                             (amul
                                                               (m
                                                                 (nat2finS
                                                                   (Stdlib.Int.succ
                                                                   (Stdlib.Int.succ
                                                                   (Stdlib.Int.succ
                                                                   0))) 0)
                                                                 (nat2finS
                                                                   (Stdlib.Int.succ
                                                                   (Stdlib.Int.succ
                                                                   (Stdlib.Int.succ
                                                                   0)))
                                                                   (Stdlib.Int.succ
                                                                   0)))
                                                               (m
                                                                 (nat2finS
                                                                   (Stdlib.Int.succ
                                                                   (Stdlib.Int.succ
                                                                   (Stdlib.Int.succ
                                                                   0)))
                                                                   (Stdlib.Int.succ
                                                                   0))
                                                                 (nat2finS
                                                                   (Stdlib.Int.succ
                                                                   (Stdlib.Int.succ
                                                                   (Stdlib.Int.succ
                                                                   0)))
                                                                   (Stdlib.Int.succ
                                                                   (Stdlib.Int.succ
                                                                   (Stdlib.Int.succ
                                                                   0))))))
                                                             (m
                                                               (nat2finS
                                                                 (Stdlib.Int.succ
                                                                 (Stdlib.Int.succ
                                                                 (Stdlib.Int.succ
                                                                 0)))
                                                                 (Stdlib.Int.succ
                                                                 (Stdlib.Int.succ
                                                                 0)))
                                                               (nat2finS
                                                                 (Stdlib.Int.succ
                                                                 (Stdlib.Int.succ
                                                                 (Stdlib.Int.succ
                                                                 0)))
                                                                 (Stdlib.Int.succ
                                                                 (Stdlib.Int.succ
                                                                 0)))))))
                                                       (aopp
                                                         (amul
                                                           (amul
                                                             (m
                                                               (nat2finS
                                                                 (Stdlib.Int.succ
                                                                 (Stdlib.Int.succ
                                                                 (Stdlib.Int.succ
                                                                 0))) 0)
                                                               (nat2finS
                                                                 (Stdlib.Int.succ
                                                                 (Stdlib.Int.succ
                                                                 (Stdlib.Int.succ
                                                                 0)))
                                                                 (Stdlib.Int.succ
                                                                 (Stdlib.Int.succ
                                                                 0))))
                                                             (m
                                                               (nat2finS
                                                                 (Stdlib.Int.succ
                                                                 (Stdlib.Int.succ
                                                                 (Stdlib.Int.succ
                                                                 0)))
                                                                 (Stdlib.Int.succ
                                                                 0))
                                                               (nat2finS
                                                                 (Stdlib.Int.succ
                                                                 (Stdlib.Int.succ
                                                                 (Stdlib.Int.succ
                                                                 0)))
                                                                 (Stdlib.Int.succ
                                                                 0))))
                                                           (m
                                                             (nat2finS
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               0)))
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               0)))
                                                             (nat2finS
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               0)))
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               0))))))))
                                                     (amul
                                                       (amul
                                                         (m
                                                           (nat2finS
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             0))) 0)
                                                           (nat2finS
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             0)))
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ 0))))
                                                         (m
                                                           (nat2finS
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             0)))
                                                             (Stdlib.Int.succ 0))
                                                           (nat2finS
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             0)))
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             0))))))
                                                       (m
                                                         (nat2finS
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ 0)))
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ 0)))
                                                         (nat2finS
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ 0)))
                                                           (Stdlib.Int.succ 0)))))
                                                   (amul
                                                     (amul
                                                       (m
                                                         (nat2finS
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ 0)))
                                                           0)
                                                         (nat2finS
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ 0)))
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ 0)))))
                                                       (m
                                                         (nat2finS
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ 0)))
                                                           (Stdlib.Int.succ 0))
                                                         (nat2finS
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ 0)))
                                                           (Stdlib.Int.succ 0))))
                                                     (m
                                                       (nat2finS (Stdlib.Int.succ
                                                         (Stdlib.Int.succ
                                                         (Stdlib.Int.succ 0)))
                                                         (Stdlib.Int.succ
                                                         (Stdlib.Int.succ 0)))
                                                       (nat2finS (Stdlib.Int.succ
                                                         (Stdlib.Int.succ
                                                         (Stdlib.Int.succ 0)))
                                                         (Stdlib.Int.succ
                                                         (Stdlib.Int.succ 0))))))
                                                 (aopp
                                                   (amul
                                                     (amul
                                                       (m
                                                         (nat2finS
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ 0)))
                                                           0)
                                                         (nat2finS
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ 0)))
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ 0)))))
                                                       (m
                                                         (nat2finS
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ 0)))
                                                           (Stdlib.Int.succ 0))
                                                         (nat2finS
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ 0)))
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ 0)))))
                                                     (m
                                                       (nat2finS (Stdlib.Int.succ
                                                         (Stdlib.Int.succ
                                                         (Stdlib.Int.succ 0)))
                                                         (Stdlib.Int.succ
                                                         (Stdlib.Int.succ 0)))
                                                       (nat2finS (Stdlib.Int.succ
                                                         (Stdlib.Int.succ
                                                         (Stdlib.Int.succ 0)))
                                                         (Stdlib.Int.succ 0))))))) :: [])))) :: ((
      (aopp
        (aadd
          (aadd
            (aadd
              (aadd
                (aadd
                  (amul
                    (amul
                      (m
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0))
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) 0))
                      (m
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                          0)))
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                          0)))))
                    (m
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))))
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))))))
                  (aopp
                    (amul
                      (amul
                        (m
                          (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0))
                          (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ 0))) 0))
                        (m
                          (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ 0))) (Stdlib.Int.succ
                            (Stdlib.Int.succ 0)))
                          (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ 0))) (Stdlib.Int.succ
                            (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                      (m
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))))
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                          0)))))))
                (aopp
                  (amul
                    (amul
                      (m
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0))
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                          0))))
                      (m
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                          0)))
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) 0)))
                    (m
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))))
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))))))))
              (amul
                (amul
                  (m
                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))) (Stdlib.Int.succ 0))
                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))) (Stdlib.Int.succ (Stdlib.Int.succ 0))))
                  (m
                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))) (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))))))
                (m
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) 0))))
            (amul
              (amul
                (m
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ 0))
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
                (m
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) 0)))
              (m
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
          (aopp
            (amul
              (amul
                (m
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ 0))
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
                (m
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
              (m
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  0)))))) :: ((aadd
                                (aadd
                                  (aadd
                                    (aadd
                                      (aadd
                                        (amul
                                          (amul
                                            (m
                                              (nat2finS (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))) 0)
                                              (nat2finS (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))) 0))
                                            (m
                                              (nat2finS (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))) (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0)))
                                              (nat2finS (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))) (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0)))))
                                          (m
                                            (nat2finS (Stdlib.Int.succ
                                              (Stdlib.Int.succ (Stdlib.Int.succ
                                              0))) (Stdlib.Int.succ
                                              (Stdlib.Int.succ (Stdlib.Int.succ
                                              0))))
                                            (nat2finS (Stdlib.Int.succ
                                              (Stdlib.Int.succ (Stdlib.Int.succ
                                              0))) (Stdlib.Int.succ
                                              (Stdlib.Int.succ (Stdlib.Int.succ
                                              0))))))
                                        (aopp
                                          (amul
                                            (amul
                                              (m
                                                (nat2finS (Stdlib.Int.succ
                                                  (Stdlib.Int.succ
                                                  (Stdlib.Int.succ 0))) 0)
                                                (nat2finS (Stdlib.Int.succ
                                                  (Stdlib.Int.succ
                                                  (Stdlib.Int.succ 0))) 0))
                                              (m
                                                (nat2finS (Stdlib.Int.succ
                                                  (Stdlib.Int.succ
                                                  (Stdlib.Int.succ 0)))
                                                  (Stdlib.Int.succ
                                                  (Stdlib.Int.succ 0)))
                                                (nat2finS (Stdlib.Int.succ
                                                  (Stdlib.Int.succ
                                                  (Stdlib.Int.succ 0)))
                                                  (Stdlib.Int.succ
                                                  (Stdlib.Int.succ
                                                  (Stdlib.Int.succ 0))))))
                                            (m
                                              (nat2finS (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))) (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))))
                                              (nat2finS (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))) (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0)))))))
                                      (aopp
                                        (amul
                                          (amul
                                            (m
                                              (nat2finS (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))) 0)
                                              (nat2finS (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))) (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0))))
                                            (m
                                              (nat2finS (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))) (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0)))
                                              (nat2finS (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))) 0)))
                                          (m
                                            (nat2finS (Stdlib.Int.succ
                                              (Stdlib.Int.succ (Stdlib.Int.succ
                                              0))) (Stdlib.Int.succ
                                              (Stdlib.Int.succ (Stdlib.Int.succ
                                              0))))
                                            (nat2finS (Stdlib.Int.succ
                                              (Stdlib.Int.succ (Stdlib.Int.succ
                                              0))) (Stdlib.Int.succ
                                              (Stdlib.Int.succ (Stdlib.Int.succ
                                              0))))))))
                                    (amul
                                      (amul
                                        (m
                                          (nat2finS (Stdlib.Int.succ
                                            (Stdlib.Int.succ (Stdlib.Int.succ
                                            0))) 0)
                                          (nat2finS (Stdlib.Int.succ
                                            (Stdlib.Int.succ (Stdlib.Int.succ
                                            0))) (Stdlib.Int.succ
                                            (Stdlib.Int.succ 0))))
                                        (m
                                          (nat2finS (Stdlib.Int.succ
                                            (Stdlib.Int.succ (Stdlib.Int.succ
                                            0))) (Stdlib.Int.succ
                                            (Stdlib.Int.succ 0)))
                                          (nat2finS (Stdlib.Int.succ
                                            (Stdlib.Int.succ (Stdlib.Int.succ
                                            0))) (Stdlib.Int.succ
                                            (Stdlib.Int.succ (Stdlib.Int.succ
                                            0))))))
                                      (m
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ 0))))
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          0))))
                                  (amul
                                    (amul
                                      (m
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          0)
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ 0)))))
                                      (m
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          0)))
                                    (m
                                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ 0))))
                                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ
                                        (Stdlib.Int.succ 0))))))
                                (aopp
                                  (amul
                                    (amul
                                      (m
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          0)
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ 0)))))
                                      (m
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
                                    (m
                                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ 0))))
                                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ 0))) 0))))) :: (
      (aopp
        (aadd
          (aadd
            (aadd
              (aadd
                (aadd
                  (amul
                    (amul
                      (m
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) 0)
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) 0))
                      (m
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0))
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                          0)))))
                    (m
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))))
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))))))
                  (aopp
                    (amul
                      (amul
                        (m
                          (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ 0))) 0)
                          (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ 0))) 0))
                        (m
                          (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0))
                          (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ 0))) (Stdlib.Int.succ
                            (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                      (m
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))))
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                          0)))))))
                (aopp
                  (amul
                    (amul
                      (m
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) 0)
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                          0))))
                      (m
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0))
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) 0)))
                    (m
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))))
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))))))))
              (amul
                (amul
                  (m
                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))) 0)
                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))) (Stdlib.Int.succ (Stdlib.Int.succ 0))))
                  (m
                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))) (Stdlib.Int.succ 0))
                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))))))
                (m
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) 0))))
            (amul
              (amul
                (m
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) 0)
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
                (m
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ 0))
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) 0)))
              (m
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
          (aopp
            (amul
              (amul
                (m
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) 0)
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
                (m
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ 0))
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
              (m
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  0)))))) :: ((aadd
                                (aadd
                                  (aadd
                                    (aadd
                                      (aadd
                                        (amul
                                          (amul
                                            (m
                                              (nat2finS (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))) 0)
                                              (nat2finS (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))) 0))
                                            (m
                                              (nat2finS (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))) (Stdlib.Int.succ 0))
                                              (nat2finS (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))) (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0)))))
                                          (m
                                            (nat2finS (Stdlib.Int.succ
                                              (Stdlib.Int.succ (Stdlib.Int.succ
                                              0))) (Stdlib.Int.succ
                                              (Stdlib.Int.succ 0)))
                                            (nat2finS (Stdlib.Int.succ
                                              (Stdlib.Int.succ (Stdlib.Int.succ
                                              0))) (Stdlib.Int.succ
                                              (Stdlib.Int.succ (Stdlib.Int.succ
                                              0))))))
                                        (aopp
                                          (amul
                                            (amul
                                              (m
                                                (nat2finS (Stdlib.Int.succ
                                                  (Stdlib.Int.succ
                                                  (Stdlib.Int.succ 0))) 0)
                                                (nat2finS (Stdlib.Int.succ
                                                  (Stdlib.Int.succ
                                                  (Stdlib.Int.succ 0))) 0))
                                              (m
                                                (nat2finS (Stdlib.Int.succ
                                                  (Stdlib.Int.succ
                                                  (Stdlib.Int.succ 0)))
                                                  (Stdlib.Int.succ 0))
                                                (nat2finS (Stdlib.Int.succ
                                                  (Stdlib.Int.succ
                                                  (Stdlib.Int.succ 0)))
                                                  (Stdlib.Int.succ
                                                  (Stdlib.Int.succ
                                                  (Stdlib.Int.succ 0))))))
                                            (m
                                              (nat2finS (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))) (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0)))
                                              (nat2finS (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))) (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0)))))))
                                      (aopp
                                        (amul
                                          (amul
                                            (m
                                              (nat2finS (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))) 0)
                                              (nat2finS (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))) (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0))))
                                            (m
                                              (nat2finS (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))) (Stdlib.Int.succ 0))
                                              (nat2finS (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))) 0)))
                                          (m
                                            (nat2finS (Stdlib.Int.succ
                                              (Stdlib.Int.succ (Stdlib.Int.succ
                                              0))) (Stdlib.Int.succ
                                              (Stdlib.Int.succ 0)))
                                            (nat2finS (Stdlib.Int.succ
                                              (Stdlib.Int.succ (Stdlib.Int.succ
                                              0))) (Stdlib.Int.succ
                                              (Stdlib.Int.succ (Stdlib.Int.succ
                                              0))))))))
                                    (amul
                                      (amul
                                        (m
                                          (nat2finS (Stdlib.Int.succ
                                            (Stdlib.Int.succ (Stdlib.Int.succ
                                            0))) 0)
                                          (nat2finS (Stdlib.Int.succ
                                            (Stdlib.Int.succ (Stdlib.Int.succ
                                            0))) (Stdlib.Int.succ
                                            (Stdlib.Int.succ 0))))
                                        (m
                                          (nat2finS (Stdlib.Int.succ
                                            (Stdlib.Int.succ (Stdlib.Int.succ
                                            0))) (Stdlib.Int.succ 0))
                                          (nat2finS (Stdlib.Int.succ
                                            (Stdlib.Int.succ (Stdlib.Int.succ
                                            0))) (Stdlib.Int.succ
                                            (Stdlib.Int.succ (Stdlib.Int.succ
                                            0))))))
                                      (m
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          0))))
                                  (amul
                                    (amul
                                      (m
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          0)
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ 0)))))
                                      (m
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          (Stdlib.Int.succ 0))
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          0)))
                                    (m
                                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ
                                        (Stdlib.Int.succ 0)))
                                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ
                                        (Stdlib.Int.succ 0))))))
                                (aopp
                                  (amul
                                    (amul
                                      (m
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          0)
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ 0)))))
                                      (m
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          (Stdlib.Int.succ 0))
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
                                    (m
                                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ
                                        (Stdlib.Int.succ 0)))
                                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ 0))) 0))))) :: [])))) :: ((
      (aadd
        (aadd
          (aadd
            (aadd
              (aadd
                (amul
                  (amul
                    (m
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0))
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) 0))
                    (m
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                        0)))
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0))))
                  (m
                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))))
                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))))))
                (aopp
                  (amul
                    (amul
                      (m
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0))
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) 0))
                      (m
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                          0)))
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))))))
                    (m
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))))
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0))))))
              (aopp
                (amul
                  (amul
                    (m
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0))
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0)))
                    (m
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                        0)))
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) 0)))
                  (m
                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))))
                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))))))))
            (amul
              (amul
                (m
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ 0))
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ 0)))
                (m
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
              (m
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  0))))
          (amul
            (amul
              (m
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (Stdlib.Int.succ 0))
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
              (m
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  0)))
            (m
              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))
              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                (Stdlib.Int.succ 0)))))
        (aopp
          (amul
            (amul
              (m
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (Stdlib.Int.succ 0))
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
              (m
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (Stdlib.Int.succ 0))))
            (m
              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))
              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))) 0))))) :: (
      (aopp
        (aadd
          (aadd
            (aadd
              (aadd
                (aadd
                  (amul
                    (amul
                      (m
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) 0)
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) 0))
                      (m
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                          0)))
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0))))
                    (m
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))))
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))))))
                  (aopp
                    (amul
                      (amul
                        (m
                          (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ 0))) 0)
                          (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ 0))) 0))
                        (m
                          (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ 0))) (Stdlib.Int.succ
                            (Stdlib.Int.succ 0)))
                          (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ 0))) (Stdlib.Int.succ
                            (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                      (m
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))))
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0))))))
                (aopp
                  (amul
                    (amul
                      (m
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) 0)
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0)))
                      (m
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                          0)))
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) 0)))
                    (m
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))))
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))))))))
              (amul
                (amul
                  (m
                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))) 0)
                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))) (Stdlib.Int.succ 0)))
                  (m
                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))) (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))))))
                (m
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) 0))))
            (amul
              (amul
                (m
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) 0)
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
                (m
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) 0)))
              (m
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (Stdlib.Int.succ 0)))))
          (aopp
            (amul
              (amul
                (m
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) 0)
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
                (m
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ 0))))
              (m
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  0)))))) :: ((aadd
                                (aadd
                                  (aadd
                                    (aadd
                                      (aadd
                                        (amul
                                          (amul
                                            (m
                                              (nat2finS (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))) 0)
                                              (nat2finS (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))) 0))
                                            (m
                                              (nat2finS (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))) (Stdlib.Int.succ 0))
                                              (nat2finS (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))) (Stdlib.Int.succ 0))))
                                          (m
                                            (nat2finS (Stdlib.Int.succ
                                              (Stdlib.Int.succ (Stdlib.Int.succ
                                              0))) (Stdlib.Int.succ
                                              (Stdlib.Int.succ (Stdlib.Int.succ
                                              0))))
                                            (nat2finS (Stdlib.Int.succ
                                              (Stdlib.Int.succ (Stdlib.Int.succ
                                              0))) (Stdlib.Int.succ
                                              (Stdlib.Int.succ (Stdlib.Int.succ
                                              0))))))
                                        (aopp
                                          (amul
                                            (amul
                                              (m
                                                (nat2finS (Stdlib.Int.succ
                                                  (Stdlib.Int.succ
                                                  (Stdlib.Int.succ 0))) 0)
                                                (nat2finS (Stdlib.Int.succ
                                                  (Stdlib.Int.succ
                                                  (Stdlib.Int.succ 0))) 0))
                                              (m
                                                (nat2finS (Stdlib.Int.succ
                                                  (Stdlib.Int.succ
                                                  (Stdlib.Int.succ 0)))
                                                  (Stdlib.Int.succ 0))
                                                (nat2finS (Stdlib.Int.succ
                                                  (Stdlib.Int.succ
                                                  (Stdlib.Int.succ 0)))
                                                  (Stdlib.Int.succ
                                                  (Stdlib.Int.succ
                                                  (Stdlib.Int.succ 0))))))
                                            (m
                                              (nat2finS (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))) (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))))
                                              (nat2finS (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))) (Stdlib.Int.succ 0))))))
                                      (aopp
                                        (amul
                                          (amul
                                            (m
                                              (nat2finS (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))) 0)
                                              (nat2finS (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))) (Stdlib.Int.succ 0)))
                                            (m
                                              (nat2finS (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))) (Stdlib.Int.succ 0))
                                              (nat2finS (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))) 0)))
                                          (m
                                            (nat2finS (Stdlib.Int.succ
                                              (Stdlib.Int.succ (Stdlib.Int.succ
                                              0))) (Stdlib.Int.succ
                                              (Stdlib.Int.succ (Stdlib.Int.succ
                                              0))))
                                            (nat2finS (Stdlib.Int.succ
                                              (Stdlib.Int.succ (Stdlib.Int.succ
                                              0))) (Stdlib.Int.succ
                                              (Stdlib.Int.succ (Stdlib.Int.succ
                                              0))))))))
                                    (amul
                                      (amul
                                        (m
                                          (nat2finS (Stdlib.Int.succ
                                            (Stdlib.Int.succ (Stdlib.Int.succ
                                            0))) 0)
                                          (nat2finS (Stdlib.Int.succ
                                            (Stdlib.Int.succ (Stdlib.Int.succ
                                            0))) (Stdlib.Int.succ 0)))
                                        (m
                                          (nat2finS (Stdlib.Int.succ
                                            (Stdlib.Int.succ (Stdlib.Int.succ
                                            0))) (Stdlib.Int.succ 0))
                                          (nat2finS (Stdlib.Int.succ
                                            (Stdlib.Int.succ (Stdlib.Int.succ
                                            0))) (Stdlib.Int.succ
                                            (Stdlib.Int.succ (Stdlib.Int.succ
                                            0))))))
                                      (m
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ 0))))
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          0))))
                                  (amul
                                    (amul
                                      (m
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          0)
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ 0)))))
                                      (m
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          (Stdlib.Int.succ 0))
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          0)))
                                    (m
                                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ 0))))
                                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0)))))
                                (aopp
                                  (amul
                                    (amul
                                      (m
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          0)
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ 0)))))
                                      (m
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          (Stdlib.Int.succ 0))
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          (Stdlib.Int.succ 0))))
                                    (m
                                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ 0))))
                                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ 0))) 0))))) :: (
      (aopp
        (aadd
          (aadd
            (aadd
              (aadd
                (aadd
                  (amul
                    (amul
                      (m
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) 0)
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) 0))
                      (m
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0))
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0))))
                    (m
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                        0)))
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))))))
                  (aopp
                    (amul
                      (amul
                        (m
                          (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ 0))) 0)
                          (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ 0))) 0))
                        (m
                          (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0))
                          (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ 0))) (Stdlib.Int.succ
                            (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                      (m
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                          0)))
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0))))))
                (aopp
                  (amul
                    (amul
                      (m
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) 0)
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0)))
                      (m
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0))
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) 0)))
                    (m
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                        0)))
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))))))))
              (amul
                (amul
                  (m
                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))) 0)
                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))) (Stdlib.Int.succ 0)))
                  (m
                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))) (Stdlib.Int.succ 0))
                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))))))
                (m
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) 0))))
            (amul
              (amul
                (m
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) 0)
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
                (m
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ 0))
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) 0)))
              (m
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (Stdlib.Int.succ 0)))))
          (aopp
            (amul
              (amul
                (m
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) 0)
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
                (m
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ 0))
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ 0))))
              (m
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  0)))))) :: [])))) :: (((aopp
                                           (aadd
                                             (aadd
                                               (aadd
                                                 (aadd
                                                   (aadd
                                                     (amul
                                                       (amul
                                                         (m
                                                           (nat2finS
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             0)))
                                                             (Stdlib.Int.succ 0))
                                                           (nat2finS
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             0))) 0))
                                                         (m
                                                           (nat2finS
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             0)))
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ 0)))
                                                           (nat2finS
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             0)))
                                                             (Stdlib.Int.succ 0))))
                                                       (m
                                                         (nat2finS
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ 0)))
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ 0))))
                                                         (nat2finS
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ 0)))
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ 0)))))
                                                     (aopp
                                                       (amul
                                                         (amul
                                                           (m
                                                             (nat2finS
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               0)))
                                                               (Stdlib.Int.succ
                                                               0))
                                                             (nat2finS
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               0))) 0))
                                                           (m
                                                             (nat2finS
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               0)))
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               0)))
                                                             (nat2finS
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               0)))
                                                               (Stdlib.Int.succ
                                                               (Stdlib.Int.succ
                                                               0)))))
                                                         (m
                                                           (nat2finS
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             0)))
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             0))))
                                                           (nat2finS
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             0)))
                                                             (Stdlib.Int.succ 0))))))
                                                   (aopp
                                                     (amul
                                                       (amul
                                                         (m
                                                           (nat2finS
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             0)))
                                                             (Stdlib.Int.succ 0))
                                                           (nat2finS
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             0)))
                                                             (Stdlib.Int.succ 0)))
                                                         (m
                                                           (nat2finS
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             0)))
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ 0)))
                                                           (nat2finS
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             0))) 0)))
                                                       (m
                                                         (nat2finS
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ 0)))
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ 0))))
                                                         (nat2finS
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ 0)))
                                                           (Stdlib.Int.succ
                                                           (Stdlib.Int.succ 0)))))))
                                                 (amul
                                                   (amul
                                                     (m
                                                       (nat2finS (Stdlib.Int.succ
                                                         (Stdlib.Int.succ
                                                         (Stdlib.Int.succ 0)))
                                                         (Stdlib.Int.succ 0))
                                                       (nat2finS (Stdlib.Int.succ
                                                         (Stdlib.Int.succ
                                                         (Stdlib.Int.succ 0)))
                                                         (Stdlib.Int.succ 0)))
                                                     (m
                                                       (nat2finS (Stdlib.Int.succ
                                                         (Stdlib.Int.succ
                                                         (Stdlib.Int.succ 0)))
                                                         (Stdlib.Int.succ
                                                         (Stdlib.Int.succ 0)))
                                                       (nat2finS (Stdlib.Int.succ
                                                         (Stdlib.Int.succ
                                                         (Stdlib.Int.succ 0)))
                                                         (Stdlib.Int.succ
                                                         (Stdlib.Int.succ 0)))))
                                                   (m
                                                     (nat2finS (Stdlib.Int.succ
                                                       (Stdlib.Int.succ
                                                       (Stdlib.Int.succ 0)))
                                                       (Stdlib.Int.succ
                                                       (Stdlib.Int.succ
                                                       (Stdlib.Int.succ 0))))
                                                     (nat2finS (Stdlib.Int.succ
                                                       (Stdlib.Int.succ
                                                       (Stdlib.Int.succ 0))) 0))))
                                               (amul
                                                 (amul
                                                   (m
                                                     (nat2finS (Stdlib.Int.succ
                                                       (Stdlib.Int.succ
                                                       (Stdlib.Int.succ 0)))
                                                       (Stdlib.Int.succ 0))
                                                     (nat2finS (Stdlib.Int.succ
                                                       (Stdlib.Int.succ
                                                       (Stdlib.Int.succ 0)))
                                                       (Stdlib.Int.succ
                                                       (Stdlib.Int.succ 0))))
                                                   (m
                                                     (nat2finS (Stdlib.Int.succ
                                                       (Stdlib.Int.succ
                                                       (Stdlib.Int.succ 0)))
                                                       (Stdlib.Int.succ
                                                       (Stdlib.Int.succ 0)))
                                                     (nat2finS (Stdlib.Int.succ
                                                       (Stdlib.Int.succ
                                                       (Stdlib.Int.succ 0))) 0)))
                                                 (m
                                                   (nat2finS (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ 0)))
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ 0))))
                                                   (nat2finS (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ 0)))
                                                     (Stdlib.Int.succ 0)))))
                                             (aopp
                                               (amul
                                                 (amul
                                                   (m
                                                     (nat2finS (Stdlib.Int.succ
                                                       (Stdlib.Int.succ
                                                       (Stdlib.Int.succ 0)))
                                                       (Stdlib.Int.succ 0))
                                                     (nat2finS (Stdlib.Int.succ
                                                       (Stdlib.Int.succ
                                                       (Stdlib.Int.succ 0)))
                                                       (Stdlib.Int.succ
                                                       (Stdlib.Int.succ 0))))
                                                   (m
                                                     (nat2finS (Stdlib.Int.succ
                                                       (Stdlib.Int.succ
                                                       (Stdlib.Int.succ 0)))
                                                       (Stdlib.Int.succ
                                                       (Stdlib.Int.succ 0)))
                                                     (nat2finS (Stdlib.Int.succ
                                                       (Stdlib.Int.succ
                                                       (Stdlib.Int.succ 0)))
                                                       (Stdlib.Int.succ 0))))
                                                 (m
                                                   (nat2finS (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ 0)))
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ 0))))
                                                   (nat2finS (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ 0))) 0)))))) :: (
      (aadd
        (aadd
          (aadd
            (aadd
              (aadd
                (amul
                  (amul
                    (m
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) 0)
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) 0))
                    (m
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                        0)))
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0))))
                  (m
                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))))
                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))) (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
                (aopp
                  (amul
                    (amul
                      (m
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) 0)
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) 0))
                      (m
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                          0)))
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                          0)))))
                    (m
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))))
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0))))))
              (aopp
                (amul
                  (amul
                    (m
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) 0)
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0)))
                    (m
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                        0)))
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) 0)))
                  (m
                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))))
                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))) (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))
            (amul
              (amul
                (m
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) 0)
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ 0)))
                (m
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
              (m
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  0))))
          (amul
            (amul
              (m
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  0)
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (Stdlib.Int.succ (Stdlib.Int.succ 0))))
              (m
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  0)))
            (m
              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))
              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                (Stdlib.Int.succ 0)))))
        (aopp
          (amul
            (amul
              (m
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  0)
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (Stdlib.Int.succ (Stdlib.Int.succ 0))))
              (m
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (Stdlib.Int.succ 0))))
            (m
              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))
              (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))) 0))))) :: (
      (aopp
        (aadd
          (aadd
            (aadd
              (aadd
                (aadd
                  (amul
                    (amul
                      (m
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) 0)
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) 0))
                      (m
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0))
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0))))
                    (m
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))))
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                        0)))))
                  (aopp
                    (amul
                      (amul
                        (m
                          (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ 0))) 0)
                          (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ 0))) 0))
                        (m
                          (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0))
                          (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ 0))) (Stdlib.Int.succ
                            (Stdlib.Int.succ 0)))))
                      (m
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))))
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0))))))
                (aopp
                  (amul
                    (amul
                      (m
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) 0)
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0)))
                      (m
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0))
                        (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ 0))) 0)))
                    (m
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))))
                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ (Stdlib.Int.succ
                        0)))))))
              (amul
                (amul
                  (m
                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))) 0)
                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))) (Stdlib.Int.succ 0)))
                  (m
                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))) (Stdlib.Int.succ 0))
                    (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))) (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
                (m
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) 0))))
            (amul
              (amul
                (m
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) 0)
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ (Stdlib.Int.succ 0))))
                (m
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ 0))
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) 0)))
              (m
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (Stdlib.Int.succ 0)))))
          (aopp
            (amul
              (amul
                (m
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) 0)
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ (Stdlib.Int.succ 0))))
                (m
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ 0))
                  (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0))) (Stdlib.Int.succ 0))))
              (m
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))
                (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                  0)))))) :: ((aadd
                                (aadd
                                  (aadd
                                    (aadd
                                      (aadd
                                        (amul
                                          (amul
                                            (m
                                              (nat2finS (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))) 0)
                                              (nat2finS (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))) 0))
                                            (m
                                              (nat2finS (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))) (Stdlib.Int.succ 0))
                                              (nat2finS (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))) (Stdlib.Int.succ 0))))
                                          (m
                                            (nat2finS (Stdlib.Int.succ
                                              (Stdlib.Int.succ (Stdlib.Int.succ
                                              0))) (Stdlib.Int.succ
                                              (Stdlib.Int.succ 0)))
                                            (nat2finS (Stdlib.Int.succ
                                              (Stdlib.Int.succ (Stdlib.Int.succ
                                              0))) (Stdlib.Int.succ
                                              (Stdlib.Int.succ 0)))))
                                        (aopp
                                          (amul
                                            (amul
                                              (m
                                                (nat2finS (Stdlib.Int.succ
                                                  (Stdlib.Int.succ
                                                  (Stdlib.Int.succ 0))) 0)
                                                (nat2finS (Stdlib.Int.succ
                                                  (Stdlib.Int.succ
                                                  (Stdlib.Int.succ 0))) 0))
                                              (m
                                                (nat2finS (Stdlib.Int.succ
                                                  (Stdlib.Int.succ
                                                  (Stdlib.Int.succ 0)))
                                                  (Stdlib.Int.succ 0))
                                                (nat2finS (Stdlib.Int.succ
                                                  (Stdlib.Int.succ
                                                  (Stdlib.Int.succ 0)))
                                                  (Stdlib.Int.succ
                                                  (Stdlib.Int.succ 0)))))
                                            (m
                                              (nat2finS (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))) (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0)))
                                              (nat2finS (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))) (Stdlib.Int.succ 0))))))
                                      (aopp
                                        (amul
                                          (amul
                                            (m
                                              (nat2finS (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))) 0)
                                              (nat2finS (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))) (Stdlib.Int.succ 0)))
                                            (m
                                              (nat2finS (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))) (Stdlib.Int.succ 0))
                                              (nat2finS (Stdlib.Int.succ
                                                (Stdlib.Int.succ (Stdlib.Int.succ
                                                0))) 0)))
                                          (m
                                            (nat2finS (Stdlib.Int.succ
                                              (Stdlib.Int.succ (Stdlib.Int.succ
                                              0))) (Stdlib.Int.succ
                                              (Stdlib.Int.succ 0)))
                                            (nat2finS (Stdlib.Int.succ
                                              (Stdlib.Int.succ (Stdlib.Int.succ
                                              0))) (Stdlib.Int.succ
                                              (Stdlib.Int.succ 0)))))))
                                    (amul
                                      (amul
                                        (m
                                          (nat2finS (Stdlib.Int.succ
                                            (Stdlib.Int.succ (Stdlib.Int.succ
                                            0))) 0)
                                          (nat2finS (Stdlib.Int.succ
                                            (Stdlib.Int.succ (Stdlib.Int.succ
                                            0))) (Stdlib.Int.succ 0)))
                                        (m
                                          (nat2finS (Stdlib.Int.succ
                                            (Stdlib.Int.succ (Stdlib.Int.succ
                                            0))) (Stdlib.Int.succ 0))
                                          (nat2finS (Stdlib.Int.succ
                                            (Stdlib.Int.succ (Stdlib.Int.succ
                                            0))) (Stdlib.Int.succ
                                            (Stdlib.Int.succ 0)))))
                                      (m
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          0))))
                                  (amul
                                    (amul
                                      (m
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          0)
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0))))
                                      (m
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          (Stdlib.Int.succ 0))
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          0)))
                                    (m
                                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ
                                        (Stdlib.Int.succ 0)))
                                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ 0)))))
                                (aopp
                                  (amul
                                    (amul
                                      (m
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          0)
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0))))
                                      (m
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          (Stdlib.Int.succ 0))
                                        (nat2finS (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                                          (Stdlib.Int.succ 0))))
                                    (m
                                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ 0))) (Stdlib.Int.succ
                                        (Stdlib.Int.succ 0)))
                                      (nat2finS (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ 0))) 0))))) :: [])))) :: [])))))

type 'a rowOp =
| ROnop
| ROswap of fin * fin
| ROscale of fin * 'a
| ROadd of fin * fin * 'a

(** val rowOps2mat :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> 'a1 -> int -> 'a1 rowOp
    list -> 'a1 vec vec **)

let rowOps2mat aadd azero amul aone n l =
  fold_right (fun op m ->
    match op with
    | ROnop -> m
    | ROswap (i, j) -> mrowSwap (Stdlib.Int.succ n) i j m
    | ROscale (i, c) -> mrowScale amul (Stdlib.Int.succ n) i c m
    | ROadd (i, j, c) -> mrowAdd aadd amul (Stdlib.Int.succ n) i j c m)
    (mat1 azero aone (Stdlib.Int.succ n)) l

(** val rowOps2matInv :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 ->
    ('a1 -> 'a1) -> int -> 'a1 rowOp list -> 'a1 vec vec **)

let rowOps2matInv aadd azero aopp amul aone ainv n l =
  fold_left (fun m op ->
    match op with
    | ROnop -> m
    | ROswap (i, j) -> mrowSwap (Stdlib.Int.succ n) i j m
    | ROscale (i, c) -> mrowScale amul (Stdlib.Int.succ n) i (ainv c) m
    | ROadd (i, j, c) -> mrowAdd aadd amul (Stdlib.Int.succ n) i j (aopp c) m) l
    (mat1 azero aone (Stdlib.Int.succ n))

(** val firstNonzero :
    'a1 -> 'a1 dec -> int -> 'a1 vec vec -> int -> fin -> fin option **)

let rec firstNonzero azero hAeqDec n m x j =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> None)
    (fun x' ->
    if aeqdec hAeqDec (m (nat2finS n (sub (Stdlib.Int.succ n) x)) j) azero
    then firstNonzero azero hAeqDec n m x' j
    else Some (nat2finS n (sub (Stdlib.Int.succ n) x)))
    x

(** val elimDown :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 dec
    -> int -> 'a1 vec vec -> int -> fin -> 'a1 rowOp list * 'a1 vec vec **)

let rec elimDown aadd azero aopp amul hAeqDec n m x j =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> ([], m))
    (fun x' ->
    let fx = nat2finS n (sub (Stdlib.Int.succ n) x) in
    let x0 = m fx j in
    if aeqdec hAeqDec x0 azero
    then elimDown aadd azero aopp amul hAeqDec n m x' j
    else let op1 = ROadd (fx, j, (aopp x0)) in
         let m1 = mrowAdd aadd amul (Stdlib.Int.succ n) fx j (aopp x0) m in
         let (l2, m2) = elimDown aadd azero aopp amul hAeqDec n m1 x' j in
         ((app l2 (op1 :: [])), m2))
    x

(** val rowEchelon :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 ->
    'a1) -> 'a1 dec -> int -> 'a1 vec vec -> int -> ('a1 rowOp list * 'a1 vec
    vec) option **)

let rec rowEchelon aadd azero aopp amul ainv hAeqDec n m x =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Some ([], m))
    (fun x' ->
    let j = nat2finS n (sub (Stdlib.Int.succ n) x) in
    (match firstNonzero azero hAeqDec n m x j with
     | Some i ->
       if nat_eq_Dec (fin2nat (Stdlib.Int.succ n) i)
            (fin2nat (Stdlib.Int.succ n) j)
       then let op1 = ROnop in
            let (op2, m2) =
              let c = m j j in
              ((ROscale (j, (ainv c))),
              (mrowScale amul (Stdlib.Int.succ n) j (ainv c) m))
            in
            let (l3, m3) = elimDown aadd azero aopp amul hAeqDec n m2 x' j in
            (match rowEchelon aadd azero aopp amul ainv hAeqDec n m3 x' with
             | Some p ->
               let (l4, m4) = p in
               Some ((app l4 (app l3 (op2 :: (op1 :: [])))), m4)
             | None -> None)
       else let op1 = ROswap (j, i) in
            let m1 = mrowSwap (Stdlib.Int.succ n) j i m in
            let (op2, m2) =
              let c = m1 j j in
              ((ROscale (j, (ainv c))),
              (mrowScale amul (Stdlib.Int.succ n) j (ainv c) m1))
            in
            let (l3, m3) = elimDown aadd azero aopp amul hAeqDec n m2 x' j in
            (match rowEchelon aadd azero aopp amul ainv hAeqDec n m3 x' with
             | Some p ->
               let (l4, m4) = p in
               Some ((app l4 (app l3 (op2 :: (op1 :: [])))), m4)
             | None -> None)
     | None -> None))
    x

(** val elimUp :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 dec
    -> int -> 'a1 vec vec -> int -> fin -> 'a1 rowOp list * 'a1 vec vec **)

let rec elimUp aadd azero aopp amul hAeqDec n m x j =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> ([], m))
    (fun x' ->
    let fx = nat2finS n x' in
    let a = m fx j in
    if aeqdec hAeqDec a azero
    then elimUp aadd azero aopp amul hAeqDec n m x' j
    else let op1 = ROadd (fx, j, (aopp a)) in
         let m1 = mrowAdd aadd amul (Stdlib.Int.succ n) fx j (aopp a) m in
         let (l2, m2) = elimUp aadd azero aopp amul hAeqDec n m1 x' j in
         ((app l2 (op1 :: [])), m2))
    x

(** val minRowEchelon :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 dec
    -> int -> 'a1 vec vec -> int -> 'a1 rowOp list * 'a1 vec vec **)

let rec minRowEchelon aadd azero aopp amul hAeqDec n m x =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> ([], m))
    (fun x' ->
    let fx = nat2finS n x' in
    let (l1, m1) = elimUp aadd azero aopp amul hAeqDec n m x' fx in
    let (l2, m2) = minRowEchelon aadd azero aopp amul hAeqDec n m1 x' in
    ((app l2 l1), m2))
    x

(** val minvtbleb0 :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 ->
    'a1) -> 'a1 dec -> int -> 'a1 vec vec -> bool **)

let minvtbleb0 aadd azero aopp amul ainv aeqDec n x =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> true)
    (fun n' ->
    match rowEchelon aadd azero aopp amul ainv aeqDec n' x (Stdlib.Int.succ n') with
    | Some _ -> true
    | None -> false)
    n

(** val minvo0 :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 ->
    ('a1 -> 'a1) -> 'a1 dec -> int -> 'a1 vec vec -> 'a1 vec vec option **)

let minvo0 aadd azero aopp amul aone ainv aeqDec n m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Some (mat1 azero aone 0))
    (fun n' ->
    match rowEchelon aadd azero aopp amul ainv aeqDec n' m (Stdlib.Int.succ n') with
    | Some p ->
      let (l1, m1) = p in
      let (l2, _) =
        minRowEchelon aadd azero aopp amul aeqDec n' m1 (Stdlib.Int.succ n')
      in
      Some (rowOps2mat aadd azero amul aone n' (app l2 l1))
    | None -> None)
    n

(** val minv0 :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 ->
    ('a1 -> 'a1) -> 'a1 dec -> int -> 'a1 vec vec -> 'a1 vec vec **)

let minv0 aadd azero aopp amul aone ainv aeqDec n x =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> mat1 azero aone 0)
    (fun n' ->
    match rowEchelon aadd azero aopp amul ainv aeqDec n' x n with
    | Some p ->
      let (l1, m1) = p in
      let (l2, _) = minRowEchelon aadd azero aopp amul aeqDec n' m1 n in
      rowOps2mat aadd azero amul aone n' (app l2 l1)
    | None -> mat1 azero aone (Stdlib.Int.succ n'))
    n

module NormedOrderedFieldMatrixTheory =
 functor (E:NormedOrderedFieldElementType) ->
 struct
  type vec = E.coq_A Coq__2.vec

  (** val veq_dec : int -> vec dec **)

  let veq_dec n =
    veq_dec n E.coq_AeqDec

  (** val v2f : int -> vec -> int -> E.coq_A **)

  let v2f n a =
    v2f E.coq_Azero n a

  (** val f2v : int -> (int -> E.coq_A) -> vec **)

  let f2v =
    f2v

  (** val v2l : int -> vec -> E.coq_A list **)

  let v2l =
    v2l

  (** val l2v : int -> E.coq_A list -> vec **)

  let l2v n l =
    l2v E.coq_Azero n l

  (** val mkvec1 : E.coq_A -> vec **)

  let mkvec1 a1 =
    mkvec1 E.coq_Azero a1

  (** val mkvec2 : E.coq_A -> E.coq_A -> vec **)

  let mkvec2 a1 a2 =
    mkvec2 E.coq_Azero a1 a2

  (** val mkvec3 : E.coq_A -> E.coq_A -> E.coq_A -> vec **)

  let mkvec3 a1 a2 a3 =
    mkvec3 E.coq_Azero a1 a2 a3

  (** val mkvec4 : E.coq_A -> E.coq_A -> E.coq_A -> E.coq_A -> vec **)

  let mkvec4 a1 a2 a3 a4 =
    mkvec4 E.coq_Azero a1 a2 a3 a4

  (** val vmap : int -> (E.coq_A -> E.coq_A) -> vec -> vec **)

  let vmap n f a =
    vmap f n a

  (** val vmap2 : int -> (E.coq_A -> E.coq_A -> E.coq_A) -> vec -> vec -> vec **)

  let vmap2 n f a b =
    vmap2 f n a b

  (** val vrepeat : int -> E.coq_A -> vec **)

  let vrepeat =
    vrepeat

  (** val vzero : int -> vec **)

  let vzero n =
    vzero E.coq_Azero n

  (** val vset : int -> vec -> fin -> E.coq_A -> vec **)

  let vset =
    vset

  (** val vswap : int -> vec -> fin -> fin -> vec **)

  let vswap =
    vswap

  (** val vinsert : int -> vec -> fin -> E.coq_A -> vec **)

  let vinsert =
    vinsert

  (** val vremove : int -> vec -> fin -> vec **)

  let vremove =
    vremove

  (** val vhead : int -> vec -> E.coq_A **)

  let vhead =
    vhead

  (** val vtail : int -> vec -> E.coq_A **)

  let vtail n a =
    a (nat2finS n n)

  (** val vheadN : int -> int -> vec -> vec **)

  let vheadN =
    vheadN

  (** val vtailN : int -> int -> vec -> vec **)

  let vtailN =
    vtailN

  (** val vremoveH : int -> vec -> vec **)

  let vremoveH =
    vremoveH

  (** val vremoveT : int -> vec -> vec **)

  let vremoveT =
    vremoveT

  (** val vremoveHN : int -> int -> vec -> vec **)

  let vremoveHN =
    vremoveHN

  (** val vremoveTN : int -> int -> vec -> vec **)

  let vremoveTN =
    vremoveTN

  (** val vconsH : int -> E.coq_A -> vec -> vec **)

  let vconsH =
    vconsH

  (** val vconsT : int -> vec -> E.coq_A -> vec **)

  let vconsT =
    vconsT

  (** val vapp : int -> int -> vec -> vec -> vec **)

  let vapp =
    vapp

  (** val vmem_dec : int -> vec -> E.coq_A -> bool **)

  let vmem_dec n a x =
    vmem_dec E.coq_AeqDec n a x

  (** val vmems_dec : int -> int -> vec -> vec -> bool **)

  let vmems_dec r s a b =
    vmems_dec E.coq_AeqDec r s a b

  (** val vequiv_dec : int -> int -> vec -> vec -> bool **)

  let vequiv_dec r s a b =
    vequiv_dec E.coq_AeqDec r s a b

  (** val vfoldl : int -> vec -> 'a1 -> ('a1 -> E.coq_A -> 'a1) -> 'a1 **)

  let vfoldl n a x f =
    vfoldl E.coq_Azero n a x f

  (** val vfoldr : int -> vec -> 'a1 -> (E.coq_A -> 'a1 -> 'a1) -> 'a1 **)

  let vfoldr n a x f =
    vfoldr E.coq_Azero n a x f

  type mat = E.coq_A Coq__2.vec Coq__2.vec

  (** val cv2v : int -> mat -> vec **)

  let cv2v =
    cv2v

  (** val v2cv : int -> vec -> mat **)

  let v2cv =
    v2cv

  (** val rv2v : int -> mat -> vec **)

  let rv2v =
    rv2v

  (** val v2rv : int -> vec -> mat **)

  let v2rv =
    v2rv

  (** val f2m : int -> int -> (int -> int -> E.coq_A) -> mat **)

  let f2m =
    f2m

  (** val m2f : int -> int -> mat -> int -> int -> E.coq_A **)

  let m2f r c m =
    m2f E.coq_Azero r c m

  (** val l2m : int -> int -> E.coq_A list list -> mat **)

  let l2m r c dl =
    l2m E.coq_Azero r c dl

  (** val m2l : int -> int -> mat -> E.coq_A list list **)

  let m2l =
    m2l

  (** val m2rvl : int -> int -> mat -> vec list **)

  let m2rvl =
    m2rvl

  (** val rvl2m : int -> int -> vec list -> mat **)

  let rvl2m r c l =
    rvl2m E.coq_Azero r c l

  (** val m2cvl : int -> int -> mat -> vec list **)

  let m2cvl =
    m2cvl

  (** val cvl2m : int -> int -> vec list -> mat **)

  let cvl2m r c l =
    cvl2m E.coq_Azero r c l

  (** val mkmat_0_c : int -> mat **)

  let mkmat_0_c c =
    mkmat_0_c E.coq_Azero c

  (** val mkmat_r_0 : int -> mat **)

  let mkmat_r_0 r =
    mkmat_r_0 E.coq_Azero r

  (** val mkmat_1_1 : E.coq_A -> mat **)

  let mkmat_1_1 a11 =
    mkmat_1_1 E.coq_Azero a11

  (** val mkmat_1_c : int -> vec -> mat **)

  let mkmat_1_c =
    mkmat_1_c

  (** val mkmat_r_1 : int -> vec -> mat **)

  let mkmat_r_1 =
    mkmat_r_1

  (** val mkmat_1_2 : E.coq_A -> E.coq_A -> mat **)

  let mkmat_1_2 a11 a12 =
    mkmat_1_2 E.coq_Azero a11 a12

  (** val mkmat_2_1 : E.coq_A -> E.coq_A -> mat **)

  let mkmat_2_1 a11 a21 =
    mkmat_2_1 E.coq_Azero a11 a21

  (** val mkmat_2_2 : E.coq_A -> E.coq_A -> E.coq_A -> E.coq_A -> mat **)

  let mkmat_2_2 a11 a12 a21 a22 =
    mkmat_2_2 E.coq_Azero a11 a12 a21 a22

  (** val mkmat_1_3 : E.coq_A -> E.coq_A -> E.coq_A -> mat **)

  let mkmat_1_3 a11 a12 a13 =
    mkmat_1_3 E.coq_Azero a11 a12 a13

  (** val mkmat_3_1 : E.coq_A -> E.coq_A -> E.coq_A -> mat **)

  let mkmat_3_1 a11 a21 a31 =
    mkmat_3_1 E.coq_Azero a11 a21 a31

  (** val mkmat_3_3 :
      E.coq_A -> E.coq_A -> E.coq_A -> E.coq_A -> E.coq_A -> E.coq_A -> E.coq_A
      -> E.coq_A -> E.coq_A -> mat **)

  let mkmat_3_3 a11 a12 a13 a21 a22 a23 a31 a32 a33 =
    mkmat_3_3 E.coq_Azero a11 a12 a13 a21 a22 a23 a31 a32 a33

  (** val mkmat_1_4 : E.coq_A -> E.coq_A -> E.coq_A -> E.coq_A -> mat **)

  let mkmat_1_4 a11 a12 a13 a14 =
    mkmat_1_4 E.coq_Azero a11 a12 a13 a14

  (** val mkmat_4_1 : E.coq_A -> E.coq_A -> E.coq_A -> E.coq_A -> mat **)

  let mkmat_4_1 a11 a21 a31 a41 =
    mkmat_4_1 E.coq_Azero a11 a21 a31 a41

  (** val mkmat_4_4 :
      E.coq_A -> E.coq_A -> E.coq_A -> E.coq_A -> E.coq_A -> E.coq_A -> E.coq_A
      -> E.coq_A -> E.coq_A -> E.coq_A -> E.coq_A -> E.coq_A -> E.coq_A ->
      E.coq_A -> E.coq_A -> E.coq_A -> mat **)

  let mkmat_4_4 a11 a12 a13 a14 a21 a22 a23 a24 a31 a32 a33 a34 a41 a42 a43 a44 =
    mkmat_4_4 E.coq_Azero a11 a12 a13 a14 a21 a22 a23 a24 a31 a32 a33 a34 a41 a42
      a43 a44

  (** val mrow : int -> int -> mat -> fin -> vec **)

  let mrow =
    mrow

  (** val mcol : int -> int -> mat -> fin -> vec **)

  let mcol =
    mcol

  (** val mappr : int -> int -> int -> mat -> mat -> mat **)

  let mappr r1 r2 c m n =
    mappr E.coq_Azero r1 r2 c m n

  (** val mappc : int -> int -> int -> mat -> mat -> mat **)

  let mappc r c1 c2 m n =
    mappc E.coq_Azero r c1 c2 m n

  (** val mheadc : int -> int -> mat -> vec **)

  let mheadc =
    mheadc

  (** val mtailc : int -> int -> mat -> vec **)

  let mtailc =
    mtailc

  (** val mremovecH : int -> int -> mat -> mat **)

  let mremovecH =
    mremovecH

  (** val mremovecT : int -> int -> mat -> mat **)

  let mremovecT =
    mremovecT

  (** val mconsrH : int -> int -> vec -> mat -> mat **)

  let mconsrH =
    mconsrH

  (** val mconsrT : int -> int -> mat -> vec -> mat **)

  let mconsrT =
    mconsrT

  (** val mconscH : int -> int -> vec -> mat -> mat **)

  let mconscH =
    mconscH

  (** val mconscT : int -> int -> mat -> vec -> mat **)

  let mconscT =
    mconscT

  (** val mmap : int -> int -> (E.coq_A -> E.coq_A) -> mat -> mat **)

  let mmap r c f m =
    Coq__3.vmap (Coq__3.vmap f c) r m

  (** val mmap2 :
      int -> int -> (E.coq_A -> E.coq_A -> E.coq_A) -> mat -> mat -> mat **)

  let mmap2 r c f m n =
    Coq__4.vmap2 (Coq__4.vmap2 f c) r m n

  (** val msetr : int -> int -> mat -> vec -> fin -> mat **)

  let msetr =
    msetr

  (** val msetc : int -> int -> mat -> vec -> fin -> mat **)

  let msetc =
    msetc

  (** val mtrans : int -> int -> mat -> mat **)

  let mtrans =
    mtrans

  (** val mdiagMk : int -> vec -> mat **)

  let mdiagMk n a =
    mdiagMk E.coq_Azero n a

  (** val mat0 : int -> int -> mat **)

  let mat0 r c =
    mat0 E.coq_Azero r c

  (** val vsum : int -> vec -> E.coq_A **)

  let vsum n a =
    vsum E.coq_Aadd E.coq_Azero n a

  (** val vadd : int -> vec -> vec -> vec **)

  let vadd n a b =
    vadd E.coq_Aadd n a b

  (** val madd : int -> int -> mat -> mat -> mat **)

  let madd r c m n =
    madd E.coq_Aadd r c m n

  (** val veye : int -> fin -> vec **)

  let veye n i =
    veye E.coq_Azero E.coq_Aone n i

  (** val veyes : int -> E.coq_A Coq__2.vec Coq__2.vec **)

  let veyes n =
    veyes E.coq_Azero E.coq_Aone n

  (** val vopp : int -> vec -> vec **)

  let vopp n a =
    vopp E.coq_Aopp n a

  (** val vcmul : int -> E.coq_A -> vec -> vec **)

  let vcmul n x a =
    vcmul E.coq_Amul n x a

  (** val vdot : int -> vec -> vec -> E.coq_A **)

  let vdot n a b =
    vdot E.coq_Aadd E.coq_Azero E.coq_Amul n a b

  (** val mat1 : int -> mat **)

  let mat1 n =
    mat1 E.coq_Azero E.coq_Aone n

  (** val mtrace : int -> mat -> E.coq_A **)

  let mtrace n m =
    mtrace E.coq_Aadd E.coq_Azero n m

  (** val mopp : int -> int -> mat -> mat **)

  let mopp r c m =
    mopp E.coq_Aopp r c m

  (** val mcmul : int -> int -> E.coq_A -> mat -> mat **)

  let mcmul r c x m =
    mcmul E.coq_Amul r c x m

  (** val mmul : int -> int -> int -> mat -> mat -> mat **)

  let mmul r c s m n =
    mmul E.coq_Aadd E.coq_Azero E.coq_Amul r c s m n

  (** val mmulv : int -> int -> mat -> vec -> vec **)

  let mmulv r c m a =
    mmulv E.coq_Aadd E.coq_Azero E.coq_Amul r c m a

  (** val mvmul : int -> int -> vec -> mat -> vec **)

  let mvmul r c a m =
    mvmul E.coq_Aadd E.coq_Azero E.coq_Amul r c a m

  (** val mdet : int -> mat -> E.coq_A **)

  let mdet n m =
    mdet E.coq_Aadd E.coq_Azero E.coq_Aopp E.coq_Amul E.coq_Aone n m

  (** val mdet1 : mat -> E.coq_A **)

  let mdet1 =
    mdet1

  (** val mdet2 : mat -> E.coq_A **)

  let mdet2 m =
    mdet2 E.coq_Aadd E.coq_Aopp E.coq_Amul m

  (** val mdet3 : mat -> E.coq_A **)

  let mdet3 m =
    mdet3 E.coq_Aadd E.coq_Aopp E.coq_Amul m

  (** val madj : int -> mat -> mat **)

  let madj n m =
    madj E.coq_Aadd E.coq_Azero E.coq_Aopp E.coq_Amul E.coq_Aone n m

  module AM =
   struct
    module Minv_inst =
     struct
      module AMNotations =
       struct
       end

      (** val minvtbleb : int -> E.coq_A Coq__2.vec Coq__2.vec -> bool **)

      let minvtbleb n m =
        minvtbleb E.coq_Aadd E.coq_Azero E.coq_Aopp E.coq_Amul E.coq_Aone
          E.coq_AeqDec n m

      (** val minvo :
          int -> E.coq_A Coq__2.vec Coq__2.vec -> E.coq_A Coq__2.vec Coq__2.vec
          option **)

      let minvo n m =
        minvo E.coq_Aadd E.coq_Azero E.coq_Aopp E.coq_Amul E.coq_Aone E.coq_Ainv
          E.coq_AeqDec n m

      (** val minv :
          int -> E.coq_A Coq__2.vec Coq__2.vec -> E.coq_A Coq__2.vec Coq__2.vec **)

      let minv n m =
        minv E.coq_Aadd E.coq_Azero E.coq_Aopp E.coq_Amul E.coq_Aone E.coq_Ainv
          E.coq_AeqDec n m

      (** val minvNoCheck :
          int -> E.coq_A Coq__2.vec Coq__2.vec -> E.coq_A Coq__2.vec Coq__2.vec **)

      let minvNoCheck n m =
        minvNoCheck E.coq_Aadd E.coq_Azero E.coq_Aopp E.coq_Amul E.coq_Aone
          E.coq_Ainv n m
     end

    module MinvMore_inst =
     struct
      (** val minvtblebList : int -> E.coq_A list list -> bool **)

      let minvtblebList n dl =
        Minv_inst.minvtbleb n (Coq__5.l2m E.coq_Azero n n dl)

      (** val minvList : int -> E.coq_A list list -> E.coq_A list list **)

      let minvList n dl =
        Coq__6.m2l n n (Minv_inst.minv n (Coq__5.l2m E.coq_Azero n n dl))

      (** val solveEq :
          int -> E.coq_A Coq__2.vec Coq__2.vec -> E.coq_A Coq__2.vec -> E.coq_A
          Coq__2.vec **)

      let solveEq n c b =
        Coq__7.mmulv E.coq_Aadd E.coq_Azero E.coq_Amul n n (Minv_inst.minv n c) b

      (** val solveEqList :
          int -> E.coq_A list list -> E.coq_A list -> E.coq_A list **)

      let solveEqList n lC lb =
        let c = Coq__5.l2m E.coq_Azero n n lC in
        let b = Coq__8.l2v E.coq_Azero n lb in
        let x = solveEq n c b in Coq__9.v2l n x
     end

    (** val solveEqNoCheck :
        int -> E.coq_A Coq__2.vec Coq__2.vec -> E.coq_A Coq__2.vec -> E.coq_A
        Coq__2.vec **)

    let solveEqNoCheck n c b =
      Coq__7.mmulv E.coq_Aadd E.coq_Azero E.coq_Amul n n
        (Minv_inst.minvNoCheck n c) b

    (** val solveEqListNoCheck :
        int -> E.coq_A list list -> E.coq_A list -> E.coq_A list **)

    let solveEqListNoCheck n lC lb =
      let c = Coq__5.l2m E.coq_Azero n n lC in
      let b = Coq__8.l2v E.coq_Azero n lb in
      let x = solveEqNoCheck n c b in Coq__9.v2l n x

    (** val minvElement :
        int -> E.coq_A Coq__2.vec Coq__2.vec -> fin -> fin -> E.coq_A **)

    let minvElement n m i j =
      minvElement E.coq_Aadd E.coq_Azero E.coq_Aopp E.coq_Amul E.coq_Aone
        E.coq_Ainv n m i j

    (** val minv1 :
        E.coq_A Coq__2.vec Coq__2.vec -> E.coq_A Coq__2.vec Coq__2.vec **)

    let minv1 m =
      minv1 E.coq_Azero E.coq_Amul E.coq_Aone E.coq_Ainv m

    (** val minv2 :
        E.coq_A Coq__2.vec Coq__2.vec -> E.coq_A Coq__2.vec Coq__2.vec **)

    let minv2 m =
      minv2 E.coq_Aadd E.coq_Azero E.coq_Aopp E.coq_Amul E.coq_Ainv m

    (** val minv3 :
        E.coq_A Coq__2.vec Coq__2.vec -> E.coq_A Coq__2.vec Coq__2.vec **)

    let minv3 m =
      minv3 E.coq_Aadd E.coq_Azero E.coq_Aopp E.coq_Amul E.coq_Ainv m

    (** val minv4 :
        E.coq_A Coq__2.vec Coq__2.vec -> E.coq_A Coq__2.vec Coq__2.vec **)

    let minv4 m =
      minv4 E.coq_Aadd E.coq_Azero E.coq_Aopp E.coq_Amul E.coq_Ainv m
   end

  module GE =
   struct
    module Minv_inst =
     struct
      module GENotations =
       struct
       end

      (** val minvtbleb : int -> E.coq_A Coq__2.vec Coq__2.vec -> bool **)

      let minvtbleb n m =
        minvtbleb0 E.coq_Aadd E.coq_Azero E.coq_Aopp E.coq_Amul E.coq_Ainv
          E.coq_AeqDec n m

      (** val minvo :
          int -> E.coq_A Coq__2.vec Coq__2.vec -> E.coq_A Coq__2.vec Coq__2.vec
          option **)

      let minvo n m =
        minvo0 E.coq_Aadd E.coq_Azero E.coq_Aopp E.coq_Amul E.coq_Aone E.coq_Ainv
          E.coq_AeqDec n m

      (** val minv :
          int -> E.coq_A Coq__2.vec Coq__2.vec -> E.coq_A Coq__2.vec Coq__2.vec **)

      let minv n m =
        minv0 E.coq_Aadd E.coq_Azero E.coq_Aopp E.coq_Amul E.coq_Aone E.coq_Ainv
          E.coq_AeqDec n m
     end

    module MinvMore_inst =
     struct
      (** val minvtblebList : int -> E.coq_A list list -> bool **)

      let minvtblebList n dl =
        Minv_inst.minvtbleb n (Coq__5.l2m E.coq_Azero n n dl)

      (** val minvList : int -> E.coq_A list list -> E.coq_A list list **)

      let minvList n dl =
        Coq__6.m2l n n (Minv_inst.minv n (Coq__5.l2m E.coq_Azero n n dl))

      (** val solveEq :
          int -> E.coq_A Coq__2.vec Coq__2.vec -> E.coq_A Coq__2.vec -> E.coq_A
          Coq__2.vec **)

      let solveEq n c b =
        Coq__7.mmulv E.coq_Aadd E.coq_Azero E.coq_Amul n n (Minv_inst.minv n c) b

      (** val solveEqList :
          int -> E.coq_A list list -> E.coq_A list -> E.coq_A list **)

      let solveEqList n lC lb =
        let c = Coq__5.l2m E.coq_Azero n n lC in
        let b = Coq__8.l2v E.coq_Azero n lb in
        let x = solveEq n c b in Coq__9.v2l n x
     end
   end

  module OrthAM =
   struct
    module AM =
     struct
      module Minv_inst =
       struct
        module AMNotations =
         struct
         end

        (** val minvtbleb : int -> E.coq_A Coq__2.vec Coq__2.vec -> bool **)

        let minvtbleb n m =
          minvtbleb E.coq_Aadd E.coq_Azero E.coq_Aopp E.coq_Amul E.coq_Aone
            E.coq_AeqDec n m

        (** val minvo :
            int -> E.coq_A Coq__2.vec Coq__2.vec -> E.coq_A Coq__2.vec Coq__2.vec
            option **)

        let minvo n m =
          minvo E.coq_Aadd E.coq_Azero E.coq_Aopp E.coq_Amul E.coq_Aone
            E.coq_Ainv E.coq_AeqDec n m

        (** val minv :
            int -> E.coq_A Coq__2.vec Coq__2.vec -> E.coq_A Coq__2.vec Coq__2.vec **)

        let minv n m =
          minv E.coq_Aadd E.coq_Azero E.coq_Aopp E.coq_Amul E.coq_Aone E.coq_Ainv
            E.coq_AeqDec n m

        (** val minvNoCheck :
            int -> E.coq_A Coq__2.vec Coq__2.vec -> E.coq_A Coq__2.vec Coq__2.vec **)

        let minvNoCheck n m =
          minvNoCheck E.coq_Aadd E.coq_Azero E.coq_Aopp E.coq_Amul E.coq_Aone
            E.coq_Ainv n m
       end

      module MinvMore_inst =
       struct
        (** val minvtblebList : int -> E.coq_A list list -> bool **)

        let minvtblebList n dl =
          Minv_inst.minvtbleb n (Coq__5.l2m E.coq_Azero n n dl)

        (** val minvList : int -> E.coq_A list list -> E.coq_A list list **)

        let minvList n dl =
          Coq__6.m2l n n (Minv_inst.minv n (Coq__5.l2m E.coq_Azero n n dl))

        (** val solveEq :
            int -> E.coq_A Coq__2.vec Coq__2.vec -> E.coq_A Coq__2.vec -> E.coq_A
            Coq__2.vec **)

        let solveEq n c b =
          Coq__7.mmulv E.coq_Aadd E.coq_Azero E.coq_Amul n n (Minv_inst.minv n c)
            b

        (** val solveEqList :
            int -> E.coq_A list list -> E.coq_A list -> E.coq_A list **)

        let solveEqList n lC lb =
          let c = Coq__5.l2m E.coq_Azero n n lC in
          let b = Coq__8.l2v E.coq_Azero n lb in
          let x = solveEq n c b in Coq__9.v2l n x
       end

      (** val solveEqNoCheck :
          int -> E.coq_A Coq__2.vec Coq__2.vec -> E.coq_A Coq__2.vec -> E.coq_A
          Coq__2.vec **)

      let solveEqNoCheck n c b =
        Coq__7.mmulv E.coq_Aadd E.coq_Azero E.coq_Amul n n
          (Minv_inst.minvNoCheck n c) b

      (** val solveEqListNoCheck :
          int -> E.coq_A list list -> E.coq_A list -> E.coq_A list **)

      let solveEqListNoCheck n lC lb =
        let c = Coq__5.l2m E.coq_Azero n n lC in
        let b = Coq__8.l2v E.coq_Azero n lb in
        let x = solveEqNoCheck n c b in Coq__9.v2l n x

      (** val minvElement :
          int -> E.coq_A Coq__2.vec Coq__2.vec -> fin -> fin -> E.coq_A **)

      let minvElement n m i j =
        minvElement E.coq_Aadd E.coq_Azero E.coq_Aopp E.coq_Amul E.coq_Aone
          E.coq_Ainv n m i j

      (** val minv1 :
          E.coq_A Coq__2.vec Coq__2.vec -> E.coq_A Coq__2.vec Coq__2.vec **)

      let minv1 m =
        minv1 E.coq_Azero E.coq_Amul E.coq_Aone E.coq_Ainv m

      (** val minv2 :
          E.coq_A Coq__2.vec Coq__2.vec -> E.coq_A Coq__2.vec Coq__2.vec **)

      let minv2 m =
        minv2 E.coq_Aadd E.coq_Azero E.coq_Aopp E.coq_Amul E.coq_Ainv m

      (** val minv3 :
          E.coq_A Coq__2.vec Coq__2.vec -> E.coq_A Coq__2.vec Coq__2.vec **)

      let minv3 m =
        minv3 E.coq_Aadd E.coq_Azero E.coq_Aopp E.coq_Amul E.coq_Ainv m

      (** val minv4 :
          E.coq_A Coq__2.vec Coq__2.vec -> E.coq_A Coq__2.vec Coq__2.vec **)

      let minv4 m =
        minv4 E.coq_Aadd E.coq_Azero E.coq_Aopp E.coq_Amul E.coq_Ainv m
     end

    type coq_GOn =
      E.coq_A Coq__2.vec Coq__2.vec
      (* singleton inductive, whose constructor was Build_GOn *)

    (** val coq_GOn_mat : int -> coq_GOn -> E.coq_A Coq__2.vec Coq__2.vec **)

    let coq_GOn_mat _ g =
      g

    (** val mkGOn : int -> E.coq_A Coq__2.vec Coq__2.vec -> coq_GOn **)

    let mkGOn _ m =
      m

    (** val coq_GOn_mul : int -> coq_GOn -> coq_GOn -> coq_GOn **)

    let coq_GOn_mul n x1 x2 =
      Coq__10.mmul E.coq_Aadd E.coq_Azero E.coq_Amul n n n x1 x2

    (** val coq_GOn_1 : int -> coq_GOn **)

    let coq_GOn_1 n =
      Coq__11.mat1 E.coq_Azero E.coq_Aone n

    (** val coq_GOn_inv : int -> coq_GOn -> coq_GOn **)

    let coq_GOn_inv n x =
      Coq__12.mtrans n n x

    type coq_SOn =
      coq_GOn
      (* singleton inductive, whose constructor was Build_SOn *)

    (** val coq_SOn_GOn : int -> coq_SOn -> coq_GOn **)

    let coq_SOn_GOn _ s =
      s

    (** val mkSOn : int -> E.coq_A Coq__2.vec Coq__2.vec -> coq_SOn **)

    let mkSOn _ m =
      m

    (** val coq_SOn_mul : int -> coq_SOn -> coq_SOn -> coq_SOn **)

    let coq_SOn_mul =
      coq_GOn_mul

    (** val coq_SOn_1 : int -> coq_SOn **)

    let coq_SOn_1 =
      coq_GOn_1

    (** val coq_SOn_inv : int -> coq_SOn -> coq_SOn **)

    let coq_SOn_inv =
      coq_GOn_inv
   end

  (** val vproj : int -> vec -> vec -> vec **)

  let vproj n a b =
    vproj E.coq_Aadd E.coq_Azero E.coq_Amul E.coq_Ainv n a b

  (** val vperp : int -> vec -> vec -> vec **)

  let vperp n a b =
    vperp E.coq_Aadd E.coq_Azero E.coq_Aopp E.coq_Amul E.coq_Ainv n a b

  (** val cramerRule : int -> mat -> vec -> vec **)

  let cramerRule n c b =
    cramerRule E.coq_Aadd E.coq_Azero E.coq_Aopp E.coq_Amul E.coq_Aone E.coq_Ainv
      n c b

  (** val cramerRuleList :
      int -> E.coq_A list list -> E.coq_A list -> E.coq_A list **)

  let cramerRuleList n lC lb =
    cramerRuleList E.coq_Aadd E.coq_Azero E.coq_Aopp E.coq_Amul E.coq_Aone
      E.coq_Ainv n lC lb

  (** val rowOps2mat : int -> E.coq_A rowOp list -> mat **)

  let rowOps2mat n l =
    rowOps2mat E.coq_Aadd E.coq_Azero E.coq_Amul E.coq_Aone n l

  (** val rowOps2matInv : int -> E.coq_A rowOp list -> mat **)

  let rowOps2matInv n l =
    rowOps2matInv E.coq_Aadd E.coq_Azero E.coq_Aopp E.coq_Amul E.coq_Aone
      E.coq_Ainv n l

  (** val minvtblebGE : int -> mat -> bool **)

  let minvtblebGE =
    GE.Minv_inst.minvtbleb

  (** val minvoGE : int -> mat -> mat option **)

  let minvoGE =
    GE.Minv_inst.minvo

  (** val minvGE : int -> mat -> mat **)

  let minvGE =
    GE.Minv_inst.minv

  module MinvGENotations =
   struct
   end

  (** val minvtblebListGE : int -> E.coq_A list list -> bool **)

  let minvtblebListGE =
    GE.MinvMore_inst.minvtblebList

  (** val minvListGE : int -> E.coq_A list list -> E.coq_A list list **)

  let minvListGE =
    GE.MinvMore_inst.minvList

  (** val solveEqGE : int -> mat -> vec -> vec **)

  let solveEqGE =
    GE.MinvMore_inst.solveEq

  (** val solveEqListGE :
      int -> E.coq_A list list -> E.coq_A list -> E.coq_A list **)

  let solveEqListGE =
    GE.MinvMore_inst.solveEqList

  (** val minvtblebAM : int -> mat -> bool **)

  let minvtblebAM =
    OrthAM.AM.Minv_inst.minvtbleb

  (** val minvoAM : int -> mat -> mat option **)

  let minvoAM =
    OrthAM.AM.Minv_inst.minvo

  (** val minvAM : int -> mat -> mat **)

  let minvAM =
    OrthAM.AM.Minv_inst.minv

  module MinvAMNotations =
   struct
   end

  (** val minvAM1 : mat -> mat **)

  let minvAM1 =
    OrthAM.AM.minv1

  (** val minvAM2 : mat -> mat **)

  let minvAM2 =
    OrthAM.AM.minv2

  (** val minvAM3 : mat -> mat **)

  let minvAM3 =
    OrthAM.AM.minv3

  (** val minvAM4 : mat -> mat **)

  let minvAM4 =
    OrthAM.AM.minv4

  (** val minvtblebListAM : int -> E.coq_A list list -> bool **)

  let minvtblebListAM =
    OrthAM.AM.MinvMore_inst.minvtblebList

  (** val minvListAM : int -> E.coq_A list list -> E.coq_A list list **)

  let minvListAM =
    OrthAM.AM.MinvMore_inst.minvList

  (** val solveEqAM : int -> mat -> vec -> vec **)

  let solveEqAM =
    OrthAM.AM.MinvMore_inst.solveEq

  (** val solveEqListAM :
      int -> E.coq_A list list -> E.coq_A list -> E.coq_A list **)

  let solveEqListAM =
    OrthAM.AM.MinvMore_inst.solveEqList

  (** val minvNoCheckAM : int -> mat -> mat **)

  let minvNoCheckAM =
    OrthAM.AM.Minv_inst.minvNoCheck

  (** val solveEqNoCheckAM : int -> mat -> vec -> vec **)

  let solveEqNoCheckAM n c b =
    mmulv n n (minvNoCheckAM n c) b

  (** val solveEqListNoCheckAM :
      int -> E.coq_A list list -> E.coq_A list -> E.coq_A list **)

  let solveEqListNoCheckAM =
    OrthAM.AM.solveEqListNoCheck

  type coq_GOn = OrthAM.coq_GOn

  (** val coq_GOn_mat : int -> coq_GOn -> mat **)

  let coq_GOn_mat _ m =
    m

  (** val mkGOn : int -> mat -> coq_GOn **)

  let mkGOn =
    OrthAM.mkGOn

  (** val coq_GOn_mul : int -> coq_GOn -> coq_GOn -> coq_GOn **)

  let coq_GOn_mul =
    OrthAM.coq_GOn_mul

  (** val coq_GOn_1 : int -> coq_GOn **)

  let coq_GOn_1 =
    OrthAM.coq_GOn_1

  (** val coq_GOn_inv : int -> coq_GOn -> coq_GOn **)

  let coq_GOn_inv =
    OrthAM.coq_GOn_inv

  type coq_SOn = OrthAM.coq_SOn

  (** val coq_SOn_GOn : int -> coq_SOn -> coq_GOn **)

  let coq_SOn_GOn _ m =
    m

  (** val mkSOn : int -> mat -> coq_SOn **)

  let mkSOn =
    OrthAM.mkSOn

  (** val coq_SOn_mul : int -> coq_SOn -> coq_SOn -> coq_SOn **)

  let coq_SOn_mul =
    OrthAM.coq_SOn_mul

  (** val coq_SOn_1 : int -> coq_SOn **)

  let coq_SOn_1 =
    OrthAM.coq_SOn_1

  (** val coq_SOn_inv : int -> coq_SOn -> coq_SOn **)

  let coq_SOn_inv =
    OrthAM.coq_SOn_inv

  (** val vlen : int -> vec -> RbaseSymbolsImpl.coq_R **)

  let vlen n a =
    vlen E.coq_Aadd E.coq_Azero E.coq_Amul E.a2r n a
 end

module MatrixTheoryR =
 NormedOrderedFieldMatrixTheory(NormedOrderedFieldElementTypeR)
