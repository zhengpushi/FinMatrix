(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Extraction of [R] into Ocaml's [float]
  author    : Zhengpu Shi
  date      : Nov 3, 2022

  Reference :
  1. coq/theories/extraction/ExtrOcamlNatInt.v

*)

Require Export Extraction.
Require Import Reals.

(* the command provided by std library will generate warning *)
(* Require Import extraction.ExtrOcamlBasic.
Require Import extraction.ExtrOcamlNatInt.
Require Import extraction.ExtrOcamlZInt. *)


(* some inductive datatypes *)
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive nat => "int" [ "0" "Int.succ" ] 
  "(fun fO fS n -> if n=0 then fO () else fS (n-1))".


(* constant - Real number and operations *)
Extract Constant R => float.

(* patch for coq 8.11 and newer *)
Extract Constant Rabst => "__".
Extract Constant Rrepr => "__".

Extract Constant R0 => "0.0".
Extract Constant R1 => "1.0".
Extract Constant PI => "Float.pi".
Extract Constant Rplus => "(+.)".
Extract Constant Rmult => "( *. )".
Extract Constant Rminus => "(-.)".
Extract Constant Ropp => "fun a -> (0.0 -. a)".
Extract Constant Rinv => "fun a -> (1.0 /. a)".
Extract Constant Rpower => "Float.pow".
Extract Constant sin => "Float.sin".
Extract Constant cos => "Float.cos".
Extract Constant sqrt => "Float.sqrt".
Extract Constant atan => "Float.atan".
Extract Constant acos => "Float.acos".


(** two float numbers are comparison decidable *)
Extract Constant total_order_T => "fun r1 r2 ->
  let c = Float.compare r1 r2 in
  if c < 0 then Some true
  else (if c = 0 then None else Some false)".

Extract Constant Req_dec_T => "fun r1 r2 ->
  let c = Float.compare r1 r2 in
  if c = 0 then true
  else false".

(* Extract Constant pow => 
  "fun r0 n -> if n=0 then 1.0 else (r0 *. (pow r0 (n-1)))". *)

(* Example ex_r1 : R := 1.25. *)
(* Example ex_r2 (r1 r2 : R) : R := sin r1 + r2. *)

(* Recursive Extraction ex_r1 ex_r2. *)
(* Extraction "test1.ml" ex_r1 ex_r2. *)
