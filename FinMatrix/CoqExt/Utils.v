(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Utilities
  author    : Zhengpu Shi
  date      : 2023.12

  remark    :
 *)

Require Import List.
Import ListNotations.

(** * 基于列表的字典 *)
Section LDict.
  Variable (K V : Type).
  Variable (Keqb : K -> K -> bool).
  
  (* 取出键值对的键和值 *)
  Notation "x .K" := (fst x) (at level 10, format "x .K").
  Notation "x .V" := (snd x) (at level 10, format "x .V").
  (* 字典类型 *)
  Definition LDict := list (K * V).
  
  (* 建立空字典 *)
  Definition ldictEmpty : LDict := [].
  
  (* 加入元素 *)
  Fixpoint ldictAdd (x : K * V) (d : LDict) : LDict :=
    match d with
    | [] => [x]
    | hd :: td =>
        (* 若发现第一个键相同的元素，则替换后不再追究 *)
        if Keqb (x.K) (hd.K)
        then x :: td
        else hd :: (ldictAdd x td)
    end.
  
  (* 查询 *)
  Fixpoint ldictFind (k : K) (d : LDict) : option V :=
    match d with
    | [] => None
    | hd :: td =>
        if Keqb k (hd.K)
        then Some (hd.V)
        else ldictFind k td
    end.
End LDict.
