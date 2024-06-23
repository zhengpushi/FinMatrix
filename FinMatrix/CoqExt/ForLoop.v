(*
  Copyright 2024 Zhengpu Shi
  This file is part of FinMatrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : understand For Loop
  author    : Zhengpu Shi
  date      : 2023.05
  
  remark    :
  1. copy from lecture of FEM by professor Gang Chen, NUAA, 2021.
  2. change the index from 1 to 0
 *)

Require Import Nat Lia.

(* define a non-tailrecursive version of for_loop. *)
Fixpoint for_loop_aux {A B:Set} 
  (n:nat) (input:A) (output:B) (p:nat->A->B->B) {struct n} : B :=
  match n with
    0 => output
  | S m => p m input (for_loop_aux m input output p)
  end.

(*
  n      循环次数
  input  
  init   初始值

  示例：for_loop 5 input p init
     = p 5 input (p 4 input (p 3 input (p 2 input (p 1 input init))))
  p
  *)
Definition for_loop {A B:Set} 
  (n:nat) (input:A) (p:nat->A->B->B) (init:B) : B :=
  for_loop_aux n input init p.

Section test.
  Import Nat.
  Variable input init : nat.
  Variable p : nat -> nat -> nat -> nat.
  Compute for_loop 5 input p init.

  Let p' (idx:nat) (input : nat) (init : nat) : nat :=
        if (idx <? 2)
        then init
        else input + init.
  Opaque Nat.add.
  Eval cbn in for_loop 5 input p' init.
  
End test.

Lemma for_loop_S :
  forall (A B:Set) (n:nat) (input:A) (p:nat->A->B->B) (init:B),
    for_loop (S n) input p init =
      p n input (for_loop n input p init).
Proof. intros. unfold for_loop. simpl. auto. Qed.


(* define the tail-recursive version of for_loop. *)
Fixpoint for_loop_tail_aux {A B:Set} 
  (n k:nat) (input:A) (output:B) (p:nat->A->B->B) {struct n} : B :=
  match n with
    0 => output
  | S m => for_loop_tail_aux m (S k) input (p k input output) p
  end.

Definition for_loop_tail {A B:Set} 
  (n:nat) (input:A) (p:nat->A->B->B) (init:B) : B :=
  for_loop_tail_aux n 0 input init p.


Section test.
  Import Nat.
  Variable input init : nat.
  Variable p : nat -> nat -> nat -> nat.
  Compute for_loop_tail 5 input p init.

  Let p' (idx:nat) (input : nat) (init : nat) : nat :=
        if (idx <? 2)
        then init
        else input + init.
  Opaque Nat.add.
  Eval cbn in for_loop_tail 5 input p' init.
  
End test.

Lemma for_loop_tail_aux_S :
  forall (A B:Set) (n k:nat) 
    (input:A) (output:B) (p:nat->A->B->B) ,
    for_loop_tail_aux (S n) k input output p =
      for_loop_tail_aux n (S k) input (p k input output) p.
Proof. intros. simpl. auto. Qed.

Lemma for_loop_tail_aux_inv :
  forall (A B:Set)  
    (input:A)  (p:nat->A->B->B) (n k:nat) (init:B),
    p (n+k) input (for_loop_tail_aux n k input init p) =
      for_loop_tail_aux n (S k) input (p k input init) p.
Proof.
  intros until p. induction n.
  + reflexivity. 
  + intros. rewrite for_loop_tail_aux_S. rewrite for_loop_tail_aux_S. 
    cut (S n + k = n + S k). intro. rewrite H. 
    rewrite (IHn (S k)). auto. lia.
Qed.

Lemma for_loop_aux_equiv :
  forall {A B:Set}
    (n : nat) (input : A) (p : nat -> A -> B -> B) (init : B),
    for_loop_aux n input init p =
      for_loop_tail_aux n 0 input init p.
Proof.
  intros. induction n.
  + reflexivity. 
  + rewrite for_loop_tail_aux_S. simpl. rewrite IHn.
    rewrite <- for_loop_tail_aux_inv. f_equal. auto.
Qed.

(* tail recursive for_loop and non tail recursive for_loop are equivalent. *)
Lemma for_loop_equiv :
  forall {A B:Set} 
    (n:nat) (input:A) (p:nat->A->B->B) (init:B),
    for_loop n input p init = for_loop_tail n input p init.
Proof.
  unfold for_loop, for_loop_tail.
  intros. apply for_loop_aux_equiv.
Qed.

Lemma for_loop_tail_S :
  forall (A B : Set) (n : nat) 
    (input : A) (p : nat -> A -> B -> B)
    (init : B),
    for_loop_tail (S n) input p init =
      p n input (for_loop_tail n input p init).
Proof.
  intros. rewrite<- ?for_loop_equiv. apply for_loop_S.
Qed.
