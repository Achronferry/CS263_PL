Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Relation_Definitions.
Require Export Coq.ZArith.ZArith.
Require Export Coq.Strings.String.
Require Export Coq.Logic.Classical.

Open Scope Z.   (*必不可少*)

Definition var: Type := nat.

(*定义*)
Inductive aexp : Type :=
  | ANum (n : Z)
  | AId (X : var)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Coercion ANum : Z >-> aexp.

Definition bool_to_bexp (b : bool) : bexp :=
  if b then BTrue else BFalse.
Coercion bool_to_bexp : bool >-> bexp.



Notation "x + y" := (APlus x y) (at level 50, left associativity) : imp_scope.
Notation "x - y" := (AMinus x y) (at level 50, left associativity) : imp_scope.
Notation "x * y" := (AMult x y) (at level 40, left associativity) : imp_scope.
Notation "x <= y" := (BLe x y) (at level 70, no associativity) : imp_scope.
Notation "x == y" := (BEq x y) (at level 70, no associativity) : imp_scope.
Notation "x && y" := (BAnd x y) (at level 40, left associativity) : imp_scope.
Notation "'!' b" := (BNot b) (at level 39, right associativity) : imp_scope.

Definition state: Type := nat -> Z.

Fixpoint aeval (a : aexp) (st : state) : Z :=
  match a with
  | ANum n => n
  | AId X => st X
  | APlus a1 a2 => (aeval a1 st) + (aeval a2 st)
  | AMinus a1 a2  => (aeval a1 st) - (aeval a2 st)
  | AMult a1 a2 => (aeval a1 st) * (aeval a2 st)
  end.

Definition aexp_dequiv (d1 d2: state -> Z): Prop :=
  forall st, d1 st = d2 st.

Definition aexp_equiv (a1 a2: aexp): Prop :=
  aexp_dequiv (aeval a1) (aeval a2).

Fixpoint beval (b : bexp) (st : state) : Prop :=
  match b with
  | BTrue       => True
  | BFalse      => False
  | BEq a1 a2   => (aeval a1 st) = (aeval a2 st)
  | BLe a1 a2   => (aeval a1 st) <= (aeval a2 st)
  | BNot b1     => ~ (beval b1 st)
  | BAnd b1 b2  => (beval b1 st) /\ (beval b2 st)
  end.
  
Inductive aexp_halt: aexp -> Prop :=
  | AH_num : forall n, aexp_halt (ANum n).

Inductive astep : state -> aexp -> aexp -> Prop :=
  | AS_Id : forall st X,
      astep st
        (AId X) (ANum (st X))

  | AS_Plus1 : forall st a1 a1' a2,
      astep st
        a1 a1' ->
      astep st
        (APlus a1 a2) (APlus a1' a2)
  | AS_Plus2 : forall st a1 a2 a2',
      aexp_halt a1 ->
      astep st
        a2 a2' ->
      astep st
        (APlus a1 a2) (APlus a1 a2')
  | AS_Plus : forall st n1 n2,
      astep st
        (APlus (ANum n1) (ANum n2)) (ANum (n1 + n2))

  | AS_Minus1 : forall st a1 a1' a2,
      astep st
        a1 a1' ->
      astep st
        (AMinus a1 a2) (AMinus a1' a2)
  | AS_Minus2 : forall st a1 a2 a2',
      aexp_halt a1 ->
      astep st
        a2 a2' ->
      astep st
        (AMinus a1 a2) (AMinus a1 a2')
  | AS_Minus : forall st n1 n2,
      astep st
        (AMinus (ANum n1) (ANum n2)) (ANum (n1 - n2))

  | AS_Mult1 : forall st a1 a1' a2,
      astep st
        a1 a1' ->
      astep st
        (AMult a1 a2) (AMult a1' a2)
  | AS_Mult2 : forall st a1 a2 a2',
      aexp_halt a1 ->
      astep st
        a2 a2' ->
      astep st
        (AMult a1 a2) (AMult a1 a2')
  | AS_Mult : forall st n1 n2,
      astep st
        (AMult (ANum n1) (ANum n2)) (ANum (n1 * n2)).

Inductive bexp_halt: bexp -> Prop :=
  | BH_True : bexp_halt BTrue
  | BH_False : bexp_halt BFalse.

Inductive bstep : state -> bexp -> bexp -> Prop :=

  | BS_Eq1 : forall st a1 a1' a2,
      astep st
        a1 a1' ->
      bstep st
        (BEq a1 a2) (BEq a1' a2)
  | BS_Eq2 : forall st a1 a2 a2',
      aexp_halt a1 ->
      astep st
        a2 a2' ->
      bstep st
        (BEq a1 a2) (BEq a1 a2')
  | BS_Eq_True : forall st n1 n2,
      n1 = n2 ->
      bstep st
        (BEq (ANum n1) (ANum n2)) BTrue
  | BS_Eq_False : forall st n1 n2,
      n1 <> n2 ->
      bstep st
        (BEq (ANum n1) (ANum n2)) BFalse

  | BS_Le1 : forall st a1 a1' a2,
      astep st
        a1 a1' ->
      bstep st
        (BLe a1 a2) (BLe a1' a2)
  | BS_Le2 : forall st a1 a2 a2',
      aexp_halt a1 ->
      astep st
        a2 a2' ->
      bstep st
        (BLe a1 a2) (BLe a1 a2')
  | BS_Le_True : forall st n1 n2,
      n1 <= n2 ->
      bstep st
        (BLe (ANum n1) (ANum n2)) BTrue
  | BS_Le_False : forall st n1 n2,
      n1 > n2 ->
      bstep st
        (BLe (ANum n1) (ANum n2)) BFalse

  | BS_NotStep : forall st b1 b1',
      bstep st
        b1 b1' ->
      bstep st
        (BNot b1) (BNot b1')
  | BS_NotTrue : forall st,
      bstep st
        (BNot BTrue) BFalse
  | BS_NotFalse : forall st,
      bstep st
        (BNot BFalse) BTrue

  | BS_AndStep : forall st b1 b1' b2,
      bstep st
        b1 b1' ->
      bstep st
       (BAnd b1 b2) (BAnd b1' b2)
  | BS_AndTrue : forall st b,
      bstep st
       (BAnd BTrue b) b
  | BS_AndFalse : forall st b,
      bstep st
       (BAnd BFalse b) BFalse.