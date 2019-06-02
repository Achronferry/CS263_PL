Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Relation_Definitions.
Require Export Coq.ZArith.ZArith.
Require Export Coq.Strings.String.
Require Export Coq.Logic.Classical.


Definition var: Type := nat.
Definition state: Type := nat -> Z.


Open Scope Z.

Inductive aexp : Type :=
  | ANum (n : Z)
  | AId (X : var)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Coercion ANum : Z >-> aexp.

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Bind Scope imp_scope with aexp.
Bind Scope imp_scope with bexp.
Delimit Scope imp_scope with imp.

Notation "x + y" := (APlus x y) (at level 50, left associativity) : imp_scope.
Notation "x - y" := (AMinus x y) (at level 50, left associativity) : imp_scope.
Notation "x * y" := (AMult x y) (at level 40, left associativity) : imp_scope.
Notation "x <= y" := (BLe x y) (at level 70, no associativity) : imp_scope.
Notation "x == y" := (BEq x y) (at level 70, no associativity) : imp_scope.
Notation "x && y" := (BAnd x y) (at level 40, left associativity) : imp_scope.
Notation "'!' b" := (BNot b) (at level 39, right associativity) : imp_scope.

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



Definition bool_to_bexp (b : bool) : bexp :=
  if b then BTrue else BFalse.
Coercion bool_to_bexp : bool >-> bexp.

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

Inductive exit_kind: Type :=
  | EK_Normal
  | EK_Break
  | EK_Cont.


Inductive com : Type :=
  | CSkip
  | CAss (X: var) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com)
  | CBreak                       (* <--- new *)
  | CCont                        (* <--- new *)
  | CFor  (c1 : com)(b : bexp) (c2 : com) (c3: com)
  | CDoWhile   (c : com) (b : bexp).

Bind Scope imp_scope with com.
Notation "'Skip'" :=
   CSkip : imp_scope.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity) : imp_scope.
Notation "'While' b 'Do' c 'EndWhile'" :=
  (CWhile b c) (at level 80, right associativity) : imp_scope.
Notation "'If' c1 'Then' c2 'Else' c3 'EndIf'" :=
  (CIf c1 c2 c3) (at level 10, right associativity) : imp_scope.
Notation "'Do' c 'While' b 'EndWhile'" :=
  (CDoWhile c b) (at level 80, right associativity) : imp_scope.
Notation "'For(' c1 ';' b ';' c2 ')' c3 'EndFor'" :=
  (CFor c1 b c2 c3 )(at level 80, right associativity) : imp_scope.
Notation "'Continue'":=
  (CCont)(at level 80, right associativity) : imp_scope.
Notation "'Break'":=
  (CBreak)(at level 80, right associativity) : imp_scope.



Definition skip_sem: state -> exit_kind -> state -> Prop :=
  fun st1 ek st2 =>
    st1 = st2 /\ ek = EK_Normal.

Definition asgn_sem (X: var) (E: aexp): state -> exit_kind -> state -> Prop :=
  fun st1 ek st2 =>
    st2 X = aeval E st1 /\
    forall Y, X <> Y -> st1 Y = st2 Y /\
    ek = EK_Normal.

Definition break_sem: state -> exit_kind -> state -> Prop :=
  fun st1 ek st2 =>
    st1 = st2 /\ ek = EK_Break.

Definition cont_sem: state -> exit_kind -> state -> Prop :=
  fun st1 ek st2 =>
    st1 = st2 /\ ek = EK_Cont.

Definition seq_sem (d1 d2: state -> exit_kind -> state -> Prop)
  : state -> exit_kind -> state -> Prop
:=
  fun st1 ek st3 =>
    (exists st2, d1 st1 EK_Normal st2 /\ d2 st2 ek st3) \/
    (d1 st1 ek st3 /\ ek <> EK_Normal).

Definition if_sem (b: bexp) (d1 d2: state -> exit_kind -> state -> Prop)
  : state -> exit_kind -> state -> Prop
:=
  fun st1 ek st2 =>
    (d1 st1 ek st2 /\ beval b st1) \/
    (d2 st1 ek st2 /\ ~beval b st1).

Fixpoint iter_loop_body1
  (b: bexp)
  (loop_body: state -> exit_kind -> state -> Prop)
  (n: nat)
  : state -> state -> Prop
:=
  match n with
  | O =>
     fun st1 st2 =>
       st1 = st2 /\ ~beval b st1
  | S n' =>
     fun st1 st3 =>
      ((exists st2,
         (loop_body) st1 EK_Normal st2 /\
         (iter_loop_body1 b loop_body n') st2 st3) \/
       (loop_body) st1 EK_Break st3 \/
       (exists st2,
         (loop_body) st1 EK_Cont st2 /\
         (iter_loop_body1 b loop_body n') st2 st3)) /\
       beval b st1
  end.

Definition loop_sem1 (b: bexp) (loop_body: state -> exit_kind -> state -> Prop)
  : state -> exit_kind -> state -> Prop
:=
  fun st1 ek st2 =>
    exists n, (iter_loop_body1 b loop_body n) st1 st2 /\ ek = EK_Normal.

Fixpoint iter_loop_body2
  (b: bexp)
  (loop_body: state -> exit_kind -> state -> Prop)
  (n: nat)
  : state -> state -> Prop
:=
  match n with
  | O =>
     fun st1 st2 =>
       ((loop_body) st1 EK_Normal st2 /\ ~beval b st2)\/
       (loop_body) st1 EK_Break st2 \/
       ((loop_body) st1 EK_Cont st2 /\ ~beval b st2)
  | S n' =>
     fun st1 st3 =>
      ((exists st2,
         (loop_body) st1 EK_Normal st2 /\
         (iter_loop_body2 b loop_body n') st2 st3) \/
       (loop_body) st1 EK_Break st3 \/
       (exists st2,
         (loop_body) st1 EK_Cont st2 /\
         (iter_loop_body2 b loop_body n') st2 st3)) /\
       beval b st3
  end.

Definition loop_sem2 (b: bexp) (loop_body: state -> exit_kind -> state -> Prop)
  : state -> exit_kind -> state -> Prop
:=
  fun st1 ek st2 =>
    exists n, (iter_loop_body2 b loop_body n) st1 st2 /\ ek = EK_Normal.

Fixpoint iter_loop_body3
  (b: bexp)
  (loop_body: state -> exit_kind -> state -> Prop)
  (variant: state -> exit_kind -> state -> Prop)
  (n: nat)
  : state -> state -> Prop
:=
  match n with
  | O =>
     fun st1 st2 =>
       st1 = st2 /\ ~beval b st1
  | S n' =>
     fun st1 st4 =>
      ((exists st2 st3,
         (loop_body) st1 EK_Normal st2 /\
         (variant) st2 EK_Normal st3 /\
         (iter_loop_body3 b loop_body variant n') st3 st4) \/
       (loop_body) st1 EK_Break st4 \/
       (exists st2 st3,
         (loop_body) st1 EK_Cont st2 /\
         (variant) st2 EK_Normal st3 /\
         (iter_loop_body3 b loop_body variant n') st3 st4)) /\
       beval b st1
  end.

Definition loop_sem3 (b: bexp) (loop_body: state -> exit_kind -> state -> Prop) (variant: state -> exit_kind -> state -> Prop)
  : state -> exit_kind -> state -> Prop
:=
  fun st1 ek st2 =>
    exists n, (iter_loop_body3 b loop_body (variant: state -> exit_kind -> state -> Prop) n) st1 st2 /\ ek = EK_Normal.



Fixpoint ceval (c: com): state -> exit_kind -> state -> Prop :=
  match c with
  | CSkip => skip_sem
  | CAss X E => asgn_sem X E
  | CSeq c1 c2 => seq_sem (ceval c1) (ceval c2)
  | CIf b c1 c2 => if_sem b (ceval c1) (ceval c2)
  | CWhile b c => loop_sem1 b (ceval c)
  | CDoWhile c b => seq_sem (ceval c) (loop_sem2 b (ceval c))
  | CFor c1 b c2 c3 => seq_sem (ceval c1) (loop_sem3 b (ceval c3) (ceval c2))
  | CBreak => break_sem
  | CCont => cont_sem
  end.


Definition cstack: Type := list (bexp * com * com).

Inductive start_with_break: com -> Prop :=
| SWB_Break: start_with_break CBreak
| SWB_Seq: forall c1 c2,
             start_with_break c1 ->
             start_with_break (CSeq c1 c2).

Inductive start_with_cont: com -> Prop :=
| SWC_Break: start_with_cont CCont
| SWC_Seq: forall c1 c2,
             start_with_cont c1 ->
             start_with_cont (CSeq c1 c2).

Inductive start_with_loop: com -> bexp -> com -> com -> Prop :=
| SWL_While: forall b c, start_with_loop (CWhile b c) b c CSkip
| SWL_DoWhile :forall b c, start_with_loop (CDoWhile c b) b c c
| SWL_For : forall b c1 c2 c3, start_with_loop (CFor c1 b c2 c3) BTrue c1 (CWhile b (CSeq c2 c3))
| SWL_Seq: forall c1 b c11 c12 c2,
             start_with_loop c1 b c11 c12 ->
             start_with_loop (CSeq c1 c2) b c11 (CSeq c12 c2).

Inductive com': Type :=
| CNormal (s: cstack) (c: com): com'
| CLoopCond (s: cstack) (b: bexp): com'.

Inductive cstep : (com' * state) -> (com' * state) -> Prop :=
  | CS_AssStep : forall st s X a a',
      astep st a a' ->
      cstep
        (CNormal s (CAss X a), st)
        (CNormal s (CAss X a'), st)
  | CS_Ass : forall st1 st2 s X n,
      st2 X = n ->
      (forall Y, X <> Y -> st1 Y = st2 Y) ->
      cstep
        (CNormal s (CAss X (ANum n)), st1)
        (CNormal s CSkip, st2)


  | CS_SeqStep : forall st s c1 c1' st' c2,
      cstep
        (CNormal s c1, st)
        (CNormal s c1', st') ->
      cstep
        (CNormal s (CSeq c1 c2), st)
        (CNormal s (CSeq c1' c2), st')
  | CS_Seq : forall st s c2,
      cstep
        (CNormal s (CSeq CSkip c2), st)
        (CNormal s c2, st)


  | CS_IfStep : forall st s b b' c1 c2,
      bstep st b b' ->
      cstep
        (CNormal s (CIf b c1 c2), st)
        (CNormal s (CIf b' c1 c2), st)
  | CS_IfTrue : forall st s c1 c2,
      cstep
        (CNormal s (CIf BTrue c1 c2), st)
        (CNormal s c1, st)
  | CS_IfFalse : forall st s c1 c2,
      cstep
        (CNormal s (CIf BFalse c1 c2), st)
        (CNormal s c2, st)


  | CS_While : forall st s c b c1 c2,
      start_with_loop c b c1 c2 ->
      cstep
        (CNormal s c, st)
        (CLoopCond (cons (b, c1, c2) s) b, st)
  | CS_WhileStep : forall st s b b' b'' c1 c2,
      bstep st b' b'' ->
      cstep
        (CLoopCond (cons (b, c1, c2) s) b', st)
        (CLoopCond (cons (b, c1, c2) s) b'', st)
  | CS_WhileTrue : forall st s b c1 c2,
      cstep
        (CLoopCond (cons (b, c1, c2) s) BTrue, st)
        (CNormal (cons (b, c1, c2) s) c1, st)
  | CS_WhileFalse : forall st s b c1 c2,
      cstep
        (CLoopCond (cons (b, c1, c2) s) BFalse, st)
        (CNormal s c2, st)


(* Because the definition of SWL_DoWhile,this part is the same with CS_while. *)
  | CS_DoWhile : forall st s c b c1 c2,
      start_with_loop c b c1 c2 ->
      cstep
        (CNormal s c, st)
        (CLoopCond (cons (b, c1, c2) s) b, st)
  | CS_DoWhileStep : forall st s b b' b'' c1 c2,
      bstep st b' b'' ->
      cstep
        (CLoopCond (cons (b, c1, c2) s) b', st)
        (CLoopCond (cons (b, c1, c2) s) b'', st)
  | CS_DoWhileTrue : forall st s b c1 c2,
      cstep
        (CLoopCond (cons (b, c1, c2) s) BTrue, st)
        (CNormal (cons (b, c1, c2) s) c1, st)
  | CS_DoWhileFalse : forall st s b c1 c2,
      cstep
        (CLoopCond (cons (b, c1, c2) s) BFalse, st)
        (CNormal s c2, st)


(* Because the definition of SWL_For,this part is the same with CS_while. *)
  | CS_For : forall st s c b c1 c2,
      start_with_loop c b c1 c2 ->
      cstep
        (CNormal s c, st)
        (CLoopCond (cons (b, c1, c2) s) b, st)
  | CS_ForStep : forall st s b b' b'' c1 c2,
      bstep st b' b'' ->
      cstep
        (CLoopCond (cons (b, c1, c2) s) b', st)
        (CLoopCond (cons (b, c1, c2) s) b'', st)
  | CS_ForTrue : forall st s b c1 c2,
      cstep
        (CLoopCond (cons (b, c1, c2) s) BTrue, st)
        (CNormal (cons (b, c1, c2) s) c1, st)
  | CS_ForFalse : forall st s b c1 c2,
      cstep
        (CLoopCond (cons (b, c1, c2) s) BFalse, st)
        (CNormal s c2, st)


  | CS_Skip : forall st s b c1 c2,
      cstep
        (CNormal (cons (b, c1, c2) s) CSkip, st)
        (CLoopCond (cons (b, c1, c2) s) b, st)


  | CS_Break : forall st s b c1 c2 c,
      start_with_break c ->
      cstep
        (CNormal (cons (b, c1, c2) s) c, st)
        (CNormal s c2, st)


  | CS_Cont : forall st s b c1 c2 c,
      start_with_cont c ->
      cstep
        (CNormal (cons (b, c1, c2) s) c, st)
        (CLoopCond (cons (b, c1, c2) s) b, st)
.
