Require Import PL.definition_of_abc.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Relation_Definitions.
Arguments clos_refl_trans {A} _ _ _.
Arguments clos_refl_trans_1n {A} _ _ _.
Arguments clos_refl_trans_n1 {A} _ _ _.


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

Inductive stack_ele := 
| Forloop   (c1:com)(b:bexp)(c2 c3 c4:com)
| Whileloop (b:bexp)(c1 c2:com)
| Dowhileloop   (c1:com)(b:bexp)(c2:com).

Definition cstack: Type := list stack_ele.

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

Inductive start_with_while_loop: com -> bexp -> com -> com -> Prop :=
| SWWL_While: forall b c, start_with_while_loop (CWhile b c) b c CSkip
| SWWL_Seq: forall c1 b c11 c12 c2,
             start_with_while_loop c1 b c11 c12 ->
             start_with_while_loop (CSeq c1 c2) b c11 (CSeq c12 c2).

Inductive start_with_for_loop: com -> com -> bexp -> com -> com -> com -> Prop :=
| SWFL_For: forall c1 b c2 c3, start_with_for_loop (CFor c1 b c2 c3) c1 b c3 c2 CSkip
| SWFL_Seq: forall c1 c10 b c11 c12 c13 c2,
             start_with_for_loop c1 c10 b c11 c12 c13 ->
             start_with_for_loop (CSeq c1 c2) c10 b c11 c12 (CSeq c13 c2).

Inductive start_with_dowhile_loop: com -> com -> bexp -> com -> Prop :=
| SWDL_Dowhile: forall c b, start_with_dowhile_loop (CDoWhile c b) c b CSkip
| SWDL_Seq: forall c1 b c11 c12 c2,
             start_with_dowhile_loop c1 c11 b c12 ->
             start_with_dowhile_loop (CSeq c1 c2) c11 b (CSeq c12 c2).

Inductive com': Type :=
| CNormal (s: cstack) (c: com): com'
| CLoopCond (s: cstack) (b: bexp): com'
| CInit (s: cstack) (c: com) com'
| CIncrement (s: cstack) (c: com) com'.

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
      start_with_while_loop c b c1 c2 ->
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



  | CS_DoWhile : forall st s c b c1 c2,
      start_with_dowhile_loop c c1 b c2 ->
      cstep
        (CNormal s c, st)
        (CNormal (cons (c1, b, c2) s) c1, st)
  | CS_DoWhileStep1 : forall st1 st2 s b c1 c2 c1' c1'',
      cstep
        (CNormal (cons (c1, b, c2) s) c1', st1)
        (CNormal (cons (c1, b, c2) s) c1'', st2)
  | CS_DoWhileStep2 : forall st s b b' b'' c1 c2,
      bstep st b' b'' ->
      cstep
        (CLoopCond (cons (c1, b, c2) s) b', st)
        (CLoopCond (cons (c1, b, c2) s) b'', st)
  | CS_DoWhileTrue : forall st s b c1 c2,
      cstep
        (CLoopCond (cons (c1, b, c2) s) BTrue, st)
        (CNormal (cons (c1, b, c2) s) c1, st)
  | CS_DoWhileFalse : forall st s b c1 c2,
      cstep
        (CLoopCond (cons (c1, b, c2) s) BFalse, st)
        (CNormal s c2, st)


  | CS_For : forall st s c c1 b c2 c3 c4,
      start_with_for_loop c c1 b c3 c2 c4 ->
      cstep
        (CNormal s c, st)
        (CInit (cons (c1, b, c3, c2, c4) s) c1, st)
  | CS_ForStep1 : forall st1 st2 s b c1 c2 c3 c4 c1' c1'',
      cstep
        (CInit (cons (c1, b, c3, c2, c4) s) c1', st1)
        (CInit (cons (c1, b, c3, c2, c4) s) c1'', st2)
  | CS_ForStep2 : forall st s b b' b'' c1 c2 c3 c4,
      bstep st b' b'' ->
      cstep
        (CLoopCond (cons (c1, b, c3, c2, c4) s) b', st)
        (CLoopCond (cons (c1, b, c3, c2, c4) s) b'', st)
  | CS_ForTrue : forall st s b c1 c2,
      cstep
        (CLoopCond (cons (c1, b, c3, c2, c4) s) BTrue, st)
        (CNormal (cons (c1, b, c3, c2, c4) s) c3, st)
  | CS_ForFalse : forall st s b c1 c2,
      cstep
        (CLoopCond (cons (c1, b, c3, c2, c4) s) BFalse, st)
        (CNormal s c4, st)


  | CS_WhileSkip : forall st s b c1 c2,
      cstep
        (CNormal (cons (b, c1, c2) s) CSkip, st)
        (CLoopCond (cons (b, c1, c2) s) b, st)

  | CS_DoWhileSkip : forall st s b c1 c2,
      cstep
        (CNormal (cons (c1, b, c2) s) CSkip, st)
        (CLoopCond (cons (c1, b, c2) s) b, st)

  | CS_ForSkip1 : forall st s c1 b c2 c3 c4,
      cstep
        (CInit (cons (c1, b, c3, c2, c4) s) CSkip, st)
        (CLoopCond (cons (c1, b, c3, c2, c4) s) b, st)

  | CS_ForSkip2 : forall st s c1 b c2 c3 c4,
      cstep
        (CNormal (cons (c1, b, c3, c2, c4) s) CSkip, st)
        (CIncrement (cons (c1, b, c3, c2, c4) s) c2, st)

  | CS_WhileBreak : forall st s b c1 c2 c,
      start_with_break c ->
      cstep
        (CNormal (cons (b, c1, c2) s) c, st)
        (CNormal s c2, st)

  | CS_DoWhileBreak : forall st s b c1 c2 c,
      start_with_break c ->
      cstep
        (CNormal (cons (c1, b, c2) s) c, st)
        (CNormal s c2, st)

  | CS_ForBreak : forall st s c1 b c2 c3 c4 c,
      start_with_break c ->
      cstep
        (CNormal (cons (c1, b, c3, c2, c4) s) c, st)
        (CNormal s c4, st)

  | CS_WhileCont : forall st s b c1 c2 c,
      start_with_cont c ->
      cstep
        (CNormal (cons (b, c1, c2) s) c, st)
        (CLoopCond (cons (b, c1, c2) s) b, st)

  | CS_DoWhileCont : forall st s b c1 c2 c,
      start_with_cont c ->
      cstep
        (CNormal (cons (c1, b, c2) s) c, st)
        (CLoopCond (cons (c1, b, c2) s) b, st)

  | CS_ForCont : forall st s c1 b c2 c3 c4 c,
      start_with_cont c ->
      cstep
        (CNormal (cons (c1, b, c3, c2, c4) s) c, st)
        (CLoopNormal (cons (c1, b, c3, c2, c4) s) c2, st)
.


Definition id {A: Type}: A -> A -> Prop := fun a b => a = b.

Definition empty {A B: Type}: A -> B -> Prop := fun a b => False.

(* uncertain *)
Definition concat {A B C D: Type} (r1: A -> D -> B -> Prop) (r2: B -> D -> C -> Prop): A -> D -> C -> Prop :=
  fun a d c => exists b, r1 a d b /\ r2 b d c.

Definition filter1 {A B: Type} (f: A -> Prop): A -> B -> Prop :=
  fun a b => f a.

Definition filter2 {A B: Type} (f: B -> Prop): A -> B -> Prop :=
  fun a b => f b.

Definition union {A B D: Type} (r1 r2: A -> D -> B -> Prop): A -> D -> B -> Prop :=
  fun a d b => r1 a d b \/ r2 a d b.

(* uncertain *)
Definition intersection {A B D: Type} (r1 r2: A -> D -> B -> Prop): A -> D -> B -> Prop :=
  fun a d b => r1 a d b /\ r2 a d b.

Definition omega_union {A B D: Type} (rs: nat -> A -> D -> B -> Prop): A -> D -> B -> Prop :=
  fun st1 ek st2 => exists n, rs n st1 ek st2.

Definition Reflexive {A: Type} (R: A -> A -> Prop): Prop :=
  forall x, R x x.

Definition Transitive {A: Type} (R: A -> A -> Prop): Prop :=
  forall x y z, R x y -> R y z -> R x z.

Definition subrelation {A B: Type} (R R': A -> B -> Prop): Prop:=
  forall (x : A) (y : B), R x y -> R' x y.

Definition is_smallest_relation {A B: Type} (Pr: (A -> B -> Prop) -> Prop) (R: A -> B -> Prop) :=
  Pr R /\ forall R', Pr R' -> subrelation R R'.

Definition com_dequiv (d1 d2: state -> exit_kind -> state -> Prop): Prop :=
  forall st1 EK st2, d1 st1 EK st2 <-> d2 st1 EK st2.

Definition cequiv (c1 c2: com): Prop :=
  com_dequiv (ceval c1) (ceval c2).

(* Theorem loop_recur1: forall b loop_body,
  com_dequiv
    (loop_sem1 b loop_body)
    (union
      (intersection
        (concat loop_body
          (loop_sem1 b loop_body))
        (filter1 (beval b)))
      (intersection
        id
        (filter1 (beval (BNot b))))).
Proof.
  intros.
  unfold com_dequiv.
  intros.
  split.
  + intros.
    unfold loop_sem, omega_union in H.
    unfold union.
    destruct H as [n H].
    destruct n as [| n'].
    - right.
      simpl in H.
      exact H.
    - left.
      simpl in H.
      unfold concat, intersection in H.
      unfold concat, intersection.
      destruct H as [[st' [? ?]] ?].
      split.
      * exists st'.
        split.
        { exact H. }
        unfold loop_sem, omega_union.
        exists n'.
        exact H0.
      * exact H1.
  + intros.
    unfold loop_sem, omega_union.
    unfold union in H.
    destruct H.
    - unfold intersection, concat in H.
      destruct H as [[st' [? ?]] ?].
      unfold loop_sem, omega_union in H0.
      destruct H0 as [n ?].
      exists (S n).
      simpl.
      unfold intersection, concat.
      split.
      * exists st'.
        split.
        { exact H. }
        { exact H0. }
      * exact H1.
    - exists O.
      simpl.
      exact H.
Qed.
 *)
Lemma refl_com_dequiv : forall (d : state -> exit_kind -> state -> Prop),
  com_dequiv d d.
Proof.
  unfold com_dequiv.
  intros.
  tauto.
Qed.

Lemma refl_cequiv : forall (c : com), cequiv c c.
Proof.
  unfold cequiv.
  intros.
  apply refl_com_dequiv.
Qed.

Lemma sym_com_dequiv : forall (d1 d2: state -> exit_kind -> state -> Prop),
  com_dequiv d1 d2 -> com_dequiv d2 d1.
Proof.
Admitted.
(*   unfold com_dequiv.
  intros.
  specialize (H st1 st2).
  tauto.
Qed. *)

Lemma sym_cequiv : forall (c1 c2 : com),
  cequiv c1 c2 -> cequiv c2 c1.
Proof.
  unfold cequiv.
  intros.
  apply sym_com_dequiv.
  exact H.
Qed.

Lemma trans_com_dequiv : forall (d1 d2 d3 : state -> exit_kind -> state -> Prop),
  com_dequiv d1 d2 -> com_dequiv d2 d3 -> com_dequiv d1 d3.
Proof.
Admitted.
(*   unfold com_dequiv.
  intros.
  specialize (H st1 st2).
  specialize (H0 st1 st2).
  tauto.
Qed. *)

Lemma trans_cequiv : forall (c1 c2 c3 : com),
  cequiv c1 c2 -> cequiv c2 c3 -> cequiv c1 c3.
Proof.
  unfold cequiv.
  intros.
  pose proof trans_com_dequiv _ _ _ H H0.
  exact H1.
Qed.

Lemma concat_congruence: forall (d1 d2 d1' d2': state -> exit_kind -> state -> Prop),
  com_dequiv d1 d1' ->
  com_dequiv d2 d2' ->
  com_dequiv (concat d1 d2) (concat d1' d2').
Proof.
Admitted.
(*   unfold com_dequiv.
  intros.
  unfold concat.
  split; intros H1; destruct H1 as [st [? ?]].
  + exists st.
    split.
    - specialize (H st1 st).
      tauto.
    - specialize (H0 st st2).
      tauto.
  + exists st.
    split.
    - specialize (H st1 st).
      tauto.
    - specialize (H0 st st2).
      tauto.
Qed. *)

Lemma intersection_congruence: forall (d1 d2 d1' d2': state -> exit_kind -> state -> Prop),
  com_dequiv d1 d1' ->
  com_dequiv d2 d2' ->
  com_dequiv (intersection d1 d2) (intersection d1' d2').
Proof.
Admitted.
(*   unfold com_dequiv.
  intros.
  unfold intersection.
  specialize (H st1 st2).
  specialize (H0 st1 st2).
  tauto.
Qed. *)

Lemma union_congruence: forall (d1 d2 d1' d2': state -> exit_kind -> state -> Prop),
  com_dequiv d1 d1' ->
  com_dequiv d2 d2' ->
  com_dequiv (union d1 d2) (union d1' d2').
Proof.
Admitted.
(*   unfold com_dequiv.
  intros.
  unfold union.
  specialize (H st1 st2).
  specialize (H0 st1 st2).
  tauto.
Qed. *)

Lemma omega_union_congruence: forall (ds1 ds2: nat -> state -> exit_kind -> state -> Prop),
  (forall n, com_dequiv (ds1 n) (ds2 n)) ->
  com_dequiv (omega_union ds1) (omega_union ds2).
Proof.
Admitted.
(*   unfold com_dequiv.
  intros.
  unfold omega_union.
  split; intros H0; destruct H0 as [n ?]; exists n.
  + specialize (H n st1 st2).
    tauto.
  + specialize (H n st1 st2).
    tauto.
Qed. *)


Definition is_clos_refl_trans {A: Type} (R Rc: A -> A -> Prop): Prop :=
  is_smallest_relation
    (fun Rc' => subrelation R Rc' /\
                Reflexive Rc' /\
                Transitive Rc')
    Rc.



Definition multi_astep (st: state): aexp -> aexp -> Prop := clos_refl_trans (astep st).

Definition multi_bstep (st: state): bexp -> bexp -> Prop := clos_refl_trans (bstep st).

Definition multi_cstep: com' * state -> com' * state -> Prop := clos_refl_trans cstep.


