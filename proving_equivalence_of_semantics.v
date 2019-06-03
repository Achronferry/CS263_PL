Require Import PL.definition_of_two_semantics_v1.
Require Import PL.definition_of_abc.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Relation_Definitions.

Arguments clos_refl_trans {A} _ _ _.
Arguments clos_refl_trans_1n {A} _ _ _.
Arguments clos_refl_trans_n1 {A} _ _ _.


(* ################################################################# *)
(** * Semantic Equavalence: Brief Idea *)

(** This time we will prove the equivalence between denotational semantics and
step step semantics. If you forget the detailed definition, you can always use
the [Print] command in Coq for help. *)

(* Print aeval. *)
(* Print beval. *)
(* Print ceval. *)
(* Print astep. *)
(* Print bstep. *)
(* Print cstep. *)
(* Print multi_astep. *)
(* Print multi_bstep. *)
(* Print multi_cstep. *)

(** We will prove:

    Theorem semantic_equiv: forall c st1 st2,
      ceval c st1 st2 <-> multi_cstep (c, st1) (CSkip, st2).

That is, the binary relation between denotational semantics is the same as the
one defined by multi-step relation. *)

(** To prove this theorem, we need to prove two separate facts: the derivation
from the left hand side to the right hand side and from the right hand side to
the left hand side. *)

(* ================================================================= *)
(** ** => *)

(** For this direction, the main idea is to do induction over the syntax tree
of [c]. A typical induction step is as follows.

    IHc1: forall st1 st2,
            ceval c1 st1 st2 -> multi_cstep (c1, st1) (CSkip, st2)
    IHc2: forall st1 st2,
            ceval c2 st1 st2 -> multi_cstep (c1, st1) (CSkip, st2)
    ----
    To prove: forall st1 st2,
        ceval (c1 ;; c2) st1 st2 -> multi_cstep (c1 ;; c2, st1) (CSkip, st2).

From the fact that [ceval (c1 ;; c2) st1 st2], we know that there exists an
intermidiate state [st3] such that [ceval c1 st1 st3] and [ceval c2 st3 st2].
Then by induction hypothese, we know the following two facts:

    multi_cstep (c1, st1) (CSkip, st3)
    multi_cstep (c2, st3) (CSkip, st2).

Then according to the multi-step relation's congruence property on sequential
composition, we know that

    multi_cstep (c1 ;; c2, st1) (CSkip;; c2, st3)

Adding [cstep (CSkip;; c2, st3) (c2, st3)], we achieve

    multi_cstep (c1 ;; c2, st1) (CSkip, st2).

In this process, we use [multi_cstep]'s the congruence property that we have
proved last time. In other induction steps, we also need semantic equivalence
theorem for [aexp] and [bexp], i.e.,

    Theorem semantic_equiv_bexp1: forall st b,
      (beval b st -> multi_bstep st b BTrue) /\
      (~ beval b st -> multi_bstep st b BFalse).

    Theorem semantic_equiv_aexp1: forall st a n,
      aeval a st = n -> multi_astep st a (ANum n).
*)

(* ================================================================= *)
(** ** <= *)

(** For the reverse direction, we can also do induction over [c]'s structure.
If we still use sequential composition [CSeq] as an example, what we need to
prove is:

    IHc1: forall st1 st2,
            multi_cstep (c1, st1) (CSkip, st2) -> ceval c1 st1 st2
    IHc2: forall st1 st2,
            multi_cstep (c1, st1) (CSkip, st2) -> ceval c2 st1 st2
    ----
    To prove: forall st1 st2,
        multi_cstep (c1 ;; c2, st1) (CSkip, st2) -> ceval (c1 ;; c2) st1 st2.

The key point is: suppose [multi_cstep (c1 ;; c2, st1) (CSkip, st2)], this path
of program execution must contain the following two intermediate status:

    (CSkip;; c2, st3)
    (c2, st3)

for some program state [st3]. Furthermore, we can construct another path from
[(c1, st1)] to [(CSkip, st3)] based on the path from [(c1;; c2, st1)] to
[(CSkip;; c2, st3)]. This whole property can be formally stated as follows:

    Lemma CSeq_path_spec: forall c1 st1 c2 st2,
      multi_cstep (CSeq c1 c2, st1) (CSkip, st2) ->
      exists st3,
      multi_cstep (c1, st1) (CSkip, st3) /\
      multi_cstep (c2, st3) (CSkip, st2).

Then we can prove our goal easily using two induction hypotheses.

In general, in the proof of all different induction steps, we need to prove
different path properties for different commands. *)

(* ================================================================= *)
(** ** <=: Alternative proof *)

(** To show:

    Theorem semantic_equiv_com2: forall c st1 st2,
      multi_cstep (c, st1) (CSkip, st2) -> ceval c st1 st2.

We have another proof strategy besides doing induction over [c]. We can do
induction over the steps from [(c, st1)] to [(CSkip, st2)] instead.
Specifically, we first prove:

    Lemma ceval_preserve: forall c1 c2 st1 st2,
      cstep (c1, st1) (c2, st2) ->
      forall st3, ceval c2 st2 st3 -> ceval c1 st1 st3;

by induction over "how [cstep]" is constructed. Then we generalize it to:

    Lemma ceval_preserve': forall c1 c2 st1 st2,
      multi_cstep (c1, st1) (c2, st2) ->
      forall st3, ceval c2 st2 st3 -> ceval c1 st1 st3;

by induction over the steps. Our eventual goal [semantic_equiv_com2] immediately
follows.

Now, we demonstrate our proofs in Coq. *)

(* ################################################################# *)
(** * Auxiliary Lemmas For Constructing Multi-step Relations *)

Lemma multi_astep_refl: forall st a,
  multi_astep st a a.
Proof.
  unfold multi_astep.
  intros.
  apply rt_refl.
Qed.

Lemma multi_astep_step: forall {st a1 a2},
  astep st a1 a2 ->
  multi_astep st a1 a2.
Proof.
  unfold multi_astep.
  intros.
  apply rt_step.
  exact H.
Qed.

Lemma multi_astep_trans: forall {st a1 a2 a3},
  multi_astep st a1 a2 ->
  multi_astep st a2 a3 ->
  multi_astep st a1 a3.
Proof.
  unfold multi_astep.
  intros.
  eapply rt_trans.
  + exact H.
  + exact H0.
Qed.

Lemma multi_astep_trans_n1: forall {st a1 a2 a3},
  multi_astep st a1 a2 ->
  astep st a2 a3 ->
  multi_astep st a1 a3.
Proof.
  unfold multi_astep.
  intros.
  eapply rt_trans.
  + exact H.
  + apply rt_step.
    exact H0.
Qed.

Lemma multi_astep_trans_1n: forall {st a1 a2 a3},
  astep st a1 a2 ->
  multi_astep st a2 a3 ->
  multi_astep st a1 a3.
Proof.
  unfold multi_astep.
  intros.
  eapply rt_trans.
  + apply rt_step.
    exact H.
  + exact H0.
Qed.

Lemma multi_bstep_refl: forall st b,
  multi_bstep st b b.
Proof.
  unfold multi_bstep.
  intros.
  apply rt_refl.
Qed.

Lemma multi_bstep_step: forall {st b1 b2},
  bstep st b1 b2 ->
  multi_bstep st b1 b2.
Proof.
  unfold multi_bstep.
  intros.
  apply rt_step.
  exact H.
Qed.

Lemma multi_bstep_trans: forall {st b1 b2 b3},
  multi_bstep st b1 b2 ->
  multi_bstep st b2 b3 ->
  multi_bstep st b1 b3.
Proof.
  unfold multi_bstep.
  intros.
  eapply rt_trans.
  + exact H.
  + exact H0.
Qed.

Lemma multi_bstep_trans_n1: forall {st b1 b2 b3},
  multi_bstep st b1 b2 ->
  bstep st b2 b3 ->
  multi_bstep st b1 b3.
Proof.
  unfold multi_bstep.
  intros.
  eapply rt_trans.
  + exact H.
  + apply rt_step.
    exact H0.
Qed.

Lemma multi_bstep_trans_1n: forall {st b1 b2 b3},
  bstep st b1 b2 ->
  multi_bstep st b2 b3 ->
  multi_bstep st b1 b3.
Proof.
  unfold multi_bstep.
  intros.
  eapply rt_trans.
  + apply rt_step.
    exact H.
  + exact H0.
Qed.

Lemma multi_cstep_refl: forall st c,
  multi_cstep (c, st) (c, st).
Proof.
  unfold multi_cstep.
  intros.
  apply rt_refl.
Qed.

Lemma multi_cstep_step: forall {st1 st2 c1 c2},
  cstep (c1, st1) (c2, st2) ->
  multi_cstep (c1, st1) (c2, st2).
Proof.
  unfold multi_cstep.
  intros.
  apply rt_step.
  exact H.
Qed.

Lemma multi_cstep_trans: forall {st1 st2 st3 c1 c2 c3},
  multi_cstep (c1, st1) (c2, st2) ->
  multi_cstep (c2, st2) (c3, st3) ->
  multi_cstep (c1, st1) (c3, st3).
Proof.
  unfold multi_cstep.
  intros.
  eapply rt_trans.
  + exact H.
  + exact H0.
Qed.

Lemma multi_cstep_trans_n1: forall {st1 st2 st3 c1 c2 c3},
  multi_cstep (c1, st1) (c2, st2) ->
  cstep (c2, st2) (c3, st3) ->
  multi_cstep (c1, st1) (c3, st3).
Proof.
  unfold multi_cstep.
  intros.
  eapply rt_trans.
  + exact H.
  + apply rt_step.
    exact H0.
Qed.

Lemma multi_cstep_trans_1n: forall {st1 st2 st3 c1 c2 c3},
  cstep (c1, st1) (c2, st2) ->
  multi_cstep (c2, st2) (c3, st3) ->
  multi_cstep (c1, st1) (c3, st3).
Proof.
  unfold multi_cstep.
  intros.
  eapply rt_trans.
  + apply rt_step.
    exact H.
  + exact H0.
Qed.

(* ################################################################# *)
(** * Auxiliary Lemmas For Induction *)

Lemma multi_astep_ind_n1: forall st (P: aexp -> aexp -> Prop),
  (forall a, P a a) ->
  (forall a1 a2 a3 (IH: P a1 a2),
    multi_astep st a1 a2 ->
    astep st a2 a3 ->
    P a1 a3) ->
  (forall a1 a2,
    multi_astep st a1 a2 ->
    P a1 a2).
Proof.
  intros.
  unfold multi_astep in H1.
  apply Operators_Properties.clos_rt_rtn1_iff in H1.
  induction H1.
  + apply H.
  + apply Operators_Properties.clos_rt_rtn1_iff in H2.
    unfold multi_astep in H0.
    pose proof H0 _ y _ IHclos_refl_trans_n1 H2 H1.
    exact H3.
Qed.

Lemma multi_bstep_ind_n1: forall st (P: bexp -> bexp -> Prop),
  (forall b, P b b) ->
  (forall b1 b2 b3 (IH: P b1 b2),
    multi_bstep st b1 b2 ->
    bstep st b2 b3 ->
    P b1 b3) ->
  (forall b1 b2,
    multi_bstep st b1 b2 ->
    P b1 b2).
Proof.
  intros.
  unfold multi_bstep in H1.
  apply Operators_Properties.clos_rt_rtn1_iff in H1.
  induction H1.
  + apply H.
  + apply Operators_Properties.clos_rt_rtn1_iff in H2.
    unfold multi_bstep in H0.
    pose proof H0 _ y _ IHclos_refl_trans_n1 H2 H1.
    exact H3.
Qed.

Lemma multi_cstep_ind_n1: forall (P: com' -> state -> com' -> state -> Prop),
  (forall c st, P c st c st) ->
  (forall c1 c2 c3 st1 st2 st3 (IH: P c1 st1 c2 st2),
    multi_cstep (c1, st1) (c2, st2) ->
    cstep (c2, st2) (c3, st3) ->
    P c1 st1 c3 st3) ->
  (forall c1 c2 st1 st2,
    multi_cstep (c1, st1) (c2, st2) ->
    P c1 st1 c2 st2).
Proof.
  intros.
  unfold multi_cstep in H1.
  apply Operators_Properties.clos_rt_rtn1_iff in H1.
  remember (c1, st1) as cst1 eqn:HH1.
  remember (c2, st2) as cst2 eqn:HH2.
  revert c1 c2 st1 st2 HH1 HH2; induction H1; intros; subst.
  + injection HH2 as ? ?.
    subst.
    apply H.
  + apply Operators_Properties.clos_rt_rtn1_iff in H2.
    destruct y as [c0 st0].
    unfold multi_cstep in H0.
    assert ((c1, st1) = (c1, st1)). { reflexivity. }
    assert ((c0, st0) = (c0, st0)). { reflexivity. }
    pose proof IHclos_refl_trans_n1 _ _ _ _ H3 H4.
    pose proof H0 _ c0 _ _ st0 _ H5 H2 H1.
    exact H6.
Qed.

Lemma multi_astep_ind_1n: forall st (P: aexp -> aexp -> Prop),
  (forall a, P a a) ->
  (forall a1 a2 a3 (IH: P a2 a3),
    astep st a1 a2 ->
    multi_astep st a2 a3 ->
    P a1 a3) ->
  (forall a1 a2,
    multi_astep st a1 a2 ->
    P a1 a2).
Proof.
  intros.
  unfold multi_astep in H1.
  apply Operators_Properties.clos_rt_rt1n_iff in H1.
  induction H1.
  + apply H.
  + apply Operators_Properties.clos_rt_rt1n_iff in H2.
    unfold multi_astep in H0.
    pose proof H0 _ y _ IHclos_refl_trans_1n H1 H2.
    exact H3.
Qed.

Lemma multi_bstep_ind_1n: forall st (P: bexp -> bexp -> Prop),
  (forall b, P b b) ->
  (forall b1 b2 b3 (IH: P b2 b3),
    bstep st b1 b2 ->
    multi_bstep st b2 b3 ->
    P b1 b3) ->
  (forall b1 b2,
    multi_bstep st b1 b2 ->
    P b1 b2).
Proof.
  intros.
  unfold multi_bstep in H1.
  apply Operators_Properties.clos_rt_rt1n_iff in H1.
  induction H1.
  + apply H.
  + apply Operators_Properties.clos_rt_rt1n_iff in H2.
    unfold multi_bstep in H0.
    pose proof H0 _ y _ IHclos_refl_trans_1n H1 H2.
    exact H3.
Qed.

Lemma multi_cstep_ind_1n: forall (P: com' -> state -> com' -> state -> Prop),
  (forall c st, P c st c st) ->
  (forall c1 c2 c3 st1 st2 st3 (IH: P c2 st2 c3 st3),
    cstep (c1, st1) (c2, st2) ->
    multi_cstep (c2, st2) (c3, st3) ->
    P c1 st1 c3 st3) ->
  (forall c1 c2 st1 st2,
    multi_cstep (c1, st1) (c2, st2) ->
    P c1 st1 c2 st2).
Proof.
  intros.
  unfold multi_cstep in H1.
  apply Operators_Properties.clos_rt_rt1n_iff in H1.
  remember (c1, st1) as cst1 eqn:HH1.
  remember (c2, st2) as cst2 eqn:HH2.
  revert c1 c2 st1 st2 HH1 HH2; induction H1; intros; subst.
  + injection HH2 as ? ?.
    subst.
    apply H.
  + apply Operators_Properties.clos_rt_rt1n_iff in H2.
    destruct y as [c0 st0].
    unfold multi_cstep in H0.
    assert ((c0, st0) = (c0, st0)). { reflexivity. }
    assert ((c2, st2) = (c2, st2)). { reflexivity. }
    pose proof IHclos_refl_trans_1n _ _ _ _ H3 H4.
    pose proof H0 _ c0 _ _ st0 _ H5 H1 H2.
    exact H6.
Qed.

Ltac induction_n1 H :=
  match type of H with
  | multi_astep ?st ?a1 ?a2 =>
      match goal with
      | |- ?P =>
           let Q := eval pattern a1, a2 in P in
           match Q with
           | ?R a1 a2 =>
             revert a1 a2 H;
             refine (multi_astep_ind_n1 st R _ _);
             [intros a1 | intros a1 ?a1 a2 ? ? ?]
           end
      end
  | multi_bstep ?st ?b1 ?b2 =>
      match goal with
      | |- ?P =>
           let Q := eval pattern b1, b2 in P in
           match Q with
           | ?R b1 b2 =>
             revert b1 b2 H;
             refine (multi_bstep_ind_n1 st R _ _);
             [intros b1 | intros b1 ?b1 b2 ? ? ?]
           end
      end
  | multi_cstep (?c1, ?st1) (?c2, ?st2) =>
      match goal with
      | |- ?P =>
           let Q := eval pattern c1, st1, c2, st2 in P in
           match Q with
           | ?R c1 st1 c2 st2 =>
             revert c1 c2 st1 st2 H;
             refine (multi_cstep_ind_n1 R _ _);
             [intros c1 st1 | intros c1 ?c1 c2 st1 ?st1 st2 ? ? ?]
           end
      end
  end.

Ltac induction_1n H :=
  match type of H with
  | multi_astep ?st ?a1 ?a2 =>
      match goal with
      | |- ?P =>
           let Q := eval pattern a1, a2 in P in
           match Q with
           | ?R a1 a2 =>
             revert a1 a2 H;
             refine (multi_astep_ind_1n st R _ _);
             [intros a1 | intros a1 ?a1 a2 ? ? ?]
           end
      end
  | multi_bstep ?st ?b1 ?b2 =>
      match goal with
      | |- ?P =>
           let Q := eval pattern b1, b2 in P in
           match Q with
           | ?R b1 b2 =>
             revert b1 b2 H;
             refine (multi_bstep_ind_1n st R _ _);
             [intros b1 | intros b1 ?b1 b2 ? ? ?]
           end
      end
  | multi_cstep (?c1, ?st1) (?c2, ?st2) =>
      match goal with
      | |- ?P =>
           let Q := eval pattern c1, st1, c2, st2 in P in
           match Q with
           | ?R c1 st1 c2 st2 =>
             revert c1 c2 st1 st2 H;
             refine (multi_cstep_ind_1n R _ _);
             [intros c1 st1 | intros c1 ?c1 c2 st1 ?st1 st2 ? ? ?]
           end
      end 
  end.

(* ################################################################# *)
(** * Congruence Theorems of Multi-step Relations *)

Theorem multi_congr_APlus1: forall st a1 a1' a2,
  multi_astep st a1 a1' ->
  multi_astep st (a1 + a2) (a1' + a2).
Proof.
  intros.
  induction_n1 H.
  + apply multi_astep_refl.
  + eapply multi_astep_trans_n1.
    - exact IH.
    - apply AS_Plus1.
      exact H0.
Qed.

Theorem multi_congr_APlus2: forall st a1 a2 a2',
  aexp_halt a1 ->
  multi_astep st a2 a2' ->
  multi_astep st (a1 + a2) (a1 + a2').
Proof.
  intros.
  induction_n1 H0.
  + apply multi_astep_refl.
  + eapply multi_astep_trans_n1.
    - exact IH.
    - apply AS_Plus2.
      * exact H.
      * exact H1.
Qed.

Theorem multi_congr_AMinus1: forall st a1 a1' a2,
  multi_astep st a1 a1' ->
  multi_astep st (a1 - a2) (a1' - a2).
Proof.
  intros.
  induction_n1 H.
  + apply multi_astep_refl.
  + eapply multi_astep_trans_n1.
    - exact IH.
    - apply AS_Minus1.
      exact H0.
Qed.

Theorem multi_congr_AMinus2: forall st a1 a2 a2',
  aexp_halt a1 ->
  multi_astep st a2 a2' ->
  multi_astep st (a1 - a2) (a1 - a2').
Proof.
  intros.
  induction_n1 H0.
  + apply multi_astep_refl.
  + eapply multi_astep_trans_n1.
    - exact IH.
    - apply AS_Minus2.
      * exact H.
      * exact H1.
Qed.

Theorem multi_congr_AMult1: forall st a1 a1' a2,
  multi_astep st a1 a1' ->
  multi_astep st (a1 * a2) (a1' * a2).
Proof.
  intros.
  induction_n1 H.
  + apply multi_astep_refl.
  + eapply multi_astep_trans_n1.
    - exact IH.
    - apply AS_Mult1.
      exact H0.
Qed.

Theorem multi_congr_AMult2: forall st a1 a2 a2',
  aexp_halt a1 ->
  multi_astep st a2 a2' ->
  multi_astep st (a1 * a2) (a1 * a2').
Proof.
  intros.
  induction_n1 H0.
  + apply multi_astep_refl.
  + eapply multi_astep_trans_n1.
    - exact IH.
    - apply AS_Mult2.
      * exact H.
      * exact H1.
Qed.

Theorem multi_congr_BEq1: forall st a1 a1' a2,
  multi_astep st a1 a1' ->
  multi_bstep st (a1 == a2) (a1' == a2).
Proof.
  intros.
  induction_n1 H.
  + apply multi_bstep_refl.
  + eapply multi_bstep_trans_n1.
    - exact IH.
    - apply BS_Eq1.
      exact H0.
Qed.

Theorem multi_congr_BEq2: forall st a1 a2 a2',
  aexp_halt a1 ->
  multi_astep st a2 a2' ->
  multi_bstep st (a1 == a2) (a1 == a2').
Proof.
  intros.
  induction_n1 H0.
  + apply multi_bstep_refl.
  + eapply multi_bstep_trans_n1.
    - exact IH.
    - apply BS_Eq2.
      * exact H.
      * exact H1.
Qed.

Theorem multi_congr_BLe1: forall st a1 a1' a2,
  multi_astep st a1 a1' ->
  multi_bstep st (a1 <= a2) (a1' <= a2).
Proof.
  intros.
  induction_n1 H.
  + apply multi_bstep_refl.
  + eapply multi_bstep_trans_n1.
    - exact IH.
    - apply BS_Le1.
      exact H0.
Qed.

Theorem multi_congr_BLe2: forall st a1 a2 a2',
  aexp_halt a1 ->
  multi_astep st a2 a2' ->
  multi_bstep st (a1 <= a2) (a1 <= a2').
Proof.
  intros.
  induction_n1 H0.
  + apply multi_bstep_refl.
  + eapply multi_bstep_trans_n1.
    - exact IH.
    - apply BS_Le2.
      * exact H.
      * exact H1.
Qed.

Theorem multi_congr_BNot: forall st b b',
  multi_bstep st b b' ->
  multi_bstep st (BNot b) (BNot b').
Proof.
  intros.
  induction_n1 H.
  + apply multi_bstep_refl.
  + eapply multi_bstep_trans_n1.
    - apply IH.
    - apply BS_NotStep.
      exact H0.
Qed.

Theorem multi_congr_BAnd: forall st b1 b1' b2,
  multi_bstep st b1 b1' ->
  multi_bstep st (BAnd b1 b2) (BAnd b1' b2).
Proof.
  intros.
  induction_n1 H.
  + apply multi_bstep_refl.
  + eapply multi_bstep_trans_n1.
    - apply IH.
    - apply BS_AndStep.
      exact H0.
Qed.

Theorem multi_congr_CAss: forall st s X a a',
  multi_astep st a a' ->
  multi_cstep (CNormal s (CAss X a), st)
        (CNormal s (CAss X a'), st).
Proof.
  intros.
  induction_n1 H.
  + apply multi_cstep_refl.
  + eapply multi_cstep_trans_n1.
    - exact IH.
    - apply CS_AssStep.
      exact H0.
Qed.

Theorem multi_congr_CSeq: forall st1 s c1 st1' c1' c2,
  multi_cstep (CNormal s c1, st1)
        (CNormal s c1', st1') ->
  multi_cstep (CNormal s (CSeq c1 c2), st1)
        (CNormal s (CSeq c1' c2), st1').
Proof.
Admitted.
(* 
  intros.
  induction_n1 H.
  + apply multi_cstep_refl.
  + eapply multi_cstep_trans_n1.
    - exact IH.
    - apply CS_SeqStep.
      exact H0.
Qed. *)

Theorem multi_congr_CIf: forall st s b b' c1 c2,
  multi_bstep st b b' ->
  multi_cstep
    (CNormal s (CIf b c1 c2), st)
        (CNormal s (CIf b' c1 c2), st).
Proof.
  intros.
  induction_n1 H.
  + apply multi_cstep_refl.
  + eapply multi_cstep_trans_n1.
    - exact IH.
    - apply CS_IfStep.
      exact H0.
Qed.

(* ################################################################# *)
(** * From Denotations To Multi-step Relations *)

Theorem semantic_equiv_aexp1: forall st a n,
  aeval a st = n -> multi_astep st a (ANum n).
Proof.
  intros.
  revert n H; induction a; intros; simpl in H.
  + simpl in H.
    rewrite H.
    apply multi_astep_refl.
  + rewrite <- H.
    apply multi_astep_step.
    apply AS_Id.
  + assert (aeval a1 st = aeval a1 st).
    { reflexivity. }
    pose proof IHa1 _ H0.
    pose proof multi_congr_APlus1 _ _ _ a2 H1 as IH1.
    clear IHa1 H0 H1.
    assert (aeval a2 st = aeval a2 st).
    { reflexivity. }
    pose proof IHa2 _ H0.
    pose proof AH_num (aeval a1 st).
    pose proof multi_congr_APlus2 _ _ _ _ H2 H1 as IH2.
    clear IHa2 H0 H1 H2.
    pose proof AS_Plus st (aeval a1 st) (aeval a2 st).
    rewrite H in H0.
    pose proof multi_astep_trans IH1 IH2.
    pose proof multi_astep_trans_n1 H1 H0.
    exact H2.
  + assert (aeval a1 st = aeval a1 st).
    { reflexivity. }
    pose proof IHa1 _ H0.
    pose proof multi_congr_AMinus1 _ _ _ a2 H1 as IH1.
    clear IHa1 H0 H1.
    assert (aeval a2 st = aeval a2 st).
    { reflexivity. }
    pose proof IHa2 _ H0.
    pose proof AH_num (aeval a1 st).
    pose proof multi_congr_AMinus2 _ _ _ _ H2 H1 as IH2.
    clear IHa2 H0 H1 H2.
    pose proof AS_Minus st (aeval a1 st) (aeval a2 st).
    rewrite H in H0.
    pose proof multi_astep_trans IH1 IH2.
    pose proof multi_astep_trans_n1 H1 H0.
    exact H2.
  + assert (aeval a1 st = aeval a1 st).
    { reflexivity. }
    pose proof IHa1 _ H0.
    pose proof multi_congr_AMult1 _ _ _ a2 H1 as IH1.
    clear IHa1 H0 H1.
    assert (aeval a2 st = aeval a2 st).
    { reflexivity. }
    pose proof IHa2 _ H0.
    pose proof AH_num (aeval a1 st).
    pose proof multi_congr_AMult2 _ _ _ _ H2 H1 as IH2.
    clear IHa2 H0 H1 H2.
    pose proof AS_Mult st (aeval a1 st) (aeval a2 st).
    rewrite H in H0.
    pose proof multi_astep_trans IH1 IH2.
    pose proof multi_astep_trans_n1 H1 H0.
    exact H2.
Qed.

Theorem semantic_equiv_bexp1: forall st b,
  (beval b st -> multi_bstep st b BTrue) /\
  (~ beval b st -> multi_bstep st b BFalse).
Proof.
  intros.
  induction b; simpl.
  + split.
    - intros.
      apply multi_bstep_refl.
    - tauto.
  + split.
    - tauto.
    - intros.
      apply multi_bstep_refl.
  + assert (aeval a1 st = aeval a1 st).
    { reflexivity. }
    pose proof semantic_equiv_aexp1 st a1 _ H.
    pose proof multi_congr_BEq1 _ _ _ a2 H0 as IH1.
    clear H H0.
    assert (aeval a2 st = aeval a2 st).
    { reflexivity. }
    pose proof semantic_equiv_aexp1 st a2 _ H.
    pose proof AH_num (aeval a1 st).
    pose proof multi_congr_BEq2 _ _ _ _ H1 H0 as IH2.
    clear H H0 H1.
    
    split; intros.
    - pose proof BS_Eq_True st _ _ H.
      pose proof multi_bstep_trans IH1 IH2.
      pose proof multi_bstep_trans_n1 H1 H0.
      exact H2.
    - pose proof BS_Eq_False st _ _ H.
      pose proof multi_bstep_trans IH1 IH2.
      pose proof multi_bstep_trans_n1 H1 H0.
      exact H2.
  + assert (aeval a1 st = aeval a1 st).
    { reflexivity. }
    pose proof semantic_equiv_aexp1 st a1 _ H.
    pose proof multi_congr_BLe1 _ _ _ a2 H0 as IH1.
    clear H H0.
    assert (aeval a2 st = aeval a2 st).
    { reflexivity. }
    pose proof semantic_equiv_aexp1 st a2 _ H.
    pose proof AH_num (aeval a1 st).
    pose proof multi_congr_BLe2 _ _ _ _ H1 H0 as IH2.
    clear H H0 H1.
    
    split; intros.
    - pose proof BS_Le_True st _ _ H.
      pose proof multi_bstep_trans IH1 IH2.
      pose proof multi_bstep_trans_n1 H1 H0.
      exact H2.
    - assert (aeval a1 st > aeval a2 st). { omega. }
      pose proof BS_Le_False st _ _ H0.
      pose proof multi_bstep_trans IH1 IH2.
      pose proof multi_bstep_trans_n1 H2 H1.
      exact H3.
  + destruct IHb as [IH1 IH2].
    split; intros.
    - specialize (IH2 H).
      pose proof multi_congr_BNot st _ _ IH2.
      pose proof BS_NotFalse st.
      pose proof multi_bstep_trans_n1 H0 H1.
      exact H2.
    - assert (multi_bstep st b BTrue). { tauto. }
      pose proof multi_congr_BNot st _ _ H0.
      pose proof BS_NotTrue st.
      pose proof multi_bstep_trans_n1 H1 H2.
      exact H3.
  + destruct IHb1 as [IHb11 IHb12].
    destruct IHb2 as [IHb21 IHb22].
    pose proof classic (beval b1 st).
    destruct H.
    - specialize (IHb11 H).
      pose proof multi_congr_BAnd _ _ _ b2 IHb11.
      pose proof BS_AndTrue st b2.
      split.
      * intros.
        destruct H2.
        specialize (IHb21 H3).
        pose proof multi_bstep_trans_n1 H0 H1.
        pose proof multi_bstep_trans H4 IHb21.
        exact H5.
      * intros.
        assert (~beval b2 st). { tauto. }
        specialize (IHb22 H3).
        pose proof multi_bstep_trans_n1 H0 H1.
        pose proof multi_bstep_trans H4 IHb22.
        exact H5.
    - split; intros. { tauto. }
      specialize (IHb12 H).
      pose proof multi_congr_BAnd _ _ _ b2 IHb12.
      pose proof BS_AndFalse st b2.
      pose proof multi_bstep_trans_n1 H1 H2.
      exact H3.
Qed.

Lemma semantic_equiv_iter_loop1: forall st1 EK st2 n b c s,
  (forall st1 st2, ceval c st1 EK st2 -> multi_cstep (CNormal s c, st1) (CNormal s CSkip, st2)) ->
  iter_loop_body1 b (ceval c) n st1 st2 ->
  multi_cstep (CLoopCond (cons (b, c, CSkip) s) b, st1) (CNormal s CSkip, st2).
Proof.
Admitted.
(*   intros.
  revert st1 st2 H0; induction n; intros.
  + simpl in H0.
    unfold Relation_Operators.intersection,
           Relation_Operators.filter1,
           Relation_Operators.id in H0.
    destruct H0.
    subst st2.
    pose proof CS_While st1 b c.
    pose proof semantic_equiv_bexp1 st1 b.
    assert (multi_bstep st1 b BFalse). { tauto. }
    pose proof multi_congr_CIf _ _ _ (c;; While b Do c EndWhile) Skip H3.
    pose proof CS_IfFalse st1 (c;; While b Do c EndWhile) Skip.
    pose proof multi_cstep_trans_1n H0 H4.
    pose proof multi_cstep_trans_n1 H6 H5.
    exact H7.
  + simpl in H0.
    unfold Relation_Operators.concat,
           Relation_Operators.intersection,
           Relation_Operators.filter1,
           Relation_Operators.id in H0.
    destruct H0 as [[st [? ?]] ?].

    pose proof CS_While st1 b c as STEP1.
    
    pose proof semantic_equiv_bexp1 st1 b.
    assert (multi_bstep st1 b BTrue). { tauto. }
    pose proof multi_congr_CIf _ _ _ (c;; While b Do c EndWhile) Skip H4
      as STEP2.
    clear H4 H3 H2.
    
    pose proof CS_IfTrue st1 (c;; While b Do c EndWhile) Skip as STEP3.
    
    pose proof H _ _ H0.
    pose proof multi_congr_CSeq _ _ _ _ (While b Do c EndWhile) H2 as STEP4.
    clear H H0 H2.
    
    pose proof CS_Seq st (While b Do c EndWhile) as STEP5.
    
    pose proof IHn _ _ H1 as STEP6.
    clear IHn H1.
    
    pose proof multi_cstep_trans_1n STEP1 STEP2.
    pose proof multi_cstep_trans_n1 H STEP3.
    pose proof multi_cstep_trans H0 STEP4.
    pose proof multi_cstep_trans_n1 H1 STEP5.
    pose proof multi_cstep_trans H2 STEP6.
    exact H3.
Qed.
 *)
Theorem semantic_equiv_com1: forall st1 st2 c s EK,
  ceval c st1 EK st2 -> multi_cstep (CNormal s c, st1) (CNormal s CSkip, st2).
Proof.
Admitted.
(*   intros.
  revert st1 st2 H; induction c; intros; simpl in H.
  + unfold Relation_Operators.id in H.
    rewrite H.
    apply multi_cstep_refl.
  + destruct H.
    assert (aeval a st1 = aeval a st1).
    { reflexivity. }
    pose proof semantic_equiv_aexp1 _ _ _ H1.
    pose proof multi_congr_CAss st1 X _ _ H2.
    pose proof CS_Ass _ _ _ _ H H0.
    pose proof multi_cstep_trans_n1 H3 H4.
    exact H5.
  + unfold Relation_Operators.concat in H.
    destruct H as [st' [? ?]].
    specialize (IHc1 _ _ H).
    specialize (IHc2 _ _ H0).
    pose proof multi_congr_CSeq _ _ _ _ c2 IHc1.
    pose proof CS_Seq st' c2.
    pose proof multi_cstep_trans_n1 H1 H2.
    pose proof multi_cstep_trans H3 IHc2.
    exact H4.
  + unfold if_sem in H.
    unfold Relation_Operators.union, Relation_Operators.intersection,
           Relation_Operators.filter1 in H.
    pose proof semantic_equiv_bexp1 st1 b.
    destruct H0.
    destruct H as [[? ?] | [? ?]].
    - specialize (H0 H2).
      pose proof IHc1 _ _ H.
      clear H H1 H2 IHc1 IHc2.
      pose proof multi_congr_CIf _ _ _ c1 c2 H0.
      pose proof CS_IfTrue st1 c1 c2.
      pose proof multi_cstep_trans_n1 H H1.
      pose proof multi_cstep_trans H2 H3.
      exact H4.
    - specialize (H1 H2).
      pose proof IHc2 _ _ H.
      clear H H0 H2 IHc1 IHc2.
      pose proof multi_congr_CIf _ _ _ c1 c2 H1.
      pose proof CS_IfFalse st1 c1 c2.
      pose proof multi_cstep_trans_n1 H H0.
      pose proof multi_cstep_trans H2 H3.
      exact H4.
  + unfold loop_sem in H.
    unfold Relation_Operators.omega_union in H.
    destruct H as [n ?].
    apply semantic_equiv_iter_loop1 with n.
    - exact IHc.
    - exact H.
Qed. *)

(* ################################################################# *)
(** * Properties Of Execution Paths *)
Local Open Scope Z.
Local Close Scope imp.

Lemma ANum_halt: forall st n a,
  multi_astep st (ANum n) a ->
  a = ANum n.
Proof.
  intros.
  unfold multi_astep in H.
  apply Operators_Properties.clos_rt_rt1n_iff in H.
  inversion H; subst.
  + reflexivity.
  + inversion H0.
Qed.

Lemma never_BFalse_to_BTrue: forall st,
  multi_bstep st BFalse BTrue -> False.
Proof.
  intros.
  unfold multi_bstep in H.
  apply Operators_Properties.clos_rt_rt1n_iff in H.
  inversion H; subst.
  inversion H0.
Qed.

Lemma never_BTrue_to_BFalse: forall st,
  multi_bstep st BTrue BFalse -> False.
Proof.
  intros.
  unfold multi_bstep in H.
  apply Operators_Properties.clos_rt_rt1n_iff in H.
  inversion H; subst.
  inversion H0.
Qed.

Lemma CSkip_halt: forall st st' c s,
  multi_cstep(CNormal s CSkip, st) (CNormal s c, st') ->
  c = CSkip /\ st = st'.
Proof.
Admitted.
(*   intros.
  unfold multi_cstep in H.
  apply Operators_Properties.clos_rt_rt1n_iff in H.
  inversion H; subst.
  + split; reflexivity.
  + inversion H0.
Qed. *)

Lemma APlus_path_spec: forall st a1 a2 n,
  multi_astep st (APlus a1 a2) (ANum n) ->
  exists n1 n2,
  multi_astep st a1 (ANum n1) /\
  multi_astep st a2 (ANum n2) /\
  n = (n1 + n2).
Proof.
  intros.
  remember (APlus a1 a2) as a eqn:H0.
  remember (ANum n) as a' eqn:H1.
  revert a1 a2 n H0 H1; induction_1n H; intros; subst.
  + discriminate H1.
  + inversion H; subst.
    - assert (APlus a1' a2 = APlus a1' a2).
      { reflexivity. }
      assert (ANum n = ANum n).
      { reflexivity. }
      pose proof IH _ _ _ H1 H2.
      clear IH H1 H2.
      destruct H3 as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      pose proof multi_astep_trans_1n H5 H1.
      tauto.
    - assert (APlus a1 a2' = APlus a1 a2').
      { reflexivity. }
      assert (ANum n = ANum n).
      { reflexivity. }
      pose proof IH _ _ _ H1 H2.
      clear IH H1 H2.
      destruct H3 as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      pose proof multi_astep_trans_1n H6 H2.
      tauto.
    - clear IH.
      apply ANum_halt in H0.
      injection H0 as H1.
      exists n1, n2.
      pose proof multi_astep_refl st (ANum n1).
      pose proof multi_astep_refl st (ANum n2).
      tauto.
Qed.

Lemma AMinus_path_spec: forall st a1 a2 n,
  multi_astep st (AMinus a1 a2) (ANum n) ->
  exists n1 n2,
  multi_astep st a1 (ANum n1) /\
  multi_astep st a2 (ANum n2) /\
  n = (n1 - n2).
Proof.
  intros.
  remember (AMinus a1 a2) as a eqn:H0.
  remember (ANum n) as a' eqn:H1.
  revert a1 a2 n H0 H1; induction_1n H; intros; subst.
  + discriminate H1.
  + inversion H; subst.
    - assert (AMinus a1' a2 = AMinus a1' a2).
      { reflexivity. }
      assert (ANum n = ANum n).
      { reflexivity. }
      pose proof IH _ _ _ H1 H2.
      clear IH H1 H2.
      destruct H3 as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      pose proof multi_astep_trans_1n H5 H1.
      tauto.
    - assert (AMinus a1 a2' = AMinus a1 a2').
      { reflexivity. }
      assert (ANum n = ANum n).
      { reflexivity. }
      pose proof IH _ _ _ H1 H2.
      clear IH H1 H2.
      destruct H3 as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      pose proof multi_astep_trans_1n H6 H2.
      tauto.
    - clear IH.
      apply ANum_halt in H0.
      injection H0 as H1.
      exists n1, n2.
      pose proof multi_astep_refl st (ANum n1).
      pose proof multi_astep_refl st (ANum n2).
      tauto.
Qed.

Lemma AMult_path_spec: forall st a1 a2 n,
  multi_astep st (AMult a1 a2) (ANum n) ->
  exists n1 n2,
  multi_astep st a1 (ANum n1) /\
  multi_astep st a2 (ANum n2) /\
  n = (n1 * n2).
Proof.
  intros.
  remember (AMult a1 a2) as a eqn:H0.
  remember (ANum n) as a' eqn:H1.
  revert a1 a2 n H0 H1; induction_1n H; intros; subst.
  + discriminate H1.
  + inversion H; subst.
    - assert (AMult a1' a2 = AMult a1' a2).
      { reflexivity. }
      assert (ANum n = ANum n).
      { reflexivity. }
      pose proof IH _ _ _ H1 H2.
      clear IH H1 H2.
      destruct H3 as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      pose proof multi_astep_trans_1n H5 H1.
      tauto.
    - assert (AMult a1 a2' = AMult a1 a2').
      { reflexivity. }
      assert (ANum n = ANum n).
      { reflexivity. }
      pose proof IH _ _ _ H1 H2.
      clear IH H1 H2.
      destruct H3 as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      pose proof multi_astep_trans_1n H6 H2.
      tauto.
    - clear IH.
      apply ANum_halt in H0.
      injection H0 as H1.
      exists n1, n2.
      pose proof multi_astep_refl st (ANum n1).
      pose proof multi_astep_refl st (ANum n2).
      tauto.
Qed.

Lemma BEq_True_path_spec: forall st a1 a2,
  multi_bstep st (BEq a1 a2) BTrue ->
  exists n1 n2,
  multi_astep st a1 (ANum n1) /\
  multi_astep st a2 (ANum n2) /\
  n1 = n2.
Proof.
  intros.
  remember (BEq a1 a2) as a eqn:H0.
  remember BTrue as a' eqn:H1.
  revert a1 a2 H0 H1; induction_1n H; intros; subst.
  + discriminate H1.
  + inversion H; subst.
    - assert (BEq a1' a2 = BEq a1' a2).
      { reflexivity. }
      assert (BTrue = BTrue).
      { reflexivity. }
      pose proof IH _ _ H1 H2.
      clear IH H1 H2.
      destruct H3 as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      pose proof multi_astep_trans_1n H5 H1.
      tauto.
    - assert (BEq a1 a2' = BEq a1 a2').
      { reflexivity. }
      assert (BTrue = BTrue).
      { reflexivity. }
      pose proof IH _ _ H1 H2.
      clear IH H1 H2.
      destruct H3 as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      pose proof multi_astep_trans_1n H6 H2.
      tauto.
    - clear IH.
      exists n2, n2.
      pose proof multi_astep_refl st (ANum n2).
      tauto.
    - apply never_BFalse_to_BTrue in H0.
      destruct H0.
Qed.

Lemma BEq_False_path_spec: forall st a1 a2,
  multi_bstep st (BEq a1 a2) BFalse ->
  exists n1 n2,
  multi_astep st a1 (ANum n1) /\
  multi_astep st a2 (ANum n2) /\
  n1 <> n2.
Proof.
  intros.
  remember (BEq a1 a2) as a eqn:H0.
  remember BFalse as a' eqn:H1.
  revert a1 a2 H0 H1; induction_1n H; intros; subst.
  + discriminate H1.
  + inversion H; subst.
    - assert (BEq a1' a2 = BEq a1' a2).
      { reflexivity. }
      assert (BFalse = BFalse).
      { reflexivity. }
      pose proof IH _ _ H1 H2.
      clear IH H1 H2.
      destruct H3 as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      unfold multi_astep in H1.
      pose proof multi_astep_trans_1n H5 H1.
      tauto.
    - assert (BEq a1 a2' = BEq a1 a2').
      { reflexivity. }
      assert (BFalse = BFalse).
      { reflexivity. }
      pose proof IH _ _ H1 H2.
      clear IH H1 H2.
      destruct H3 as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      pose proof multi_astep_trans_1n H6 H2.
      tauto.
    - apply never_BTrue_to_BFalse in H0.
      destruct H0.
    - clear IH.
      exists n1, n2.
      pose proof multi_astep_refl st (ANum n1).
      pose proof multi_astep_refl st (ANum n2).
      tauto.
Qed.

Lemma BLe_True_path_spec: forall st a1 a2,
  multi_bstep st (BLe a1 a2) BTrue ->
  exists n1 n2,
  multi_astep st a1 (ANum n1) /\
  multi_astep st a2 (ANum n2) /\
  n1 <= n2.
Proof.
  intros.
  remember (BLe a1 a2) as a eqn:H0.
  remember BTrue as a' eqn:H1.
  revert a1 a2 H0 H1; induction_1n H; intros; subst.
  + discriminate H1.
  + inversion H; subst.
    - assert (BLe a1' a2 = BLe a1' a2).
      { reflexivity. }
      assert (BTrue = BTrue).
      { reflexivity. }
      pose proof IH _ _ H1 H2.
      clear IH H1 H2.
      destruct H3 as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      pose proof multi_astep_trans_1n H5 H1.
      tauto.
    - assert (BLe a1 a2' = BLe a1 a2').
      { reflexivity. }
      assert (BTrue = BTrue).
      { reflexivity. }
      pose proof IH _ _ H1 H2.
      clear IH H1 H2.
      destruct H3 as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      pose proof multi_astep_trans_1n H6 H2.
      tauto.
    - clear IH.
      exists n1, n2.
      pose proof multi_astep_refl st (ANum n1).
      pose proof multi_astep_refl st (ANum n2).
      tauto.
    - apply never_BFalse_to_BTrue in H0.
      destruct H0.
Qed.

Lemma BLe_False_path_spec: forall st a1 a2,
  multi_bstep st (BLe a1 a2) BFalse ->
  exists n1 n2,
  multi_astep st a1 (ANum n1) /\
  multi_astep st a2 (ANum n2) /\
  n1 > n2.
Proof.
  intros.
  remember (BLe a1 a2) as a eqn:H0.
  remember BFalse as a' eqn:H1.
  revert a1 a2 H0 H1; induction_1n H; intros; subst.
  + discriminate H1.
  + inversion H; subst.
    - assert (BLe a1' a2 = BLe a1' a2).
      { reflexivity. }
      assert (BFalse = BFalse).
      { reflexivity. }
      pose proof IH _ _ H1 H2.
      clear IH H1 H2.
      destruct H3 as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      pose proof multi_astep_trans_1n H5 H1.
      tauto.
    - assert (BLe a1 a2' = BLe a1 a2').
      { reflexivity. }
      assert (BFalse = BFalse).
      { reflexivity. }
      pose proof IH _ _ H1 H2.
      clear IH H1 H2.
      destruct H3 as [n1 [n2 [? [? ?]]]].
      exists n1, n2.
      pose proof multi_astep_trans_1n H6 H2.
      tauto.
    - apply never_BTrue_to_BFalse in H0.
      destruct H0.
    - clear IH.
      exists n1, n2.
      pose proof multi_astep_refl st (ANum n1).
      pose proof multi_astep_refl st (ANum n2).
      unfold multi_astep.
      tauto.
Qed.

Lemma BNot_True_path_spec: forall st b,
  multi_bstep st (BNot b) BTrue ->
  multi_bstep st b BFalse.
Proof.
  intros.
  remember (BNot b) as b1 eqn:H0.
  remember BTrue as b2 eqn:H1.
  revert b H0 H1; induction_1n H; intros; subst.
  + discriminate H1.
  + inversion H; subst.
    - assert (BNot b1' = BNot b1').
      { reflexivity. }
      assert (BTrue = BTrue).
      { reflexivity. }
      pose proof IH _ H1 H2.
      pose proof multi_bstep_trans_1n H3 H4.
      exact H5.
    - apply never_BFalse_to_BTrue in H0.
      destruct H0.
    - apply multi_bstep_refl.
Qed.

Lemma BNot_False_path_spec: forall st b,
  multi_bstep st (BNot b) BFalse ->
  multi_bstep st b BTrue.
Proof.
  intros.
  remember (BNot b) as b1 eqn:H0.
  remember BFalse as b2 eqn:H1.
  revert b H0 H1; induction_1n H; intros; subst.
  + discriminate H1.
  + inversion H; subst.
    - assert (BNot b1' = BNot b1').
      { reflexivity. }
      assert (BFalse = BFalse).
      { reflexivity. }
      pose proof IH _ H1 H2.
      pose proof multi_bstep_trans_1n H3 H4.
      exact H5.
    - apply multi_bstep_refl.
    - apply never_BTrue_to_BFalse in H0.
      destruct H0.
Qed.

Lemma BAnd_True_path_spec: forall st b1 b2,
  multi_bstep st (BAnd b1 b2) BTrue ->
  multi_bstep st b1 BTrue /\
  multi_bstep st b2 BTrue.
Proof.
  intros.
  remember (BAnd b1 b2) as b eqn:H0.
  remember BTrue as b' eqn:H1.
  revert b1 b2 H0 H1; induction_1n H; intros; subst.
  + discriminate H1.
  + inversion H; subst.
    - assert (BAnd b1' b2 = BAnd b1' b2).
      { reflexivity. }
      assert (BTrue = BTrue).
      { reflexivity. }
      pose proof IH _ _ H1 H2.
      destruct H3.
      pose proof multi_bstep_trans_1n H5 H3.
      tauto.
    - split.
      * apply multi_bstep_refl.
      * exact H0.
    - apply never_BFalse_to_BTrue in H0.
      destruct H0.
Qed.

Lemma BAnd_False_path_spec: forall st b1 b2,
  multi_bstep st (BAnd b1 b2) BFalse ->
  multi_bstep st b1 BFalse \/
  multi_bstep st b2 BFalse.
Proof.
  intros.
  remember (BAnd b1 b2) as b eqn:H0.
  remember BFalse as b' eqn:H1.
  revert b1 b2 H0 H1; induction_1n H; intros; subst.
  + discriminate H1.
  + inversion H; subst.
    - assert (BAnd b1' b2 = BAnd b1' b2).
      { reflexivity. }
      assert (BFalse = BFalse).
      { reflexivity. }
      pose proof IH _ _ H1 H2.
      destruct H3.
      * left.
        pose proof multi_bstep_trans_1n H5 H3.
        tauto.
      * right.
        exact H3.
    - right.
      exact H0.
    - left.
      apply multi_bstep_refl.
Qed.

Lemma CAss_path_spec: forall X a st1 st2 s,
  multi_cstep (CNormal s (CAss X a), st1) (CNormal s CSkip, st2) ->
  exists n,
  multi_astep st1 a (ANum n) /\
  st2 X = n /\
  (forall Y : var, X <> Y -> st1 Y = st2 Y).
Proof.
Admitted.
(*   intros.
  remember (CAss X a) as c eqn:H0.
  remember CSkip as c' eqn:H1.
  revert a H0 H1; induction_1n H; intros; subst.
  + inversion H1.
  + inversion H; subst.
    - assert (CAss X a' = CAss X a'). { reflexivity. }
      assert (CSkip = CSkip). { reflexivity. }
      pose proof IH _ H1 H3.
      clear IH H1 H3.
      destruct H4 as [n [? ?]].
      exists n.
      pose proof multi_astep_trans_1n H2 H1.
      tauto.
    - clear IH.
      apply CSkip_halt in H0.
      destruct H0.
      subst st0.
      exists (st2 X).
      pose proof multi_astep_refl st1 (ANum (st2 X)).
      tauto.
Qed. *)

Lemma CSeq_path_spec: forall c1 st1 c2 st3 s,
  multi_cstep (CNormal s (CSeq c1 c2), st1) (CNormal s CSkip, st3) ->
  exists st2,
  multi_cstep (CNormal s c1, st1) (CNormal s CSkip, st2) /\
  multi_cstep (CNormal s c2, st2) (CNormal s CSkip, st3).
Proof.
Admitted.
(*   intros.
  remember (CSeq c1 c2) as c eqn:H0.
  remember CSkip as c' eqn:H1.
  revert c1 c2 H0 H1; induction_1n H; intros; subst.
  + inversion H1.
  + inversion H; subst.
    - assert (CSeq c1' c2 = CSeq c1' c2). { reflexivity. }
      assert (CSkip = CSkip). { reflexivity. }
      pose proof IH _ _ H1 H3.
      clear IH H1 H3.
      destruct H4 as [st2 [? ?]].
      exists st2.
      pose proof multi_cstep_trans_1n H2 H1.
      tauto.
    - exists st0.
      pose proof multi_cstep_refl st0 CSkip.
      tauto.
Qed. *)

Lemma CIf_path_spec: forall b c1 c2 st1 st2 s,
  multi_cstep (CNormal s (CIf b c1 c2), st1) (CNormal s CSkip, st2) ->
  multi_bstep st1 b BTrue /\
  multi_cstep (CNormal s c1, st1) (CNormal s CSkip, st2) \/
  multi_bstep st1 b BFalse /\
  multi_cstep (CNormal s c2, st1) (CNormal s CSkip, st2).
Proof.
Admitted.
(*   intros.
  remember (CIf b c1 c2) as c eqn:H0.
  remember CSkip as c' eqn:H1.
  revert b c1 c2 H0 H1; induction_1n H; intros; subst.
  + inversion H1.
  + inversion H; subst.
    - assert (CIf b' c1 c2 = CIf b' c1 c2). { reflexivity. }
      assert (CSkip = CSkip). { reflexivity. }
      pose proof IH _ _ _ H1 H3.
      clear IH H1 H3.
      destruct H4 as [[? ?] | [? ?]].
      * pose proof multi_bstep_trans_1n H2 H1.
        tauto.
      * pose proof multi_bstep_trans_1n H2 H1.
        tauto.
    - pose proof multi_bstep_refl st0 BTrue.
      tauto.
    - pose proof multi_bstep_refl st0 BFalse.
      tauto.
Qed. *)
Fixpoint CWhile_path s b c1 st1 st2 (n: nat): Prop:=
  match n with
  | O => multi_bstep st1 b BFalse /\ st1 = st2
  | S n' => exists st1',
            multi_bstep st1 b BTrue /\
            multi_cstep (CNormal s c1, st1) (CNormal s CSkip, st1') /\
            CWhile_path s b c1 st1' st2 n'
  end.

Definition CWhile_path' s b' b c1 st1 st2 (n: nat): Prop:=
  match n with
  | O => multi_bstep st1 b' BFalse /\ st1 = st2
  | S n' => exists st1',
            multi_bstep st1 b' BTrue /\
            multi_cstep (CNormal s c1, st1) (CNormal s CSkip, st1') /\
            CWhile_path s b c1 st1' st2 n'
  end.

Definition CWhile_path'' s c1' b c1 st1 st2 (n: nat): Prop:=
  exists st1',
    multi_cstep (CNormal s c1', st1) (CNormal s CSkip, st1') /\
    CWhile_path s b c1 st1' st2 n.

Lemma CWhile_path_spec_aux: forall s st1 st2 c c',
  multi_cstep (c, st1) (c', st2) ->
  (forall b c1,
     c = CNormal s (CWhile b c1) ->
     c' = CNormal  s CSkip%imp ->
     exists n, CWhile_path s b c1 st1 st2 n) /\
  (forall b' b c1,
     c = CNormal s (CIf b' (CSeq c1 (CWhile b c1)) CSkip) ->
     c' = CNormal  s CSkip%imp ->
     exists n, CWhile_path' s b' b c1 st1 st2 n) /\
  (forall c1' b c1,
     c = CNormal s (CSeq c1' (CWhile b c1)) ->
     c' = CNormal  s CSkip%imp ->
     exists n, CWhile_path'' s c1' b c1 st1 st2 n).
Proof.
Admitted.
(*   intros.
  induction_1n H; intros.
  + split.
    { intros; subst. inversion H0. }
    split.
    { intros; subst. inversion H0. }
    { intros; subst. inversion H0. }
  + split.
    {
      intros; subst.
      destruct IH as [? [IH ?]].
      clear H1 H2.
      inversion H; subst.
      assert (CIf b (CSeq c1 (CWhile b c1)) CSkip =
              CIf b (CSeq c1 (CWhile b c1)) CSkip).
      { reflexivity. }
      assert (CSkip = CSkip). { reflexivity. }
      pose proof IH _ _ _ H1 H2.
      clear IH H1 H2.
      destruct H3 as [n ?].
      exists n.
      destruct n; exact H1.
    }
    split.
    {
      intros; subst.
      inversion H; subst.
      - destruct IH as [? [IH ?]].
        clear H1 H3.
        assert (CIf b'0 (CSeq c1 (CWhile b c1)) CSkip =
                CIf b'0 (CSeq c1 (CWhile b c1)) CSkip).
        { reflexivity. }
        assert (CSkip = CSkip). { reflexivity. }
        pose proof IH _ _ _ H1 H3.
        clear IH H1 H3.
        destruct H4 as [n ?].
        exists n.
        destruct n; simpl in H1; simpl.
        * destruct H1.
          pose proof multi_bstep_trans_1n H2 H1.
          tauto.
        * destruct H1 as [st1' [? [? ?]]].
          exists st1'.
          pose proof multi_bstep_trans_1n H2 H1.
          tauto.
      - destruct IH as [? [? IH]].
        clear H1 H2.
        assert (CSeq c1 (CWhile b c1) = CSeq c1 (CWhile b c1)). { reflexivity. }
        assert (CSkip = CSkip). { reflexivity. }
        pose proof IH _ _ _ H1 H2.
        destruct H3 as [n ?].
        exists (S n).
        unfold CWhile_path'' in H3.
        simpl.
        destruct H3 as [st1' [? ?]].
        exists st1'.
        pose proof multi_bstep_refl st0 BTrue.
        tauto.
      - exists O.
        simpl.
        pose proof multi_bstep_refl st0 BFalse.
        apply CSkip_halt in H0.
        tauto.
    }
    {
      intros; subst.
      inversion H; subst.
      - destruct IH as [? [? IH]].
        clear H1 H3.
        assert (CSeq c1'0 (CWhile b c1) = CSeq c1'0 (CWhile b c1)). { reflexivity. }
        assert (CSkip = CSkip). { reflexivity. }
        pose proof IH _ _ _ H1 H3.
        clear IH H1 H3.
        destruct H4 as [n ?].
        exists n.
        unfold CWhile_path'' in H1.
        unfold CWhile_path''.
        destruct H1 as [st1' [? ?]].
        exists st1'.
        pose proof multi_cstep_trans_1n H2 H1.
        tauto.
      - destruct IH as [IH [? ?]].
        clear H1 H2.
        assert (CWhile b c1 = CWhile b c1). { reflexivity. }
        assert (CSkip = CSkip). { reflexivity. }
        pose proof IH _ _ H1 H2.
        clear IH H1 H2.
        destruct H3 as [n ?].
        exists n.
        unfold CWhile_path''.
        exists st0.
        pose proof multi_cstep_refl st0 CSkip.
        tauto.
    }
Qed. *)

Lemma CWhile_path_spec: forall s b c1 st1 st2,
  multi_cstep (CNormal s (CWhile b c1), st1) (CNormal  s CSkip, st2) ->
  exists n, CWhile_path s b c1 st1 st2 n.
Proof.
Admitted.
(*   intros.
  remember (CWhile b c1) as c eqn:H0.
  remember CSkip as c' eqn:H1.
  revert b c1 H0 H1.
  pose proof CWhile_path_spec_aux st1 st2 c c'.
  tauto.
Qed. *)

(* ################################################################# *)
(** * From Multi-step Relations To Denotations *)

Theorem semantic_equiv_aexp2: forall st a n,
  multi_astep st a (ANum n) -> aeval a st = n.
Proof.
  intros.
  revert n H; induction a; intros; simpl.
  + apply ANum_halt in H.
    injection H as ?H.
    rewrite H.
    reflexivity.
  + unfold multi_astep in H.
    apply Operators_Properties.clos_rt_rt1n_iff in H.
    inversion H; subst.
    inversion H0; subst.
    inversion H1; subst.
    - reflexivity.
    - inversion H2.
  + apply APlus_path_spec in H.
    destruct H as [n1 [n2 [? [? ?]]]].
    apply IHa1 in H.
    apply IHa2 in H0.
    omega.
  + apply AMinus_path_spec in H.
    destruct H as [n1 [n2 [? [? ?]]]].
    apply IHa1 in H.
    apply IHa2 in H0.
    omega.
  + apply AMult_path_spec in H.
    destruct H as [n1 [n2 [? [? ?]]]].
    apply IHa1 in H.
    apply IHa2 in H0.
    rewrite H, H0, H1.
    reflexivity.
Qed.

Theorem semantic_equiv_bexp2: forall st b,
  (multi_bstep st b BTrue -> beval b st) /\
  (multi_bstep st b BFalse -> ~ beval b st).
Proof.
  intros.
  induction b; simpl.
  + split; intros.
    - exact I.
    - apply never_BTrue_to_BFalse in H.
      destruct H.
  + split; intros.
    - apply never_BFalse_to_BTrue in H.
      destruct H.
    - tauto.
  + split; intros.
    - apply BEq_True_path_spec in H.
      destruct H as [n1 [n2 [? [? ?]]]].
      apply semantic_equiv_aexp2 in H.
      apply semantic_equiv_aexp2 in H0.
      omega.
    - apply BEq_False_path_spec in H.
      destruct H as [n1 [n2 [? [? ?]]]].
      apply semantic_equiv_aexp2 in H.
      apply semantic_equiv_aexp2 in H0.
      omega.
  + split; intros.
    - apply BLe_True_path_spec in H.
      destruct H as [n1 [n2 [? [? ?]]]].
      apply semantic_equiv_aexp2 in H.
      apply semantic_equiv_aexp2 in H0.
      omega.
    - apply BLe_False_path_spec in H.
      destruct H as [n1 [n2 [? [? ?]]]].
      apply semantic_equiv_aexp2 in H.
      apply semantic_equiv_aexp2 in H0.
      omega.
  + destruct IHb as [IHb1 IHb2].
    split; intros.
    - apply BNot_True_path_spec in H.
      tauto.
    - apply BNot_False_path_spec in H.
      tauto.
  + split; intros.
    - apply BAnd_True_path_spec in H.
      tauto.
    - apply BAnd_False_path_spec in H.
      tauto.
Qed.

Theorem semantic_equiv_com2: forall s c st1 EK st2,
  multi_cstep (CNormal  s c, st1) (CNormal  s CSkip, st2) -> ceval c st1 EK st2.
Proof.
Admitted.
(*   intros.
  revert st1 st2 H; induction c; intros.
  + apply CSkip_halt in H.
    destruct H.
    rewrite H0.
    simpl.
    unfold Relation_Operators.id.
    reflexivity.
  + apply CAss_path_spec in H.
    destruct H as [n [? [? ?]]].
    apply semantic_equiv_aexp2 in H.
    simpl.
    rewrite H.
    tauto.
  + apply CSeq_path_spec in H.
    destruct H as [st1' [? ?]].
    apply IHc1 in H.
    apply IHc2 in H0.
    simpl.
    unfold Relation_Operators.concat.
    exists st1'.
    tauto.
  + apply CIf_path_spec in H.
    simpl.
    unfold if_sem.
    unfold Relation_Operators.union,
           Relation_Operators.intersection,
           Relation_Operators.filter1.
    specialize (IHc1 st1 st2).
    specialize (IHc2 st1 st2).
    pose proof semantic_equiv_bexp2 st1 b.
    tauto.
  + apply CWhile_path_spec in H.
    simpl.
    unfold loop_sem.
    unfold Relation_Operators.omega_union.
    destruct H as [n ?].
    exists n.
    revert st1 H; induction n; simpl; intros.
    - pose proof semantic_equiv_bexp2 st1 b.
      destruct H.
      subst st2.
      unfold Relation_Operators.intersection,
             Relation_Operators.id,
             Relation_Operators.filter1.
      tauto.
    - destruct H as [st1' [? [? ?]]].
      specialize (IHn st1').
      unfold Relation_Operators.intersection,
             Relation_Operators.concat,
             Relation_Operators.filter1.
      apply semantic_equiv_bexp2 in H.
      split.
      * exists st1'.
        specialize (IHc st1 st1').
        tauto.
      * exact H.
Qed.
 *)
(* ################################################################# *)
(** * Final Theorem *)

Theorem semantic_equiv: forall s c st1 EK st2,
  ceval c st1 EK st2 <-> multi_cstep (CNormal  s c, st1) (CNormal  s CSkip, st2).
Proof.
  intros.
  split.
  + apply semantic_equiv_com1.
  + apply semantic_equiv_com2.
Qed.

(* ################################################################# *)
(** * Alternative Proofs: From Multi-step Relations To Denotations *)

Lemma aeval_preserve: forall st a1 a2,
  astep st a1 a2 ->
  aeval a1 st  = aeval a2 st.
Proof.
  intros.
  induction H.
  + simpl.
    reflexivity.
  + simpl.
    rewrite IHastep.
    reflexivity.
  + simpl.
    rewrite IHastep.
    reflexivity.
  + simpl.
    reflexivity.
  + simpl.
    rewrite IHastep.
    reflexivity.
  + simpl.
    rewrite IHastep.
    reflexivity.
  + simpl.
    reflexivity.
  + simpl.
    rewrite IHastep.
    reflexivity.
  + simpl.
    rewrite IHastep.
    reflexivity.
  + simpl.
    reflexivity.
Qed.

Theorem semantic_equiv_aexp3: forall st a n,
  multi_astep st a (ANum n) -> aeval a st = n.
Proof.
  intros.
  remember (ANum n) as a' eqn:H0.
  revert n H0; induction_1n H; simpl; intros.
  + rewrite H0.
    simpl.
    reflexivity.
  + pose proof aeval_preserve _ _ _ H.
    rewrite H2.
    apply IH.
    exact H1.
Qed.

Lemma beval_preserve: forall st b1 b2,
  bstep st b1 b2 ->
  (beval b1 st  <-> beval b2 st).
Proof.
  intros.
  induction H.
  + apply aeval_preserve in H.
    simpl.
    rewrite H.
    tauto.
  + apply aeval_preserve in H0.
    simpl.
    rewrite H0.
    tauto.
  + simpl.
    tauto.
  + simpl.
    tauto.
  + apply aeval_preserve in H.
    simpl.
    rewrite H.
    tauto.
  + apply aeval_preserve in H0.
    simpl.
    rewrite H0.
    tauto.
  + simpl.
    tauto.
  + simpl.
    omega.
  + simpl.
    tauto.
  + simpl.
    tauto.
  + simpl.
    tauto.
  + simpl.
    tauto.
  + simpl.
    tauto.
  + simpl.
    tauto.
Qed.

Theorem semantic_equiv_bexp3: forall st b TF,
  multi_bstep st b TF ->
  (TF = BTrue -> beval b st) /\
  (TF = BFalse -> ~ beval b st).
Proof.
  intros.
  induction_1n H; simpl; intros.
  + split; intros; subst; simpl; tauto.
  + pose proof beval_preserve _ _ _ H.
    tauto.
Qed.

Lemma ceval_preserve: forall s c1 c2 st1 EK st2,
  cstep (CNormal  s c1, st1) (CNormal s c2, st2) ->
  forall st3, ceval c2 st2 EK st3 -> ceval c1 st1 EK st3.
Proof.
Admitted.
(** We could prove a stronger conclusion:

    forall st3, ceval c1 st1 st3 <-> ceval c2 st2 st3.

But this single direction version is enough to use. *)
(*   intros.
  revert H0.
  remember (c1, st1) as cst1 eqn:H0.
  remember (c2, st2) as cst2 eqn:H1.
  revert c1 c2 st1 st2 st3 H0 H1; induction H; simpl; intros.
  + apply aeval_preserve in H.
    injection H0 as ? ?.
    injection H1 as ? ?.
    subst.
    simpl.
    simpl in H2.
    rewrite H.
    tauto.
  + injection H1 as ? ?.
    injection H2 as ? ?.
    subst.
    simpl.
    simpl in H3.
    unfold Relation_Operators.id in H3.
    subst.
    tauto.
  + injection H0 as ? ?.
    injection H1 as ? ?.
    subst.
    simpl in H2.
    simpl.
    unfold Relation_Operators.concat in H2.
    unfold Relation_Operators.concat.
    destruct H2 as [st2' [? ?]].
    exists st2'.
    assert ((c1, st1) = (c1, st1)). { reflexivity. }
    assert ((c1', st2) = (c1', st2)). { reflexivity. }
    specialize (IHcstep _ _ _ _ st2' H2 H3).
    tauto.
  + injection H0 as ? ?.
    injection H1 as ? ?.
    subst.
    simpl.
    unfold Relation_Operators.concat, Relation_Operators.id.
    exists st2.
    split.
    - reflexivity.
    - exact H2.
  + injection H0 as ? ?.
    injection H1 as ? ?.
    subst.
    simpl in H2.
    simpl.
    unfold if_sem in H2.
    unfold if_sem.
    unfold Relation_Operators.union,
           Relation_Operators.intersection,
           Relation_Operators.filter1 in H2.
    unfold Relation_Operators.union,
           Relation_Operators.intersection,
           Relation_Operators.filter1.
    apply beval_preserve in H.
    simpl in H2.
    simpl.
    tauto.
  + injection H0 as ? ?.
    injection H1 as ? ?.
    subst.
    simpl in H2.
    simpl.
    unfold if_sem.
    unfold Relation_Operators.union,
           Relation_Operators.intersection,
           Relation_Operators.filter1.
    simpl.
    tauto.
  + injection H0 as ? ?.
    injection H1 as ? ?.
    subst.
    simpl in H2.
    simpl.
    unfold if_sem.
    unfold Relation_Operators.union,
           Relation_Operators.intersection,
           Relation_Operators.filter1.
    simpl.
    tauto.
  + injection H0 as ? ?.
    injection H1 as ? ?.
    subst.
    simpl in H2.
    simpl.
    SearchAbout loop_sem.
    pose proof loop_recur b (ceval c) st2 st3.
    unfold com_dequiv,
           if_sem,
           Relation_Operators.union,
           Relation_Operators.intersection,
           Relation_Operators.filter1,
           Relation_Operators.concat in H, H2.
    apply H; clear H.
    exact H2.
Qed.
 *)
Theorem semantic_equiv_com3: forall s c st1 EK st2,
  multi_cstep (CNormal  s c, st1) (CNormal  s CSkip, st2) -> ceval c st1 EK st2.
Proof.
Admitted.
(*   intros.
  remember (CSkip) as c' eqn:H0.
  revert H0; induction_1n H; simpl; intros; subst.
  + simpl.
    unfold Relation_Operators.id.
    reflexivity.
  + pose proof ceval_preserve _ _ _ _ H st2.
    tauto.
Qed. *)