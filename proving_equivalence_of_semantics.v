Require Import PL.definition_of_two_semantics.
Require Import PL.definition_of_abc.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Relation_Definitions.

Arguments clos_refl_trans {A} _ _ _.
Arguments clos_refl_trans_1n {A} _ _ _.
Arguments clos_refl_trans_n1 {A} _ _ _.

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
   intros.
  remember (CNormal s c1, st1) as x; remember (CNormal s c1', st1') as y.
  revert s c1 c2 c1' st1 st1' Heqx Heqy.
   induction H;intros.
  + rewrite Heqx in H. rewrite Heqy in H. 
      pose proof CS_SeqStep _ _ _ _ _ c2 H. 
      eapply multi_cstep_step. exact H0.
  + rewrite Heqy in Heqx. 
      inversion Heqx.
      eapply multi_cstep_refl.

  + eapply IHclos_refl_trans2;subst.

      - admit.
      - reflexivity.
Admitted.
(*   refine multi_cstep_ind_n1 multi_cstep _ _.
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

Theorem multi_congr_CWhileLoop: forall st s b b' c1 c2,
  multi_bstep st b b' ->
  multi_cstep
     (CLoopCond (Whileloop b c1 c2 :: s)%list b, st)
        (CLoopCond (Whileloop b c1 c2 :: s)%list b', st).
Proof.
  intros.
  induction_n1 H.
  + apply multi_cstep_refl.
  + eapply multi_cstep_trans_n1.
    - exact IH.
    - apply CS_WhileStep.
      exact H0.
Qed.

Theorem multi_congr_CDoWhileLoop: forall st s b b' c1 c2,
  multi_bstep st b b' ->
  multi_cstep
     (CLoopCond (Dowhileloop c1 b c2 :: s)%list b, st)
        (CLoopCond (Dowhileloop c1 b c2 :: s)%list b', st).
Proof.
  intros.
  induction_n1 H.
  + apply multi_cstep_refl.
  + eapply multi_cstep_trans_n1.
    - exact IH.
    - apply CS_DoWhileStep2.
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

Lemma semantic_equiv_iter_loop1: forall st1 st2 n b c s,
  (forall st1 st2, ceval c st1 EK_Normal st2 -> multi_cstep (CNormal s c, st1) (CNormal s CSkip, st2)) ->
  iter_loop_body1 b (ceval c) n st1 st2 ->
  multi_cstep (CLoopCond (cons (Whileloop b c CSkip) s) b, st1) (CNormal s CSkip, st2).
Proof.
  intros.
  revert st1 st2 H0; induction n; intros.
  + simpl in H0.
    firstorder;subst st2.
    pose proof CS_While.
    pose proof semantic_equiv_bexp1 st1 b.
    firstorder.
    pose proof multi_congr_CWhileLoop st1 s b BFalse c Skip H3.
    pose proof CS_WhileFalse st1 s b c Skip.
    pose proof multi_cstep_trans_n1 H4 H5.
    exact H6.
  + simpl in H0.
    destruct H0.
    destruct H0.
    - destruct H0 as [st3 [? ?]].
      specialize (IHn st3 st2 H2).
      pose proof CS_While.
      
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


Lemma semantic_equiv_iter_loop2: forall st1 st2  c s  b n,
iter_loop_body2 b (ceval c) n st1 st2 ->
(forall st3 st4 : state,
      ceval c st3 EK_Normal st4 -> multi_cstep (CNormal s c, st3) (CNormal s Skip, st4)) ->
multi_cstep (CNormal (Dowhileloop c b Skip :: s)%list c, st1) (CNormal s Skip, st2).
Proof.
  intros.
  revert st1 st2 H; induction n; intros.
  + simpl in H.
    firstorder; subst.
    - pose proof CS_While.
      pose proof semantic_equiv_bexp1 st2 b.
      firstorder.
      pose proof multi_congr_CDoWhileLoop st2 s b BFalse c Skip H4.
      pose proof CS_DoWhileFalse st2 s b c Skip.
      pose proof multi_cstep_trans_n1 H5 H6.
Admitted.


(* *)
Lemma semantic_equiv_iter_loop3: forall st1 st2 st3 c1 c2 c3 s  b n,(* 前提不是都要用*)
ceval c1 st1 EK_Normal st3 ->
  iter_loop_body3 b (ceval c3) (ceval c2) n st1 st2 ->
(forall st4 st5 : state,
       ceval c1 st4 EK_Normal st5 -> multi_cstep (CNormal s c1, st4) (CNormal s Skip, st5)) ->
(forall st4 st5 : state,
       ceval c2 st4 EK_Normal st5 -> multi_cstep (CNormal s c2, st4) (CNormal s Skip, st5)) ->
(forall st4 st5 : state,
       ceval c3 st4 EK_Normal st5 -> multi_cstep (CNormal s c3, st4) (CNormal s Skip, st5))->
multi_cstep  (CInit (Forloop c1 b c3 c2 Skip :: s)%list c1, st1)  (CNormal s Skip, st2).
Proof.
Admitted.


Theorem semantic_equiv_com1_Normal: forall st1 st2 c s,
ceval c st1 EK_Normal st2 ->  multi_cstep (CNormal s c, st1) (CNormal s CSkip, st2).
Proof.
  intros.
  revert st1 st2 H; induction c; intros; simpl in H.
  + unfold skip_sem in H; destruct H.
    rewrite H.
    eapply rt_refl.
  + unfold asgn_sem in H; destruct H.
    assert (aeval a st1 = aeval a st1). {reflexivity. }
    pose proof semantic_equiv_aexp1 _ _ _ H1.
    pose proof (multi_congr_CAss _ s X _ _ ) H2.
    eapply multi_cstep_trans_n1.
    exact H3.
    destruct H0.
    rewrite <- H.
    apply CS_Ass; [reflexivity|exact H4].
  + destruct H.
    unfold seq_sem in H; destruct H as [ st3 [] ].
    - pose proof IHc1 _ _ H.
      pose proof (multi_congr_CSeq _ _ _ _ _ c2) H1 .
      pose proof CS_Seq st3 s c2.
      pose proof multi_cstep_trans_n1 H2 H3. 
      clear H3 H2 H1 H IHc1.
      eapply multi_cstep_trans.
      exact H4. 
      eapply IHc2.
      firstorder.
    - destruct H.
      pose proof IHc1 _ _ H.
      pose proof (multi_congr_CSeq _ _ _ _ _ c2) H1 .
      pose proof CS_Seq st2 s c2.
      pose proof multi_cstep_trans_n1 H2 H3. 
      clear H3 H2 H1 H IHc1.
      eapply multi_cstep_trans.
      exact H4.
      firstorder.
  + unfold if_sem in H.
    pose proof semantic_equiv_bexp1 st1 b.
    destruct H0.
    destruct H as [[? ?] | [? ?]].
    - specialize (H0 H2).
      pose proof IHc1 _ _ H.
      clear H H1 H2 IHc1 IHc2.
      pose proof multi_congr_CIf st1 s _ _ c1 c2 H0.
      pose proof CS_IfTrue st1 s c1 c2.
      pose proof multi_cstep_trans_n1 H H1.
      pose proof multi_cstep_trans H2 H3.
      exact H4.
    - specialize (H1 H2).
      pose proof IHc2 _  _ H.
      clear H H0 H2 IHc1 IHc2.
      pose proof (multi_congr_CIf st1 s  _ _ c1 c2) H1.
      pose proof CS_IfFalse st1 s c1 c2.
      pose proof multi_cstep_trans_n1 H H0.
      pose proof multi_cstep_trans H2 H3.
      exact H4.
  + destruct H as [n [? ?]].
    pose proof (semantic_equiv_iter_loop1 _ _ _ _ _ _) IHc H.
    pose proof (CS_While st1 s  (While b Do c EndWhile) b c CSkip) (SWWL_While b c).
    eapply multi_cstep_trans_1n.
    exact H2.
    exact H1.
  + destruct H. discriminate H0.
  + destruct H. discriminate H0.
  + destruct H.
    destruct H as [? [[n ?] ?]].
    pose proof semantic_equiv_iter_loop3 st1 st2 x c1 c2 c3 s b n H H0 IHc1 IHc2 IHc3.
    pose proof (CS_For st1 s (For( c1; b; c2) c3 EndFor) c1 b _ _ _) (SWFL_For c1 b c2 c3).
    eapply multi_cstep_trans_1n.
    exact H3.
    exact H2.
  + destruct H as [? [] ].
    pose proof (CS_DoWhile st1 s (Do c While b EndWhile) b _ CSkip) (SWDL_Dowhile _ b).
    eapply multi_cstep_trans_1n.
    exact H1.
    pose proof (semantic_equiv_iter_loop2 _ _ _ _ _ _) H IHc.
    exact H2.
Qed.


Theorem semantic_equiv_com1_Break: forall st1 st2 c s,
ceval c st1 EK_Break st2  ->  exists c', multi_cstep (CNormal s c, st1) (CNormal s c', st2) /\ start_with_break c'.
Proof.
  intros.
  revert st1 st2 H; induction c; intros; simpl in H.
  + destruct H.
    discriminate H0.
  + destruct H as [? [? ?]].
    discriminate H0.
  + destruct H.
    - destruct H as [st3 [? ?]].
      pose proof (IHc2 _ _) H0.
      destruct H1 as [c' [? ?]].
      exists c'.
      split.
      * pose proof (semantic_equiv_com1_Normal _  _ _ s) H.
        pose proof multi_congr_CSeq.
        pose proof (multi_congr_CSeq _ s _ _ _ c2) H3.
        pose proof multi_cstep_trans_n1 H5 (CS_Seq st3 s c2).
        pose proof multi_cstep_trans H6 H1.
        exact H7.
      * exact H2.
    - destruct H.
      pose proof (IHc1 _ _) H.
      destruct H1 as [c' [? ?]].
      exists (c';;c2)%imp. split.
      * eapply multi_congr_CSeq.
        exact H1.
      * eapply SWB_Seq.
        exact H2.
  + pose proof semantic_equiv_bexp1 st1 b. destruct H0.
    destruct H.
    - destruct H. pose proof H0 H2;clear H0 H1 H2.
      pose proof (IHc1 _ _) H; clear IHc1 H.
      destruct H0 as [c' [? ?]].
      exists c'.
      split.
      * pose proof (multi_congr_CIf _ s _ _ c1 c2) H3.
        pose proof (CS_IfTrue st1 s c1 c2).
        pose proof multi_cstep_trans_n1 H1 H2.
        pose proof multi_cstep_trans H4 H.
        exact H5.
      * exact H0.
    - destruct H. pose proof H1 H2;clear H0 H1 H2.
      pose proof (IHc2 _ _) H; clear IHc1 H.
      destruct H0 as [c' [? ?]].
      exists c'.
      split.
      * pose proof (multi_congr_CIf _ s _ _ c1 c2) H3.
        pose proof (CS_IfFalse st1 s c1 c2).
        pose proof multi_cstep_trans_n1 H1 H2.
        pose proof multi_cstep_trans H4 H.
        exact H5.
      * exact H0.
  + destruct H as [? [? ?]].
    discriminate H0.
  + destruct H.
    rewrite H.
    exists (CBreak).
    split.
    eapply multi_cstep_refl.
    apply SWB_Break.
  + destruct H. discriminate H0.
  + destruct H as [? [? [? ?]]].
    discriminate H1.
  + destruct H as [?[]].
    discriminate H0.
Qed.


Theorem semantic_equiv_com1_Cont: forall st1 st2 c s,
ceval c st1 EK_Cont st2 -> exists c', multi_cstep (CNormal s c, st1) (CNormal s c', st2) /\ start_with_cont c'.
Proof.
  intros.
  revert st1 st2 H; induction c; intros; simpl in H.
  + destruct H.
    discriminate H0.
  + destruct H as [? [? ?]].
    discriminate H0.
  + destruct H.
    - destruct H as [st3 [? ?]].
      pose proof (IHc2 _ _) H0.
      destruct H1 as [c' [? ?]].
      exists c'.
      split.
      * pose proof (semantic_equiv_com1_Normal _  _ _ s) H.
        pose proof multi_congr_CSeq.
        pose proof (multi_congr_CSeq _ s _ _ _ c2) H3.
        pose proof multi_cstep_trans_n1 H5 (CS_Seq st3 s c2).
        pose proof multi_cstep_trans H6 H1.
        exact H7.
      * exact H2.
    - destruct H.
      pose proof (IHc1 _ _) H.
      destruct H1 as [c' [? ?]].
      exists (c';;c2)%imp. split.
      * eapply multi_congr_CSeq.
        exact H1.
      * eapply SWC_Seq.
        exact H2.
  + pose proof semantic_equiv_bexp1 st1 b. destruct H0.
    destruct H.
    - destruct H. pose proof H0 H2;clear H0 H1 H2.
      pose proof (IHc1 _ _) H; clear IHc1 H.
      destruct H0 as [c' [? ?]].
      exists c'.
      split.
      * pose proof (multi_congr_CIf _ s _ _ c1 c2) H3.
        pose proof (CS_IfTrue st1 s c1 c2).
        pose proof multi_cstep_trans_n1 H1 H2.
        pose proof multi_cstep_trans H4 H.
        exact H5.
      * exact H0.
    - destruct H. pose proof H1 H2;clear H0 H1 H2.
      pose proof (IHc2 _ _) H; clear IHc1 H.
      destruct H0 as [c' [? ?]].
      exists c'.
      split.
      * pose proof (multi_congr_CIf _ s _ _ c1 c2) H3.
        pose proof (CS_IfFalse st1 s c1 c2).
        pose proof multi_cstep_trans_n1 H1 H2.
        pose proof multi_cstep_trans H4 H.
        exact H5.
      * exact H0.
  + destruct H as [? [? ?]].
    discriminate H0.
  + destruct H.
    discriminate H0.
  + destruct H.
    rewrite H.
    exists (CCont).
    split.
    eapply multi_cstep_refl.
    apply SWC_Break.
  + destruct H as [? [? [? ?]]].
    discriminate H1.
  + destruct H as [? []].
    discriminate H0.
Qed.

Theorem semantic_equiv_com1: forall st1 st2 c s,
(ceval c st1 EK_Normal st2 ->  multi_cstep (CNormal s c, st1) (CNormal s CSkip, st2))  /\
(ceval c st1 EK_Break st2  ->  exists c', multi_cstep (CNormal s c, st1) (CNormal s c', st2) /\ start_with_break c') /\
(ceval c st1 EK_Cont st2 -> exists c', multi_cstep (CNormal s c, st1) (CNormal s c', st2) /\ start_with_cont c').
Proof.
  intros.
  split; [eapply semantic_equiv_com1_Normal|].
  split; [eapply semantic_equiv_com1_Break|eapply semantic_equiv_com1_Cont].
Qed.

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
  intros.
  remember (CNormal s Skip, st) as C'.
  remember (CNormal s c, st') as C''.
  revert HeqC' HeqC'' .
  revert c s st st'.
  induction H; intros; split; subst.
  + inversion H;
    subst.
    - inversion H1.
    - admit.
    - admit.
    - inversion H1.
    - inversion H1.
    - inversion H1.
  + inversion H; subst.
    - reflexivity.
    - admit.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
  + inversion HeqC''.
    reflexivity.
  + inversion HeqC''.
    reflexivity.
  + admit.
  + admit.

Admitted.


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
  intros.
  remember (CWhile b c1) as c eqn:H0.
  remember CSkip as c' eqn:H1.
  revert b c1 H0 H1.
  pose proof CWhile_path_spec_aux s st1 st2 (CNormal s c) (CNormal s c') H.
  destruct H0 as [? [? ?]].
  intros.
  specialize H0 with b c1.
  destruct H0.
  rewrite H3.
  reflexivity.
  rewrite H4.
  reflexivity.
  exists x.
  exact H0.
Qed.

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

Theorem semantic_equiv_com2: forall s c st1 st2,
  (multi_cstep (CNormal  s c, st1) (CNormal  s CSkip, st2) -> ceval c st1 EK_Normal st2) /\
  ((exists c', multi_cstep (CNormal  s c, st1) (CNormal  s c', st2) /\ start_with_break c') -> ceval c st1 EK_Break st2) /\
  ((exists c', multi_cstep (CNormal  s c, st1) (CNormal  s c', st2) /\ start_with_cont c')  -> ceval c st1 EK_Cont st2).
Proof.
  intros.
  revert st1 st2; induction c; intros.
  + repeat split.
    - apply CSkip_halt in H.
      destruct H.
      rewrite H0.
      tauto.
    - destruct H.
      destruct H.
      apply CSkip_halt in H.
      destruct H.
      exact H1.
    - destruct H.
      destruct H.
      apply CSkip_halt in H.
      destruct H.
      rewrite H in H0.
      inversion H0.
    - destruct H.
      destruct H.
      apply CSkip_halt in H.
      destruct H.
      exact H1.
    - destruct H.
      destruct H.
      apply CSkip_halt in H.
      destruct H.
      rewrite H in H0.
      inversion H0.
  + split.
    - intros.
      apply CAss_path_spec in H.
      destruct H.
      destruct H as [? [? ?]].
      simpl.
      unfold asgn_sem.
      rewrite H0.
      split.
      * apply semantic_equiv_aexp2 in H.
        omega.
      * split.
        { tauto. }
        { intros.
          pose proof H1 _ H2.
          tauto.
        }
    - split.
      * intros.
        destruct H.
        destruct H.
        inversion H; admit.
(*       revert H H0; induction x; intros.
      - inversion H0.
      - inversion H0.
      - apply IHx1.
          admit.
          inversion H0.
          exact H2.
      - inversion H0.
      - inversion H0.
      -  *)
      * admit.
      (* 
      inversion H0.
      simpl.
      unfold asgn_sem.
      split.
      exists CSkip.
      intros.
      destruct H.
      apply CAss_path_spec in H.
      inversion H0. *)
 + split.
  - intros.
    apply CSeq_path_spec in H.
    destruct H as [st1' [? ?]].
    apply IHc1 in H.
    apply IHc2 in H0.
    simpl.
    unfold seq_sem.
    left.
    exists st1'.
    tauto.
  - split.
    * intros.
      destruct H.
      simpl.
      unfold seq_sem.
      right.
      split.
      {
        destruct H.
        admit.
      }
      {
        destruct H.
        inversion H0; unfold not; intros . discriminate H2. discriminate H3. 
      }
     * intros.
       destruct H.
       destruct H.
       inversion H0; admit.
  + pose proof semantic_equiv_bexp2 st1 b.
    destruct H.
    split.
    - intros.
      apply CIf_path_spec in H1.
      destruct H1.
      * simpl.
        unfold if_sem.
        left.
        destruct H1.
        apply H0 in H.
        { firstorder. }
        {
          apply H in H1.
          admit.
        }
        { admit. }
      * firstorder.
    - split.
      * intros.
        admit.
      * admit.
 + admit.
  (* repeat split. intros.
  apply CIf_path_spec in H.
  destruct H as [[? ?] | [? ?]].
      simpl;
    unfold if_sem.
    - left.
    split.
    apply IHc1 in H0.
    exact H0.
    pose proof semantic_equiv_bexp2 st1 b.
    destruct H1.
    pose proof H1 H.
    exact H3.
    - right.
    split.
    apply IHc2 in H0.
    exact H0.
    pose proof semantic_equiv_bexp2 st1 b.
    destruct H1.
    pose proof H2 H.
    exact H3.
    -
    exists CSkip.
    intros.
    destruct H.
    inversion H0.
    - exists CSkip.
    intros.
    destruct H.
    inversion H0.*)
  + admit.
  (* repeat split.
      intros.
      apply CWhile_path_spec in H.
      simpl.
      unfold loop_sem1.
      destruct H.
      exists x.
      split.
    revert st1 st2 H; induction x; simpl; intros.
    - pose proof semantic_equiv_bexp2 st1 b.
    destruct H.
      destruct H0.
      pose proof H2 H.
      subst st2.
      tauto.
    - destruct H as [st1' [? [? ?]]].
      specialize (IHx st1' st2).
      apply semantic_equiv_bexp2 in H.
      split.
      *left. exists st1'.
        specialize (IHc st1 st1').
        tauto.
      * exact H.
     - tauto.
     - exists CSkip.
     intros.
     destruct H.
     inversion H0.
     - exists CSkip.
     intros.
     destruct H.
     inversion H0.  *)
  + admit.
  (* split.
  intros.
  apply CBreak_halt in H.
  destruct H.
  inversion H.
  split.
  exists CBreak.
  intros.
  destruct H.
  apply CBreak_halt in H.
  simpl.
  unfold break_sem.
  tauto.
  exists CBreak.
  intros.
  destruct H.
  apply CBreak_halt in H.
  destruct H.
  inversion H0. *)
  + admit.
    (* split.
  intros.
  apply CCont_halt in H.
  destruct H.
  inversion H.
  split.
  exists CBreak.
  intros.
  destruct H.
  apply CCont_halt in H.
  destruct H.
  inversion H.
  exists CCont.
  intros.
  destruct H.
  apply CCont_halt in H.
  destruct H.
  simpl.
  unfold cont_sem.
  tauto. *)
 + admit.
Admitted.

(* ################################################################# *)
(** * Final Theorem *)

Theorem semantic_equiv_com2_trans: forall s c st1 st2,
(exists c' : com, multi_cstep (CNormal s c, st1) (CNormal s c', st2) /\ start_with_break c' -> ceval c st1 EK_Break st2) ->
((exists c' : com, multi_cstep (CNormal s c, st1) (CNormal s c', st2) /\ start_with_break c') -> ceval c st1 EK_Break st2).
Proof.
  intros.
  destruct H.
Admitted.

Theorem semantic_equiv: forall s c st1 st2,
(ceval c st1 EK_Normal st2 <->  multi_cstep (CNormal s c, st1) (CNormal s CSkip, st2))  /\
(ceval c st1 EK_Break st2  <->  exists c', multi_cstep (CNormal s c, st1) (CNormal s c', st2) /\ start_with_break c') /\
(ceval c st1 EK_Cont st2 <-> exists c', multi_cstep (CNormal s c, st1) (CNormal s c', st2) /\ start_with_cont c').
Proof.
  intros.
  repeat split.
  + apply semantic_equiv_com1.
  + apply semantic_equiv_com2.
  + apply semantic_equiv_com1.
  + apply semantic_equiv_com2.
  + apply semantic_equiv_com1.
  + apply semantic_equiv_com2.
Qed.
