Require Import PL.Imp8.
Import Assertion_D.
Import Abstract_Pretty_Printing.

(* ################################################################# *)
(** * Soundness *)

(** We will prove Hoare logic's soundness today. Recall that a Hoare logic is
sound when all provable Hoare triples are valid. *)

Definition hoare_sound (T: FirstOrderLogic): Prop :=
  forall P c Q QB QC,
    |-- {{ P }} c {{ Q }} {{ QB }} {{ QC }}->
    |== {{ P }} c {{ Q }} {{ QB }} {{ QC }}.

Lemma aeval_aexp'_denote: forall st La a,
  aeval a st = aexp'_denote (st, La) (ainj a).
Proof.
  intros.
  induction a; simpl.
  + reflexivity.
  + reflexivity.
  + rewrite IHa1, IHa2.
    reflexivity.
  + rewrite IHa1, IHa2.
    reflexivity.
  + rewrite IHa1, IHa2.
    reflexivity.
Qed.

Lemma beval_bexp'_denote: forall st La b,
  beval b st <-> bexp'_denote (st, La) (binj b).
Proof.
  intros.
  induction b; simpl.
  + tauto.
  + tauto.
  + rewrite <- aeval_aexp'_denote.
    rewrite <- aeval_aexp'_denote.
    tauto.
  + rewrite <- aeval_aexp'_denote.
    rewrite <- aeval_aexp'_denote.
    tauto.
  + tauto.
  + tauto.
Qed.


(** We will prove that if the logic for assertion derivation is sound, then the
corresponding Hoare logic is also sound. Similarly, an assertion is called
_valid_ if it is satisfied on all interpreations. And a logic for assertion
derivation is called sound, if every provable assertion is valid. *)

Definition FOL_valid {T: FirstOrderLogic} (P: Assertion): Prop :=
  forall J: Interp, J |== P.

Definition FOL_sound (T: FirstOrderLogic): Prop :=
  forall P: Assertion, FOL_provable P -> FOL_valid P.

(** Now, we will start our Hoare logic soundness proof. *)

Lemma hoare_seq_sound : forall (P Q R QB QC RB RC: Assertion) (c1 c2: com),
  |== {{P}} c1 {{ Q }} {{ QB }} {{ QC }} ->
  |== {{Q}} c2 {{R}} {{RB}} {{RC}}->
  |== {{P}} c1;;c2 {{R}} {{RB}} {{RC}}.
Proof.
  unfold valid.
  intros.
  simpl in H2.
  unfold seq_sem in H2.
  destruct H2.
  + destruct H2 as [st1' [? ?]].
    specialize (H _ _ _ H1 H2).
    specialize (H0 _ _ _ H H3).
    exact H0.
  + destruct H2.
    unfold not in H3.
    destruct H3.
    reflexivity.
Qed.

Lemma hoare_skip_sound : forall P,
  |== {{P}} Skip {{P}}{{{[BFalse]}}}{{{[BFalse]}}}.
Proof.
  unfold valid.
  intros.
  simpl in H0.
  unfold skip_sem in H0.
  destruct H0.
  rewrite <- H0.
  exact H.
Qed.

Lemma hoare_break_sound : forall P,
  |== {{P}} Skip {{{[BFalse]}}}{{P}}{{{[BFalse]}}}.
Proof.
Admitted.
(*unfold valid.
  intros.
  simpl in H0.
  unfold skip_sem in H0.
  destruct H0.
  rewrite <- H0.
  exact H.
Qed. *)

Lemma hoare_continue_sound : forall P,
  |== {{P}} Skip {{{[BFalse]}}}{{{[BFalse]}}}{{P}}.
Proof.
Admitted.
(*unfold valid.
  intros.
  simpl in H0.
  unfold skip_sem in H0.
  destruct H0.
  rewrite <- H0.
  exact H.
Qed. *)

Lemma hoare_if_sound : forall P Q QB QC(b: bexp) c1 c2,
  |== {{ P AND {[b]} }} c1 {{ Q }} {{ QB }} {{ QC }} ->
  |== {{ P AND NOT {[b]} }} c2 {{ Q }} {{ QB }} {{ QC }} ->
  |== {{ P }} If b Then c1 Else c2 EndIf {{ Q }} {{ QB }} {{ QC }}.
Proof.
  unfold valid.
  intros.
  simpl in H2.
  unfold if_sem in H2.
  repeat destruct H2.
  + apply H with st1.
    - simpl.
      pose proof beval_bexp'_denote st1 La b.
      tauto.
    - exact H2.
  + apply H0 with st1.
    - simpl.
      pose proof beval_bexp'_denote st1 La b.
      tauto.
    - exact H2.
Qed.

Lemma hoare_while_sound : forall I P(b: bexp) c,
  |== {{ I AND {[b]} }} c {{I}} {{P}} {{I}} ->
  |== {{ I }} While b Do c EndWhile {{ P OR (I AND NOT {[b]}) }} {{{[BFalse]}}} {{{[BFalse]}}}.
Proof.
  unfold valid.
  intros.
  simpl in H1.
  unfold loop_sem1 in H1.
  destruct H1 as [n ?].
  revert st1 H0 H1; induction n; intros.
  + simpl in H1.
    repeat destruct H1.
    simpl.
    right.
    pose proof beval_bexp'_denote st1 La b.
    rewrite <- H1.
    tauto.
  + simpl in H1.
    repeat destruct H1.
    - apply IHn with x.
      * assert ((st1, La) |== I AND {[b]}).
        {
          simpl.
          pose proof beval_bexp'_denote st1 La b.
          tauto.
        }
        specialize (H _ _ _ H5 H1).
        exact H.
      * split; [exact H4|exact H2].
    - simpl in H1.
      
      

Admitted.
(*   unfold valid.
  intros.
  simpl in H1.
  unfold loop_sem in H1.
  unfold Relation_Operators.omega_union in H1.
  destruct H1 as [n ?].
  revert st1 H0 H1; induction n; intros.
  + simpl in H1.
    unfold Relation_Operators.intersection,
           Relation_Operators.id,
           Relation_Operators.filter1 in H1.
    destruct H1.
    subst st2.
    simpl.
    pose proof beval_bexp'_denote st1 La b.
    tauto.
  + simpl in H1.
    unfold Relation_Operators.intersection,
           Relation_Operators.concat,
           Relation_Operators.filter1 in H1.
    destruct H1 as [[st1' [? ?]] ?].
    apply IHn with st1'.
    - apply H with st1.
      * simpl.
        pose proof beval_bexp'_denote st1 La b.
        tauto.
      * exact H1.
    - exact H2.
Qed.
 *)

Lemma hoare_for_sound : forall U I IT P c1 (b:bexp) c2 c3,
  |== {{U}} c1 {{I}}{{{[BFalse]}}}{{{[BFalse]}}} ->
  |== {{I AND {[b]}}} c3 {{IT}}{{P}}{{IT}} ->
  |== {{IT}} c2 {{I}}{{{[BFalse]}}}{{{[BFalse]}}} ->
  |== {{U}} For( c1; b; c2) c3 EndFor {{P OR I AND NOT {[b]}}}{{{[BFalse]}}}{{{[BFalse]}}}.
Proof.
  unfold valid.
  intros.
Admitted.

Lemma hoare_dowhile_sound : forall U I P0 P1 (b:bexp) c,
  |== {{U}} c {{I}}{{P0}}{{I}} ->
  |== {{I AND {[b]}}} c {{I}}{{P1}}{{I}} ->
  |== {{U}} Do c While b EndWhile {{P0 OR P1 OR I AND NOT {[b]}}}{{{[BFalse]}}}{{{[BFalse]}}}.
Proof.
  unfold valid.
  intros.
Admitted.

Lemma Assertion_sub_spec: forall st1 st2 La (P: Assertion) (X: var) (E: aexp),
  st2 X = aexp'_denote (st1, La) E ->
  (forall Y : var, X <> Y -> st1 Y = st2 Y) /\ EK_Normal = EK_Normal->
  ((st1, La) |== P[ X |-> E]) <-> ((st2, La) |== P).
Proof.
  intros.
  split;intros.
  + rewrite <- aeval_aexp'_denote in H.
    

(* FILL IN HERE *) Admitted.

Lemma hoare_asgn_bwd_sound : forall P (X: var) (E: aexp),
  |== {{ P [ X |-> E] }} X ::= E {{ P }}{{{[BFalse]}}}{{{[BFalse]}}}.
Proof.
  unfold valid.
  intros.
  simpl in H0.
  unfold asgn_sem in H0.
  destruct H0.
  pose proof aeval_aexp'_denote st1 La E.
  rewrite H2 in H0.
  pose proof Assertion_sub_spec st1 st2 La P X E H0.
  apply H3.
  + split.
    - intros.
      specialize (H1 Y H4).
      destruct H1.
      exact H1.
    - reflexivity.
  + exact H.
Qed.

Lemma hoare_consequence_sound : forall (T: FirstOrderLogic) (P P' Q Q' QB QB' QC QC': Assertion) c,
  FOL_sound T ->
  P |-- P' ->
  |== {{P'}} c {{Q'}} {{QB'}} {{QC'}} ->
  Q' |-- Q ->
  QB' |-- QB ->
  QC' |-- QC ->
  |== {{P}} c {{Q}} {{QB}} {{QC}}.
Proof.
  intros.
  unfold FOL_sound in H.
  unfold derives in H0, H2.
  apply H in H0.
  apply H in H2.
  unfold FOL_valid in H0, H2.
  simpl in H0, H2.
  unfold valid in H1.
  unfold valid.
  intros.
  assert ((st1, La) |== P').
  {
    specialize (H0 (st1, La)).
    tauto.
  }
  specialize (H1 _ _ _ H7 H6).
  specialize (H2 (st2, La)).
  tauto.
Qed.

Theorem Hoare_logic_soundness: forall (T: FirstOrderLogic) (TS: FOL_sound T),
  hoare_sound T.
Proof.
  intros.
  unfold hoare_sound.
  intros.
  remember ({{P}} c {{Q}}{{QB}}{{QC}}) as Tr.
  clear P c Q HeqTr.
  induction H.
  + eapply hoare_seq_sound.
    - exact IHprovable1.
    - exact IHprovable2.
  + apply hoare_skip_sound.
  + apply hoare_if_sound.
    - exact IHprovable1.
    - exact IHprovable2.
  + apply hoare_while_sound.
    exact IHprovable.
  + apply hoare_for_sound with IT.
    - exact IHprovable1.
    - exact IHprovable2.
    - exact IHprovable3.
  + apply hoare_dowhile_sound.
    - exact IHprovable1.
    - exact IHprovable2.
  + apply hoare_asgn_bwd_sound.
  + pose proof hoare_consequence_sound T P P' Q Q' QB0 QB' QC0 QC' c TS H IHprovable H1 H2 H3.
    exact H4.
  + apply hoare_continue_sound.
  + apply hoare_break_sound.
Qed.



(* Thu Apr 25 12:10:27 UTC 2019 *)
