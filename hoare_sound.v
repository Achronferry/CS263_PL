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
  |== {{P}} c1 {{ Q }} {{ RB }} {{ RC }} ->
  |== {{Q}} c2 {{R}} {{RB}} {{RC}}->
  |== {{P}} c1;;c2 {{R}} {{RB}} {{RC}}.
Proof.
  unfold valid.
  intros.
  repeat split; intros;
  simpl in H2; destruct H2.

  (* EK_Normal *)
  + destruct H2 as [st1' [? ?]].
    specialize (H _ _ st1' H1).
    destruct H as [? [? ?]].
    clear H1 H4 H5.
    pose proof H H2.
    specialize (H0 _ _ st2 H1).
    destruct H0 as [? [? ?]].
    clear H1 H4 H5.
    pose proof H0 H3.
    exact H1.
  + destruct H2.
    tauto.

  (* EK_Break *)
  + destruct H2 as [st1' [? ?]].
    specialize (H _ _ st1' H1).
    destruct H as [? [? ?]].
    clear H1 H4 H5.
    pose proof H H2.
    specialize (H0 _ _ st2 H1).
    destruct H0 as [? [? ?]].
    clear H1 H0 H5.
    pose proof H4 H3.
    exact H0.
  + destruct H2.
    specialize (H _ _ st2 H1).
    tauto.

  (* EK_Cont *)
  + destruct H2 as [st1' [? ?]].
    specialize (H _ _ st1' H1).
    destruct H as [? [? ?]].
    clear H1 H4 H5.
    pose proof H H2.
    specialize (H0 _ _ st2 H1).
    destruct H0 as [? [? ?]].
    clear H1 H0 H4.
    pose proof H5 H3.
    exact H0.
  + destruct H2.
    specialize (H _ _ st2 H1).
    tauto.
Qed.

Lemma hoare_skip_sound : forall P,
  |== {{P}} Skip {{P}}{{{[BFalse]}}}{{{[BFalse]}}}.
Proof.
  unfold valid.
  intros.
  repeat split;intros;
  simpl in H0; destruct H0.

  (* EK_Normal *)
  + rewrite <- H0.
    exact H.

  (* EK_Break *)
  + discriminate H1.

  (* EK_Cont *)
  + discriminate H1.
Qed.

Lemma hoare_break_sound : forall P,
  |== {{P}} Break {{{[BFalse]}}}{{P}}{{{[BFalse]}}}.
Proof.
  unfold valid.
  intros.
  repeat split; intros;
  simpl in H0; destruct H0.

  (* EK_Normal *)
  + discriminate H1.

  (* EK_Break *)
  + rewrite <- H0.
    exact H.

  (* EK_Cont *)
  + destruct H0.
    discriminate H1.
Qed.

Lemma hoare_continue_sound : forall P,
  |== {{P}} Continue {{{[BFalse]}}}{{{[BFalse]}}}{{P}}.
Proof.
  unfold valid.
  intros.
  repeat split;intros;
  simpl in H0; destruct H0.

  (* EK_Normal *)
  + discriminate H1.

  (* EK_Break *)
  + discriminate H1.

  (* EK_Cont *)
  + rewrite <- H0.
    exact H.
Qed.


Lemma hoare_if_sound : forall P Q QB QC(b: bexp) c1 c2,
  |== {{ P AND {[b]} }} c1 {{ Q }} {{ QB }} {{ QC }} ->
  |== {{ P AND NOT {[b]} }} c2 {{ Q }} {{ QB }} {{ QC }} ->
  |== {{ P }} If b Then c1 Else c2 EndIf {{ Q }} {{ QB }} {{ QC }}.
Proof.
  unfold valid.
  intros.
  repeat split; intros;
  simpl in H2; repeat destruct H2.

  (* EK_Normal *)
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

  (* EK_Break *)
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

  (* EK_Cont *)
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
  repeat split; intros;
  simpl in H1; destruct H1 as [n ?].
  + revert st1 H0 H1; induction n; intros;
    simpl in H1; repeat destruct H1.
    - simpl.
      right.
      pose proof beval_bexp'_denote st1 La b.
      tauto.
    - apply IHn with x.
      assert ((st1, La) |== I AND {[b]}).
      * simpl.
        pose proof beval_bexp'_denote st1 La b.
        tauto.
      * specialize (H _ _ x H5).
        destruct H.
        pose proof H H1.
        exact H7.
      * split.
        exact H4.
        exact H2.
    - assert ((st1, La) |== I AND {[b]}).
      * simpl.
        pose proof beval_bexp'_denote st1 La b.
        tauto.
      * specialize (H _ _ st2 H4).
        destruct H as [? [? ?]].
        pose proof H5 H1.
        simpl.
        left.
        exact H7.
    - assert ((st1, La) |== I AND {[b]}).
      * simpl.
        pose proof beval_bexp'_denote st1 La b.
        tauto.
      * specialize (H _ _ x H5).
        destruct H as [? [? ?]].
        pose proof H7 H1.
        apply IHn with x.
        exact H8.
        split.
        exact H4.
        exact H2.
  + destruct H1.
    discriminate H2.
  + destruct H1.
    discriminate H2.
Qed.

Lemma hoare_for_sound : forall U I IT P c1 (b:bexp) c2 c3,
  |== {{U}} c1 {{I}}{{{[BFalse]}}}{{{[BFalse]}}} ->
  |== {{I AND {[b]}}} c3 {{IT}}{{P}}{{IT}} ->
  |== {{IT}} c2 {{I}}{{{[BFalse]}}}{{{[BFalse]}}} ->
  |== {{U}} For( c1; b; c2) c3 EndFor {{P OR I AND NOT {[b]}}}{{{[BFalse]}}}{{{[BFalse]}}}.
Proof.
  unfold valid.
  intros.
  repeat split;intros;
  simpl in H3; destruct H3.
  + destruct H3 as [st1'[? ?]].
    specialize (H _ _ st1' H2).
    destruct H.
    clear H2 H5.
    pose proof H H3.
    clear st1 H H3.
    destruct H4 as [n ?].
    revert st1' H2 H; induction n; intros;
    simpl in H; repeat destruct H.
    - simpl.
      right.
      pose proof beval_bexp'_denote st1' La b.
      tauto.
    - apply IHn with x0.
      assert ((st1', La) |== I AND {[b]}).
      * simpl.
        pose proof beval_bexp'_denote st1' La b.
        tauto.
      * specialize (H0 _ _ x H6).
        destruct H0.
        clear H6 H7.
        pose proof H0 H.
        clear H0 H.
        specialize (H1 _ _ x0 H6).
        destruct H1.
        clear H0 H6.
        tauto.
      * tauto.
    - assert ((st1', La) |== I AND {[b]}).
      * simpl.
        pose proof beval_bexp'_denote st1' La b.
        tauto.
      * specialize (H0 _ _ st2 H5).
        destruct H0 as [? [? ?]].
        pose proof H6 H.
        simpl.
        left.
        exact H8.
    - assert ((st1', La) |== I AND {[b]}).
      * simpl.
        pose proof beval_bexp'_denote st1' La b.
        tauto.
      * specialize (H0 _ _ x H6).
        destruct H0 as [? [? ?]].
        pose proof H8 H.
        specialize (H1 _ _ x0 H9).
        destruct H1 as [? [? ?]].
        destruct H5.
        pose proof H1 H5.
        apply IHn with x0.
        exact H13.
        tauto.
  + destruct H3.
    tauto.
  + destruct H3 as [? [? [? [? ?]]]].
    discriminate H5.
  + destruct H3.
    specialize (H _ _ st2 H2).
    destruct H as [? [? ?]].
    pose proof H5 H3.
    exact H7.
  + destruct H3 as [? [? [? [? ?]]]].
    discriminate H5.
  + destruct H3.
    specialize (H _ _ st2 H2).
    destruct H as [? [? ?]].
    pose proof H6 H3.
    exact H7.
Qed.

Lemma hoare_dowhile_sound : forall U I P0 P1 (b:bexp) c,
  |== {{U}} c {{I}}{{P0}}{{I}} ->
  |== {{I AND {[b]}}} c {{I}}{{P1}}{{I}} ->
  |== {{U}} Do c While b EndWhile {{P0 OR P1 OR I AND NOT {[b]}}}{{{[BFalse]}}}{{{[BFalse]}}}.
Proof.
  unfold valid.
  intros.
  repeat split; intros.
  + destruct H2 as [n ?].
    destruct n.
    - repeat destruct H2.
      * specialize (H _ _ st2 H1).
        destruct H as [? [? ?]].
        pose proof H H2.
        simpl.
        right.
        pose proof beval_bexp'_denote st2 La b.
        tauto.
      * specialize (H _ _ st2 H1).
        destruct H as [? [? ?]].
        pose proof H4 H2.
        simpl.
        left.
        left.
        exact H6.
      * specialize (H _ _ st2 H1).
        destruct H as [? [? ?]].
        pose proof H6 H2.
        simpl.
        right.
        pose proof beval_bexp'_denote st2 La b.
        tauto.
    - repeat destruct H2.
      * specialize (H _ _ x H1).
        destruct H as [? [? ?]].
        pose proof H H2.
        destruct H4.
        clear st1 H H5 H6 H1 H2 H3.
        revert st2 H4 H7; induction n; intros.
        {
          assert ((x, La) |== I AND {[b]}).
          {
            simpl.
            pose proof beval_bexp'_denote x La b.
            tauto.
          }
          pose proof beval_bexp'_denote st2 La b.
          simpl in H4; destruct H4.
          {
            specialize (H0 _ _ st2 H).
            destruct H0 as [? [? ?]].
            clear H3 H4.
            destruct H2.
            pose proof H0 H2.
            simpl.
            right.
            tauto.
          }
          {
            destruct H2.
            {
              specialize (H0 _ _ st2 H).
              destruct H0 as [? [? ?]].
              clear H0 H4.
              pose proof H3 H2.
              simpl.
              left.
              right.
              tauto.
            }
            {
              destruct H2.
              specialize (H0 _ _ st2 H).
              destruct H0 as [? [? ?]].
              clear H0 H4.
              pose proof H5 H2.
              simpl.
              right.
              tauto.
            }
          }
        }
        {
          assert ((x, La) |== I AND {[b]}).
          {
            simpl.
            pose proof beval_bexp'_denote x La b.
            tauto.
          }
          destruct H4.
          destruct H1 as [x0 [? [? ?]]].
          pose proof H0 _ _ x0 H.
          destruct H4 as [? [? ?]].
          pose proof H4 H1.
          {
            assert ((x0, La) |== I AND {[b]}).
            {
              simpl.
              pose proof beval_bexp'_denote x0 La b.
              tauto.
            }
Admitted.

Lemma Assertion_sub_spec: forall st1 st2 La (P: Assertion) (X: var) (E: aexp),
  st2 X = aexp'_denote (st1, La) E ->
  (forall Y : var, X <> Y -> st1 Y = st2 Y) ->
  ((st1, La) |== P[ X |-> E]) <-> ((st2, La) |== P).
Proof.
  intros.
  split; intros.
  + rewrite <- aeval_aexp'_denote in H.
  (* FILL IN HERE *) Admitted.

Lemma hoare_asgn_bwd_sound : forall P (X: var) (E: aexp),
  |== {{ P [ X |-> E] }} X ::= E {{ P }}{{{[BFalse]}}}{{{[BFalse]}}}.
Proof.
  unfold valid.
  intros.
  repeat split; intros.
  + simpl in H0.
    unfold asgn_sem in H0.
    destruct H0.
    pose proof aeval_aexp'_denote st1 La E.
    rewrite H2 in H0.
    pose proof Assertion_sub_spec st1 st2 La P X E H0.
    apply H3.
    - intros.
      destruct H1.
      specialize (H5 Y H4).
      exact H5.
    - exact H.
  + simpl in H0.
    unfold asgn_sem in H0.
    destruct H0 as [? [? ?]].
    discriminate H1.
  + simpl in H0.
    unfold asgn_sem in H0.
    destruct H0 as [? [? ?]].
    discriminate H1.
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
  repeat split;intros.
  -
  specialize (H1 _ _ st2 H6).
  destruct H1 as [? [? ?]].
  pose proof H1 H7.
  specialize (H2 (st2, La)).
  tauto.
  -
  specialize (H1 _ _ st2 H6).
  destruct H1 as [? [? ?]].
  pose proof H8 H7.
  unfold derives in H3.
  apply H in H3.
  unfold FOL_valid in H3.
  simpl in H3.
  specialize (H3 (st2, La)).
  tauto.
  - 
  specialize (H1 _ _ st2 H6).
  destruct H1 as [? [? ?]].
  pose proof H9 H7.
  unfold derives in H4.
  apply H in H4.
  unfold FOL_valid in H4.
  simpl in H4.
  specialize (H4 (st2, La)).
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
    - tauto.
    - tauto.
    - exact IHprovable1.
    - exact IHprovable2.
  + eapply hoare_skip_sound.
  + eapply hoare_if_sound.
    - exact IHprovable1.
    - exact IHprovable2.
  + eapply hoare_while_sound.
    exact IHprovable.
  + eapply hoare_for_sound.
    - exact IHprovable1.
    - exact IHprovable2.
    - exact IHprovable3.
  + eapply hoare_dowhile_sound.
    - exact IHprovable1.
    - exact IHprovable2.
  + eapply hoare_asgn_bwd_sound.
  + eapply hoare_consequence_sound.
    - tauto.
    - exact H.
    - exact IHprovable.
    - exact H1.
    - exact H2.
    - exact H3.
  + eapply hoare_continue_sound.
  + eapply hoare_break_sound.
Qed.

(* Thu Apr 25 12:10:27 UTC 2019 *)
