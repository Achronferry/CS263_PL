Require Import PL.Imp8.
Import Assertion_D.
Import Abstract_Pretty_Printing.

(* ################################################################# *)
(** * Soundness *)

(** We will prove Hoare logic's soundness today. Recall that a Hoare logic is
sound when all provable Hoare triples are valid. *)

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



Definition hoare_sound (T: FirstOrderLogic): Prop :=
  forall P c Q,
    |-- {{ P }} c {{ Q }} ->
    |== {{ P }} c {{ Q }}.

(** We will prove that if the logic for assertion derivation is sound, then the
corresponding Hoare logic is also sound. Similarly, an assertion is called
_valid_ if it is satisfied on all interpreations. And a logic for assertion
derivation is called sound, if every provable assertion is valid. *)

Definition FOL_valid {T: FirstOrderLogic} (P: Assertion): Prop :=
  forall J: Interp, J |== P.

Definition FOL_sound (T: FirstOrderLogic): Prop :=
  forall P: Assertion, FOL_provable P -> FOL_valid P.

(** Now, we will start our Hoare logic soundness proof. *)

Lemma hoare_seq_sound : forall (P Q R: Assertion) (c1 c2: com),
  |== {{P}} c1 {{Q}} ->
  |== {{Q}} c2 {{R}} ->
  |== {{P}} c1;;c2 {{R}}.
Proof.
  unfold valid.
  intros.
  simpl in H2.
  unfold Relation_Operators.concat in H2.
  destruct H2 as [st1' [? ?]].
  specialize (H _ _ _ H1 H2).
  specialize (H0 _ _ _ H H3).
  exact H0.
Qed.

Lemma hoare_skip_sound : forall P,
  |== {{P}} Skip {{P}}.
Proof.
  unfold valid.
  intros.
  simpl in H0.
  unfold Relation_Operators.id in H0.
  rewrite <- H0.
  exact H.
Qed.

Lemma hoare_if_sound : forall P Q (b: bexp) c1 c2,
  |== {{ P AND {[b]} }} c1 {{ Q }} ->
  |== {{ P AND NOT {[b]} }} c2 {{ Q }} ->
  |== {{ P }} If b Then c1 Else c2 EndIf {{ Q }}.
Proof.
  unfold valid.
  intros.
  simpl in H2.
  unfold if_sem in H2.
  unfold Relation_Operators.union,
         Relation_Operators.intersection,
         Relation_Operators.filter1 in H2.
  destruct H2 as [[? ?] | [? ?]].
  + apply H with st1.
    - simpl.
      pose proof beval_bexp'_denote st1 La b.
      tauto.
    - exact H2.
  + apply H0 with st1.
    - simpl.
      simpl in H3.
      pose proof beval_bexp'_denote st1 La b.
      tauto.
    - exact H2.
Qed.

Lemma hoare_while_sound : forall P (b: bexp) c,
  |== {{ P AND {[b]} }} c {{P}} ->
  |== {{P}} While b Do c EndWhile {{ P AND NOT {[b]} }}.
Proof.
  unfold valid.
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

Lemma Assertion_sub_spec: forall st1 st2 La (P: Assertion) (X: var) (E: aexp),
  st2 X = aexp'_denote (st1, La) E ->
  (forall Y : var, X <> Y -> st1 Y = st2 Y) ->
  ((st1, La) |== P[ X |-> E]) <-> ((st2, La) |== P).
Proof.
  intros.
  split;intros.
  + rewrite <- aeval_aexp'_denote in H.
    

(* FILL IN HERE *) Admitted.

Lemma hoare_asgn_bwd_sound : forall P (X: var) (E: aexp),
  |== {{ P [ X |-> E] }} X ::= E {{ P }}.
Proof.
  unfold valid.
  intros.
  simpl in H0.
  destruct H0.
  pose proof aeval_aexp'_denote st1 La E.
  rewrite H2 in H0.
  pose proof Assertion_sub_spec st1 st2 La P X E H0 H1.
  tauto.
Qed.

Lemma hoare_consequence_sound : forall (T: FirstOrderLogic) (P P' Q Q' : Assertion) c,
  FOL_sound T ->
  P |-- P' ->
  |== {{P'}} c {{Q'}} ->
  Q' |-- Q ->
  |== {{P}} c {{Q}}.
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
  pose proof H1 _ _ _ H5 H4.
  specialize (H2 (st2, La)).
  tauto.
Qed.

Theorem Hoare_logic_soundness: forall (T: FirstOrderLogic) (TS: FOL_sound T),
  hoare_sound T.
Proof.
  intros.
  unfold hoare_sound.
  intros.
  remember ({{P}} c {{Q}}) as Tr.
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
  + apply hoare_asgn_bwd_sound.
  + pose proof hoare_consequence_sound T P P' Q Q' c TS H IHprovable H1.
    exact H2.
Qed.

(* Thu Apr 25 12:10:27 UTC 2019 *)
