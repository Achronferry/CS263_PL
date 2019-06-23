Lemma CBreak_halt: forall st st' c s,
  multi_cstep(CNormal s (Break), st) (CNormal s c, st') ->
  c = CBreak /\ st = st'.
Proof.
Admitted.

Lemma CCont_halt: forall st st' c s,
  multi_cstep(CNormal s (Continue), st) (CNormal s c, st') ->
  c = CCont /\ st = st'.
Proof.
Admitted.

Theorem semantic_equiv2: forall s c st1 st2,
  (multi_cstep (CNormal  s c, st1) (CNormal  s CSkip, st2) -> ceval c st1 EK_Normal st2) /\
  (exists c', multi_cstep (CNormal  s c, st1) (CNormal  s c', st2) /\ start_with_break c' -> ceval c st1 EK_Break st2) /\
  (exists c', multi_cstep (CNormal  s c, st1) (CNormal  s c', st2) /\ start_with_cont c'  -> ceval c st1 EK_Cont st2).
Proof.
  intros.
  revert st1 st2; induction c; intros.
  + repeat split.
    - 
    apply CSkip_halt in H.
    destruct H.
    rewrite H0.
    tauto.
    -
    exists CBreak. intros.
    destruct H.
    apply CSkip_halt in H.
    destruct H.
    discriminate H.
    -
    exists CCont. intros.
    destruct H.
    apply CSkip_halt in H.
    destruct H.
    discriminate H.
 +  split.
      intros.
      apply CAss_path_spec in H.
      destruct H.
      destruct H as [? [? ?]].
      simpl.
      unfold asgn_sem.
      rewrite H0.
      split.
      apply semantic_equiv_aexp2 in H.
      omega.
      split.
      tauto.
      intros.
      pose proof H1 _ H2.
      tauto.
      
      split.
      exists CSkip.
      intros.
      destruct H.
      inversion H0.
      
      exists CSkip.
      intros.
      destruct H.
      apply CAss_path_spec in H.
      inversion H0.
 + split.
     intros.
     apply CSeq_path_spec in H.
     destruct H as [st1' [? ?]].
    apply IHc1 in H.
    apply IHc2 in H0.
    simpl.
    unfold seq_sem.
    left.
    exists st1'.
    tauto.
    
    split;
    exists CSkip;
    intros;
    destruct H;
    inversion H0.
 +
  repeat split. intros.
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
    inversion H0.
  + repeat split.
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
     inversion H0.
  + 
  split.
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
  inversion H0.
  + 
    split.
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
  tauto.

 + admit.
 + admit.
 
Admitted.