Theorem semantic_equiv2: forall s c st1 st2 c',
  (multi_cstep (CNormal  s c, st1) (CNormal  s CSkip, st2) -> ceval c st1 EK_Normal st2) /\
  (multi_cstep (CNormal  s c, st1) (CNormal  s c', st2) /\ start_with_break c' -> ceval c st1 EK_Break st2) /\
  (multi_cstep (CNormal  s c, st1) (CNormal  s c', st2) /\ start_with_cont c'  -> ceval c st1 EK_Cont st2).
Proof.
  intros.
  induction c; subst; intros.
  + repeat split.
    - 
    apply CSkip_halt in H.
    destruct H.
    rewrite H0.
    tauto.
    -
    destruct H.
    apply CSkip_halt in H.
    tauto.
    -
    destruct H.
    apply CSkip_halt in H.
    destruct H.
    inversion H0.
      * assert (Skip%imp = Break%imp).
        rewrite H2.
        auto.
        discriminate H3.
     * rewrite H in H0.
        inversion H0.
   -
   destruct H.
   apply CSkip_halt in H.
   destruct H.
   tauto.
   - 
    destruct H.
    apply CSkip_halt in H.
    destruct H.
    inversion H0.
      * rewrite H in H2.
        discriminate H2.
     * rewrite H in H0.
        inversion H0.
 + split.
      intros.
      apply CAss_path_spec in H.
      destruct H.
      destruct H as [? [? ?]].
      
      simpl.
      unfold asgn_sem.
      split.
      rewrite H0.
      apply semantic_equiv_aexp2 in H.
      omega.
      tauto.
      
      (* repeat split.
      destruct H.
      inversion H0.
      rewrite  <- H1 in H.
      inversion H; subst.
      discriminate H. *)
      admit.
 + 
    admit.
(*     repeat split. intros.
    apply CSeq_path_spec in H.
    destruct H as [st1' [? ?]].
    admit.
 *) 
 +
  repeat split. intros.
  apply CIf_path_spec in H.
      simpl.
    unfold if_sem.
    pose proof semantic_equiv_bexp2 st1 b.
    - 
    tauto.
    - intros.
    destruct H.
    discriminate H.
    apply CIf_path_spec in H.
    
Admitted.