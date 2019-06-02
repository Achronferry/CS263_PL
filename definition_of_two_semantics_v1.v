Require Import PL.definition_of_abc.


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
