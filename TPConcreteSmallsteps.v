Module TPConcreteSmallsteps.

Load TPSmallSteps.
Export TPSmallSteps.

Fixpoint small_step exp :=
  match exp with
    | TPExpApp (TPExpAbstr id e1) e2 =>
      if TPIsValue_bool e2
        then TPSubst e1 e2 id                        (* BETA-V *)
        else TPExpApp (small_step e1) e2              (* APP-LEFT *)
    | TPExpApp e1 exp2 =>
      match e1 with
        | TPExpApp (TPExpConst (TPConstantOp op)) exp1 =>
          if TPIsValue_bool exp1 then
            if TPIsValue_bool exp2 then
              TPEvalOp op exp1 exp2                    (* OP *)
              else TPExpApp e1 (small_step exp2)      (* APP-RIGHT *)
            else TPExpApp (small_step e1) exp2        (* APP-LEFT *)
        | _ => if TPIsValue_bool exp2
          then TPExpApp (small_step e1) exp2
          (* else TPExpApp e1 (small_step exp2) *)
          else if TPIsValue_bool e1 then TPApp e1 (small_step exp2) else TPHang
      end
    | TPExpIf (TPExpConst (TPConstantBool true)) e2 e3 => e2  (* COND-TRUE *)
    | TPExpIf (TPExpConst (TPConstantBool false)) e2 e3 => e3 (* COND-FALSE *)
    | TPExpIf e1 e2 e3 => TPExpIf (small_step e1) e2 e3       (* COND-EVAL *)
    | TPExpLet id e1 e2 =>
      if TPIsValue_bool e1 then
        TPSubst e2 e1 id                             (* LET-EXEC *)
        else TPExpLet id (small_step e1) e2           (* LET-EVAL *)
    | TPExpRec id e => TPSubst e (TPExpRec id e) id        (* UNFOLD *)
    | TPExpId _ => TPExpConst TPConstantHang                  (* free identifier, cannot do anything useful *)
    (* The function small step should only be defined for non-values, the following cases would not be needed then. *)
    | TPExpConst _ | TPExpAbstr _ _ => exp                    (* nothing to do with values *)
 end.

(*Compute small_step (small_step (TPExpApp (TPExpAbstr "x" (TPExpApp (TPExpApp (TPConstant( TPop TPplus)) (TPExpId "x")) (TPConstant (TPint 1)))) (TPConstant (TPint 2)))).*)

Theorem op_rule_implemented: forall exp op exp1 exp2, exp = (TPApp (TPApp (TPOp op) exp1) exp2) /\ andb (TPIsValue_bool exp1) (TPIsValue_bool exp2) = true -> small_step exp = TPEvalOp op exp1 exp2.
Proof.
  intros exp op exp1 exp2 H.
  destruct H as [H H']. apply andb_prop in H'. destruct H' as [H' H''].
  rewrite H.
  simpl. rewrite H'. rewrite H''.
  reflexivity.
Qed.

Theorem beta_v_rule_implemented: forall exp exp' id exp'', (exp = TPApp (TPAbstr id exp') exp'' /\ TPIsValue exp'') -> small_step exp = TPSubst exp' exp'' id.
Proof.
  intros exp exp' id exp'' H. destruct H as [H H'].
  apply TPIsValue_consist in H'.
  (* FIXME
  destruct H' as [[x H0] | [[s [x H0]] | [x [ x0 [H0 H1]]]]];
  rewrite H0; rewrite H0 in H; clear H0; clear exp''; rewrite H; clear H; simpl.
    reflexivity.
    reflexivity.
    rewrite H1. reflexivity. *)
Admitted.

Lemma small_step_value : forall v, TPIsValue v -> small_step v = v.
Proof.
  intros v H.
  induction v; try (now simpl).
  case_eq v1; intros v1' H'.
  rewrite H' in H.
  simpl in H.
  induction v1'.
  simpl.
  (* FIXME
  case_eq (TPIsValue v2); intro H1.
  now intuition. now intuition. now intuition. now intuition.
  simpl; intuition; rewrite H0; destruct (TPIsValue v2); now intuition.
  now intuition. now intuition.
  rewrite H' in H; simpl in H;now intuition.
  intro H1; rewrite H1 in H; simpl in H; now intuition.
  intro H1; rewrite H1 in H; simpl in H; now intuition.
  intros exp3 H1; rewrite H1 in H; simpl in H; now intuition.
  intros exp2 H1; rewrite H1 in H; simpl in H; now intuition.
  intro H1; rewrite H1 in H; simpl in H; now intuition.
  *)
Admitted.

(*
Theorem app_left_rule_implemented: forall exp1 exp2, small_step exp1 = exp2 -> forall exp3, small_step (TPExpApp exp1 exp3) = (TPExpApp exp2 exp3).
*)
Theorem app_left_rule_implemented: forall exp1 exp2 exp3,
  TPIsValue exp1 -> small_step exp1 = exp2 -> small_step (TPExpApp exp1 exp3) = TPExpApp exp2 exp3.
Proof.
  intros exp1 exp2 exp3 H H'.
  destruct H'.
  (* FIXME
  case_eq exp1; intros e Hexp1; case_eq (TPIsValue exp3); intro He3val.
  simpl; rewrite He3val; now reflexivity.
  rewrite Hexp1 in H; simpl in H; contradict H; now intuition.
  simpl; rewrite He3val; now reflexivity.
  *)
Admitted.

Theorem app_right_rule_implemented: forall exp1 exp2, small_step exp1 = exp2 -> forall v, TPIsValue v -> small_step (TPApp v exp1) = (TPApp v exp2).
Proof.
  (* TODO *)
Admitted.

Theorem cond_eval_rule_implemented: forall exp exp' exp1 exp2,
  (small_step exp = exp' /\ exp <> TPTrue /\ exp <> TPFalse) -> small_step (TPExpIf exp exp1 exp2) = TPIf exp' exp1 exp2.
(*
Theorem cond_eval_rule_implemented: forall exp exp', (small_step exp = exp' /\ exp <> TPTrue /\ exp <> TPFalse) -> forall exp1 exp2, small_step (TPIf exp exp1 exp2) = TPIf exp' exp1 exp2.
*)
Proof.
  intros exp exp' exp1 exp2 H.
  destruct H as [H H'].
  destruct H' as [Hnot_true Hnot_false].

  rewrite <- H. clear H. clear exp'.
  induction exp; simpl; try reflexivity.
    (* Case: TPConstant *)
    destruct c; compute; try reflexivity.
      (* Case: TPBool *)
      destruct b.
      contradict Hnot_true. reflexivity.
      contradict Hnot_false. reflexivity.
Qed.

Theorem cond_true_rule_implemented: forall exp1 exp2, small_step (TPIf TPTrue exp1 exp2) = exp1.
Proof.
  intros exp1 exp2. simpl. reflexivity.
Qed.

Theorem cond_false_rule_implemented: forall exp1 exp2, small_step (TPIf TPFalse exp1 exp2) = exp2.
Proof.
  intros exp1 exp2. simpl. reflexivity.
Qed.

(* Here we need the additional requirement TPIsValue exp = false, because otherwise there will be no "real" small step exp -> exp' *)
Theorem let_eval_rule_implemented: forall exp exp' id exp1, TPIsValue exp -> small_step exp = exp' -> small_step (TPLet id exp exp1) = TPLet id exp' exp1.
Proof.
  intros exp exp' id exp1 H H'.
  simpl.
  (* FIXME
  rewrite H.
  rewrite H'.
  reflexivity.
  *)
Admitted.

Theorem let_exec_rule_implemented: forall id v exp, TPIsValue v -> small_step (TPLet id v exp) = TPSubst exp v id.
Proof.
  intros id v exp H.
  simpl.
  (* FIXME
  rewrite H.
  reflexivity.
  *)
Admitted.

End TPConcreteSmallsteps.