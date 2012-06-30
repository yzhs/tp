Module TPSmallSteps.

Load TPSyntax.
Export TPSyntax.

Open Scope Z_scope.

Definition eval op n1 n2 :=
  match op,  n1, n2 with
    | TPOperatorPlus,     TPExpConst (TPConstantInt n), TPExpConst (TPConstantInt n') => TPInt (n + n')
    | TPOperatorMinus,    TPExpConst (TPConstantInt n), TPExpConst (TPConstantInt n') => TPInt (n - n')
    | TPOperatorMult,     TPExpConst (TPConstantInt n), TPExpConst (TPConstantInt n') => TPInt (n * n')
    | TPOperatorDiv,      TPExpConst (TPConstantInt n), TPExpConst (TPConstantInt n') => TPInt (n / n')
    | TPOperatorMod,      TPExpConst (TPConstantInt n), TPExpConst (TPConstantInt n') => TPInt (n mod n')
    | TPOperatorLess,     TPExpConst (TPConstantInt n), TPExpConst (TPConstantInt n') => TPBool (Zlt_bool n n')
    | TPOperatorLessEq,   TPExpConst (TPConstantInt n), TPExpConst (TPConstantInt n') => TPBool (Zle_bool n n')
    | TPOperatorGreater,  TPExpConst (TPConstantInt n), TPExpConst (TPConstantInt n') => TPBool (Zgt_bool n n')
    | TPOperatorGreaterEq,TPExpConst (TPConstantInt n), TPExpConst (TPConstantInt n') => TPBool (Zge_bool n n')
    | TPOperatorEq,       TPExpConst (TPConstantInt n), TPExpConst (TPConstantInt n') => TPBool (Zeq_bool n n')
    | TPOperatorNeq,      TPExpConst (TPConstantInt n), TPExpConst (TPConstantInt n') => TPBool (Zneq_bool n n')
    | _, _, _ => TPHang
  end.

(* TODO: rewrite using sets (ListSet?) *)
Fixpoint free exp :=
  match exp with
    | TPExpConst _ => nil
    | TPExpId id => id :: nil
    | TPExpApp exp1 exp2 => app (free exp1) (free exp2)
    | TPExpIf exp1 exp2 exp3 => app (free exp1) (app (free exp2) (free exp3))
    | TPExpAbstr id exp => filter (string_neq id) (free exp)
    | TPExpLet id e1 e2 => app (filter (string_neq id) (free e2)) (free e1)
    | TPExpRec id exp => filter (string_neq id) (free exp)
  end.

(*
Fixpoint new_id free_ids id :=

Fixpoint subst free_ids e e' id :=
  match e with
    | TPConstant c => c
    | TPExpId id' => if string_eq id' id then e' else id'
    | TPExpAbstr id' e => if string_eq id' id then e else
      let id'' := new_id free_ids id' in TPExpAbstr id'' (subst (id'' :: free_ids) (subst free_ids e' (TPExpId id'') id) e' id)
    | _ => TPConstant TPunit
  end.
*)

Fixpoint subst e e' id :=
  match e with
    | TPExpConst c => e
    | TPExpId id' => if string_eq id' id then e' else TPExpId id'
    | TPExpIf e1 e2 e3 => TPExpIf (subst e1 e' id) (subst e2 e' id) (subst e3 e' id)
    | TPExpApp e1 e2 => TPExpApp (subst e1 e' id) (subst e2 e' id)
    | TPExpAbstr id' e => if string_eq id' id then e else TPExpAbstr id' (subst e e' id)
    | TPExpLet id' e1 e2 => TPExpLet id' (subst e1 e' id) (if string_eq id id' then e2 else subst e2 e' id)
    | TPExpRec id' e => if string_eq id' id then e else TPExpRec id' (subst e e' id)
  end.

Fixpoint small_step exp :=
  match exp with
    | TPExpApp (TPExpAbstr id e1) e2 =>
      if TPIsValue e2
        then subst e1 e2 id                        (* BETA-V *)
        else TPExpApp (small_step e1) e2              (* APP-LEFT *)
    | TPExpApp e1 exp2 =>
      match e1 with
        | TPExpApp (TPExpConst (TPConstantOp op)) exp1 =>
          if TPIsValue exp1 then
            if TPIsValue exp2 then
              eval op exp1 exp2                    (* OP *)
              else TPExpApp e1 (small_step exp2)      (* APP-RIGHT *)
            else TPExpApp (small_step e1) exp2        (* APP-LEFT *)
        | _ => if TPIsValue exp2
          then TPExpApp (small_step e1) exp2
          else TPExpApp e1 (small_step exp2)
      end
    | TPExpIf (TPExpConst (TPConstantBool true)) e2 e3 => e2     (* COND-TRUE *)
    | TPExpIf (TPExpConst (TPConstantBool false)) e2 e3 => e3    (* COND-FALSE *)
    | TPExpIf e1 e2 e3 => TPExpIf (small_step e1) e2 e3  (* COND-EVAL *)
    | TPExpLet id e1 e2 =>
      if TPIsValue e1 then
        subst e2 e1 id                             (* LET-EXEC *)
        else TPExpLet id (small_step e1) e2           (* LET-EVAL *)
    | TPExpRec id e => subst e (TPExpRec id e) id        (* UNFOLD *)
 (* | _ => if TPisvalue exp then exp else TPConstant TPhang *)
    | _ => exp
 end.

(*Compute small_step (small_step (TPExpApp (TPExpAbstr "x" (TPExpApp (TPExpApp (TPConstant( TPop TPplus)) (TPExpId "x")) (TPConstant (TPint 1)))) (TPConstant (TPint 2)))).*)

Theorem op_rule_implemented: forall exp op exp1 exp2, exp = (TPApp (TPApp (TPOp op) exp1) exp2) /\ andb (TPIsValue exp1) (TPIsValue exp2) = true -> small_step exp = eval op exp1 exp2.
Proof.
  intros exp op exp1 exp2 H.
  destruct H as [H H']. apply andb_prop in H'. destruct H' as [H' H''].
  rewrite H.
  simpl. rewrite H'. rewrite H''.
  reflexivity.
Qed.

Theorem beta_v_rule_implemented: forall exp exp' id exp'', (exp = TPApp (TPAbstr id exp') exp'' /\ TPIsValue exp'' = true) -> small_step exp = subst exp' exp'' id.
Proof.
  intros exp exp' id exp'' H. destruct H as [H H'].
  apply TPIsValue_consist in H'.
  destruct H' as [[x H0] | [[s [x H0]] | [x [ x0 [H0 H1]]]]];
  rewrite H0; rewrite H0 in H; clear H0; clear exp''; rewrite H; clear H; simpl.
    reflexivity.
    reflexivity.
    rewrite H1. reflexivity.
Qed.

Theorem app_left_rule_implemented: forall exp1 exp2, small_step exp1 = exp2 -> forall exp3, small_step (TPExpApp exp1 exp3) = (TPExpApp exp2 exp3).
Proof.
  (* TODO *)
Admitted.

Theorem app_right_rule_implemented: forall exp1 exp2, small_step exp1 = exp2 -> forall v, TPIsValue v = true -> small_step (TPApp v exp1) = (TPApp v exp2).
Proof.
  (* TODO *)
Admitted.

Theorem cond_eval_rule_implemented: forall exp exp', (small_step exp = exp' /\ exp <> TPTrue /\ exp <> TPFalse) -> forall exp1 exp2, small_step (TPIf exp exp1 exp2) = TPIf exp' exp1 exp2.
Proof.
  intros exp exp' H exp1 exp2.
  destruct H as [H H'].
  destruct H' as [Hnot_true Hnot_false].

  rewrite <- H. clear H. clear exp'.
  induction exp; simpl; try reflexivity.
    (* Case: TPConstant *)
    destruct c; compute; try reflexivity.
      (* Case: TPbool *)
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

Theorem let_eval_rule_implemented: forall exp exp', small_step exp = exp' -> forall id exp1, small_step (TPLet id exp exp1) = TPLet id exp' exp1.
Proof.
  (* TODO *)
Admitted.

Theorem let_exec_rule_implemented: forall id v, TPIsValue v = true -> forall exp, small_step (TPLet id v exp) = subst exp v id.
Proof.
  (* TODO *)
Admitted.

End TPSmallSteps.
