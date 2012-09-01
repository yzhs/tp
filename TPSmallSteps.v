Module TPSmallSteps.

Require Import Arith.
Require Import String.

Load TPSemanticSubstitution.
Export TPSemanticSubstitution.

Open Scope string_scope.
Open Scope Z_scope.

Definition TPEvalOp op n1 n2 :=
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

(* TODO Figure out, whether this definition is correct. *)
Inductive TPMakesSmallstep: TPExp -> TPExp -> Prop :=
| smallstep_op: forall n1 n2 op,
  TPMakesSmallstep (TPApp (TPApp (TPOp op) (TPInt n1)) (TPInt n2)) (TPEvalOp op (TPInt n1) (TPInt n2))
| smallstep_betav: forall id exp exp' v,
  TPIsValue v -> TPSubstitutesInto exp id v exp' -> TPMakesSmallstep (TPApp (TPAbstr id exp) v) exp'
| smallstep_appleft: forall exp1 exp1' exp2,
  TPMakesSmallstep exp1 exp1' -> TPMakesSmallstep (TPApp exp1 exp2) (TPApp exp1' exp2)
| smallstep_appright: forall exp exp' v,
  TPIsValue v -> TPMakesSmallstep exp exp' -> TPMakesSmallstep (TPApp v exp) (TPApp v exp')
| smallstep_condeval: forall exp0 exp0' exp1 exp2,
  TPMakesSmallstep exp0 exp0' -> TPMakesSmallstep (TPIf exp0 exp1 exp2) (TPIf exp0' exp1 exp2)
| smallstep_condtrue: forall exp1 exp2,
  TPMakesSmallstep (TPIf TPTrue exp1 exp2) exp1
| smallstep_condfalse: forall exp1 exp2,
  TPMakesSmallstep (TPIf TPFalse exp1 exp2) exp2
| smallstep_leteval: forall id exp1 exp1' exp2,
  TPMakesSmallstep exp1 exp1' -> TPMakesSmallstep (TPLet id exp1 exp2) (TPLet id exp1' exp2)
| smallstep_letexec: forall id exp exp' v,
  TPIsValue v -> TPSubstitutesInto exp id v exp' -> TPMakesSmallstep (TPLet id v exp) exp'
| smallstep_unfold: forall id exp exp',
  TPSubstitutesInto exp id (TPRec id exp) exp' -> TPMakesSmallstep (TPRec id exp) exp'.

Lemma values_dont_progress: forall v, TPIsValue v -> forall exp, ~ TPMakesSmallstep v exp.
Proof.
  intros v H exp Hsmallstep.
  induction Hsmallstep; try (now inversion H).
    inversion H. apply IHHsmallstep. rewrite <- H0. constructor.
Qed.

Lemma smallsteps_are_deterministic: forall exp exp1 exp2, TPMakesSmallstep exp exp1 -> TPMakesSmallstep exp exp2 -> exp1 = exp2.
Proof.
  intros exp exp1 exp2 Hexp1.
  generalize dependent exp2.
    induction Hexp1; intros exp2' Hexp2.
      (**)
      inversion Hexp2.
        reflexivity.
        inversion H2.
          contradict H6. apply values_dont_progress. constructor.
          contradict H7. apply values_dont_progress. constructor.
        contradict H3. apply values_dont_progress. constructor.
      (**)
      inversion Hexp2.
        apply substitution_is_deterministic with (exp:=exp)(id:=id)(v:=v).
          assumption.
          assumption.
        contradict H4. apply values_dont_progress. constructor.
        contradict H5. apply values_dont_progress. assumption.
      (**)
      inversion Hexp2.
        contradict Hexp1. apply values_dont_progress. rewrite <- H0. constructor. constructor.
        contradict Hexp1. apply values_dont_progress. rewrite <- H. constructor.
        rewrite IHHexp1 with (exp2:=exp1'0).
          reflexivity.
          assumption.
        contradict Hexp1. apply values_dont_progress. assumption.
      (**)
      inversion Hexp2.
        contradict Hexp1. apply values_dont_progress. rewrite <- H2. constructor.
        contradict Hexp1. apply values_dont_progress. assumption.
        contradict H3. apply values_dont_progress. assumption.
        rewrite IHHexp1 with (exp2:=exp'0).
          reflexivity.
          assumption.
      (**)
      inversion Hexp2.
        admit.
        contradict Hexp1. apply values_dont_progress. rewrite <- H0. constructor.
        contradict Hexp1. apply values_dont_progress. rewrite <- H0. constructor.
      (**)
      inversion Hexp2.
        contradict H3. apply values_dont_progress. constructor.
        reflexivity.
      (**)
      inversion Hexp2.
        contradict H3. apply values_dont_progress. constructor.
        reflexivity.
      (**)
      inversion Hexp2.
        rewrite IHHexp1 with (exp2:=exp1'0).
          reflexivity.
          assumption.
        contradict Hexp1. apply values_dont_progress. assumption. 
      (**)
      inversion_clear Hexp2.
        contradict H1. apply values_dont_progress. assumption.
        apply substitution_is_deterministic with (exp:=exp)(id:=id)(v:=v).
          assumption.
          assumption.
      (**)
      inversion Hexp2. apply substitution_is_deterministic with (exp:=exp)(id:=id)(v:=(TPRec id exp)).
        assumption.
        assumption.
Qed.

Lemma smallsteps_dont_free_ids: forall id exp exp', TPMakesSmallstep exp exp' -> TPIsNotFreeIn id exp -> TPIsNotFreeIn id exp'.
Proof.
  intros id exp exp' Hsmallstep Hnotfree.
  induction Hsmallstep.
    (**)
    destruct op; simpl; constructor.
    (**)
    inversion_clear Hnotfree. destruct H1 as [H1 H1'].
    inversion H1.
      apply unfree_id_in_subst_exp with (exp:=exp)(sexp:=v).
        rewrite <- H4. assumption.
        assumption.
      clear H3 exp0 H2 id' H4 id1. apply subst_doesnt_free_different_ids with (exp:=exp)(sexp:=v)(id:=id0).
        apply not_eq_sym. assumption.
        assumption.
        assumption.
    (**)
    constructor. inversion_clear Hnotfree. destruct H as [H0 H1].
    split.
      apply IHHsmallstep. assumption.
      assumption.
    (**)
    constructor. inversion_clear Hnotfree. destruct H0 as [H0 H1].
    split.
      assumption.
      apply IHHsmallstep. assumption.
    (**)
    constructor. inversion_clear Hnotfree. destruct H as [H0 [H1 H2]].
    split; try split.
      apply IHHsmallstep. assumption.
      assumption.
      assumption.
    (**)
    inversion_clear Hnotfree. destruct H as [H0 [H1 H2]]. assumption.
    (**)
    inversion_clear Hnotfree. destruct H as [H0 [H1 H2]]. assumption.
    (**)
    inversion_clear Hnotfree. destruct H.
      constructor.
        left. assumption.
        apply IHHsmallstep. assumption.
      constructor.
        right. assumption.
        apply IHHsmallstep. assumption.
    (**)
    inversion_clear Hnotfree. destruct H1 as [[H1 H1'] | H1].
      apply subst_doesnt_free_different_ids with (exp:=exp)(sexp:=v)(id:=id0).
        apply not_eq_sym. assumption.
        assumption.
        assumption.
      apply unfree_id_in_subst_exp with (exp:=exp)(sexp:=v).
        assumption.
        rewrite H1. assumption.
    (**)
    inversion Hnotfree.
      apply unfree_id_in_subst_exp with (exp:=exp)(sexp:=(TPRec id0 exp)).
        constructor.
        assumption.
      apply subst_doesnt_free_different_ids with (exp:=exp)(sexp:=(TPRec id0 exp))(id:=id0).
        apply not_eq_sym. assumption.
        assumption.
        assumption.
Qed.

Lemma smallsteps_dont_unfree_ids: forall id exp exp', TPMakesSmallstep exp exp' -> TPIsFreeIn id exp -> TPIsFreeIn id exp'.
Proof.
  intros id exp exp' Hsmallstep Hfree.
  generalize dependent id.
  induction Hsmallstep; intros id' Hfree.
    (**)
    contradict Hfree. apply TPIsNotFreeIn_consist. constructor. split.
      constructor. split; constructor.
      constructor.
    (**)
    inversion_clear Hfree. destruct H1.
      inversion_clear H1. apply subst_doesnt_unfree_different_ids with (exp:=exp)(sexp:=v)(id:=id).
        apply not_eq_sym. assumption.
        assumption.
        assumption.
      apply free_id_in_subst_exp with (exp:=exp)(sexp:=v).
        assumption.
        admit.
    (**)
    (**)
    (**)
    (**)
    (**)
    (**)
    (**)
    (**)
Admitted.

End TPSmallSteps.

