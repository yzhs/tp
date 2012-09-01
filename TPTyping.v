Module TPTyping.

Load TPSmallSteps.
Import TPSmallSteps.

Require Import List.
Require Import String.

Inductive TPType :=
| TPTypeUnit
| TPTypeBool
| TPTypeInt
| TPTypeFun (t1 t2 : TPType)
| TPTypeVar (id : string)
| TPTypeError.

(* Shorthands *)
Definition TPTypeIntToInt := TPTypeFun TPTypeInt TPTypeInt.
Definition TPTypeIntToBool := TPTypeFun TPTypeInt TPTypeBool.
Definition TPTypeIntToIntToInt := TPTypeFun TPTypeInt TPTypeIntToInt.
Definition TPTypeIntToIntToBool := TPTypeFun TPTypeInt TPTypeIntToBool.

Fixpoint TPType_eq t1 t2 :=
  match t1, t2 with
    | TPTypeUnit, TPTypeUnit => true
    | TPTypeBool, TPTypeBool => true
    | TPTypeInt, TPTypeInt => true
    | TPTypeFun t1 t2, TPTypeFun t3 t4 => andb (TPType_eq t1 t3) (TPType_eq t2 t4)
    | TPTypeVar id1, TPTypeVar id2 => string_eq id1 id2
    | TPTypeError, TPTypeError => true
    | _, _ => false
  end.

Lemma TPType_eq_consist: forall t1 t2, TPType_eq t1 t2 = true <-> t1 = t2.
Proof.
  intros t1 t2. split; intros H.
  (* => *)
    generalize dependent t2.
    induction t1; destruct t2; intros H; try (discriminate || reflexivity).
    (* Case: TPTypeFun *)
    simpl in H. apply andb_prop in H. destruct H as [H H'].
    rewrite IHt1_1 with (t2:=t2_1).
    rewrite IHt1_2 with (t2:=t2_2).
    now reflexivity. now exact H'. now exact H.
    (* Case: TPTypeVar *)
    simpl in H. apply string_eq_consist in H. rewrite H.
    now reflexivity.
  (* <= *)
    rewrite H. clear H. clear t1.
    induction t2; simpl; try reflexivity.
    (* Case: TPTypeFun *)
    rewrite IHt2_1. rewrite IHt2_2. now tauto.
    (* Case: TPTypeVar *)
    apply string_eq_reflex.
Qed.

Axiom TPTypeEnv: Set.
Axiom TPChangeEnv: TPTypeEnv -> TPIdentifier -> TPType -> TPTypeEnv.
Axiom TPChangeEnv_prop1: forall env env' id tau tau', TPChangeEnv env id tau = TPChangeEnv env' id tau' -> tau = tau'.

Inductive TPIdHasTypeInEnv: TPIdentifier -> TPTypeEnv -> TPType -> Prop :=
| typeenv_eq: forall env id id' tau, id = id' -> TPIdHasTypeInEnv id (TPChangeEnv env id' tau) tau
| typeenv_neq: forall env id id' tau tau', id <> id' -> TPIdHasTypeInEnv id env tau -> TPIdHasTypeInEnv id (TPChangeEnv env id' tau') tau.

Axiom TypeOfIdUnique: forall id env tau tau', TPIdHasTypeInEnv id env tau -> TPIdHasTypeInEnv id env tau' -> tau = tau'.
Axiom TypeOfChangedEnvEq: forall id env tau tau', TPIdHasTypeInEnv id (TPChangeEnv env id tau) tau' -> tau = tau'.
Axiom TypeOfChangedEnvNeq: forall id id' env tau tau', id <> id' -> TPIdHasTypeInEnv id' (TPChangeEnv env id tau) tau' -> TPIdHasTypeInEnv id' env tau'.
Axiom TypeOfDoubleChangeEnv: forall id env tau tau', TPChangeEnv (TPChangeEnv env id tau) id tau' = TPChangeEnv env id tau'.
Axiom DoubleChangeSwitch: forall id id' env tau tau', id <> id' -> TPChangeEnv (TPChangeEnv env id tau) id' tau' = TPChangeEnv (TPChangeEnv env id' tau') id tau.

Definition TPTypeOfOp op :=
  match op with
    | TPOperatorPlus
    | TPOperatorMinus
    | TPOperatorMult
    | TPOperatorDiv
    | TPOperatorMod => TPTypeIntToIntToInt
    | _ => TPTypeIntToIntToBool
  end.

Definition TPTypeOfConst (c: TPConstant) := match c with
 | TPConstantUnit => TPTypeUnit
 | TPConstantBool _ => TPTypeBool
 | TPConstantInt _ => TPTypeInt
 | TPConstantOp op => TPTypeOfOp op
 | TPConstantExn => TPTypeError
 | TPConstantHang => TPTypeError
end.

Inductive TPHasType: TPTypeEnv -> TPExp -> TPType -> Prop :=
| typerule_const: forall env c tau,
                  tau = (TPTypeOfConst c) ->
                  TPHasType env (TPConst c) tau
| typerule_id: forall env id tau,
               TPIdHasTypeInEnv id env tau ->
               TPHasType env (TPId id) tau
| typerule_app: forall env exp1 exp2 tau tau',
                (TPHasType env exp1 (TPTypeFun tau tau')) ->
                (TPHasType env exp2 tau) ->
                (TPHasType env (TPApp exp1 exp2) tau')
| typerule_cond: forall env exp0 exp1 exp2 tau,
                 (TPHasType env exp0 TPTypeBool) ->
                 (TPHasType env exp1 tau) ->
                 (TPHasType env exp2 tau) ->
                 (TPHasType env (TPIf exp0 exp1 exp2) tau)
| typerule_abstr: forall env exp id tau tau' tau'',
                  (TPHasType (TPChangeEnv env id tau) exp tau') ->
                  tau'' = TPTypeFun tau tau' ->
                  (TPHasType env (TPAbstr id exp) tau'')
| typerule_rec: forall env exp id tau,
                (TPHasType (TPChangeEnv env id tau) exp tau) ->
                (TPHasType env (TPRec id exp) tau)
| typerule_let: forall env exp1 exp2 id tau1 tau2,
                (TPHasType env exp1 tau1) ->
                (TPHasType (TPChangeEnv env id tau1) exp2 tau2) ->
                (TPHasType env (TPLet id exp1 exp2) tau2).

Notation "Env |> exp ::: tau" := (TPHasType Env exp tau) (at level 10, no associativity).

Definition TPWellTyped env exp := exists tau, env |> exp ::: tau.

Lemma type_unique: forall exp env tau tau', env |> exp ::: tau -> env |> exp ::: tau' -> tau = tau'.
Proof.
  intros exp env tau tau' Htau Htau'.
  generalize dependent tau.
  induction Htau'; intros tau''' Htau'''.
    (**)
    inversion_clear Htau'''.
    rewrite H. rewrite H0. reflexivity.
    (**)
    inversion_clear Htau'''.
    apply TypeOfIdUnique with (id:=id)(env:=env); assumption.
    (**)
    inversion_clear Htau'''.
    specialize IHHtau'1 with (tau0:=(TPTypeFun tau0 tau''')).
    assert (TPTypeFun tau0 tau''' = TPTypeFun tau tau'). apply IHHtau'1. assumption.
    inversion H1. reflexivity.
    (**)
    inversion_clear Htau'''. apply IHHtau'2. assumption.
    (**)
    admit.
    (**)
    admit.
    (**)
    admit.
Qed.

Lemma remove_unfree_ids: forall exp env id tau tau', TPIsNotFreeIn id exp -> (TPChangeEnv env id tau) |> exp ::: tau' -> env |> exp ::: tau'.
Proof.
  intros exp.
  induction exp; intros env id' tau tau' Hnotfree Hexp.
    (* TPConst *)
    inversion_clear Hexp. rewrite H. constructor. reflexivity.
    (* TPId *)
    inversion_clear Hexp. constructor. inversion_clear Hnotfree.
    apply TypeOfChangedEnvNeq with (id:=id')(tau:=tau); assumption.
    (* TPApp *)
    inversion_clear Hexp. inversion_clear Hnotfree. destruct H1 as [H1_1 H1_2].
    apply typerule_app with (tau:=tau0).
      apply IHexp1 with (id:=id')(tau:=tau); assumption.
      apply IHexp2 with (id:=id')(tau:=tau); assumption.
    (* TPAbstr *)
    inversion_clear Hexp. inversion Hnotfree.
      (* id = id' *)
      clear H4 exp0 H1 id0. rewrite H0.
      rewrite H3 in H. rewrite TypeOfDoubleChangeEnv in H.
      apply typerule_abstr with (tau:=tau0)(tau':=tau'0).
        assumption.
        reflexivity.
      (* id <> id' *)
      clear H2 exp0 H1 id'0 H3 id0. rewrite H0.
      apply typerule_abstr with (tau:=tau0)(tau':=tau'0).
        apply IHexp with (id:=id')(tau:=tau).
          assumption.
          rewrite DoubleChangeSwitch.
            assumption.
            apply not_eq_sym. assumption.
          reflexivity.
    (* TPIf *)
    inversion_clear Hexp. inversion_clear Hnotfree. destruct H2 as [H2_1 [H2_2 H2_3]].
    constructor.
      apply IHexp1 with (id:=id')(tau:=tau); assumption.
      apply IHexp2 with (id:=id')(tau:=tau); assumption.
      apply IHexp3 with (id:=id')(tau:=tau); assumption.
    (* TPLet *)
    inversion_clear Hexp. inversion_clear Hnotfree.
    apply typerule_let with (tau1:=tau1).
      apply IHexp1 with (id:=id')(tau:=tau); assumption.
      destruct H1.
        destruct H1 as [H1_1 H1_2].
        apply IHexp2 with (id:=id')(tau:=tau).
          assumption.
          rewrite DoubleChangeSwitch.
            assumption.
            apply not_eq_sym. assumption.
        rewrite <- TypeOfDoubleChangeEnv with (tau:=tau). rewrite <- H1 at 1. assumption.
    (* TPRec *)
    inversion_clear Hexp. inversion Hnotfree.
      (* id = id' *)
      clear H3 exp0 H0 id0. constructor. rewrite <- TypeOfDoubleChangeEnv with (tau:=tau).
      rewrite <- H2 at 1. assumption.
      (* id <> id' *)
      clear H1 exp0 H0 id'0 H2 id0. constructor.
      apply IHexp with (id:=id')(tau:=tau).
        assumption.
        rewrite DoubleChangeSwitch.
            assumption.
            apply not_eq_sym. assumption.
Qed.

Lemma add_unfree_ids: forall exp env id tau tau', TPIsNotFreeIn id exp -> env |> exp ::: tau' -> (TPChangeEnv env id tau) |> exp ::: tau'.
Proof.
  intros exp.
  induction exp; intros env id' tau tau' Hnotfree Hexp.
    (* TPConst *)
    inversion_clear Hexp. rewrite H. constructor. reflexivity.
    (* TPId *)
    inversion_clear Hexp. constructor. inversion_clear Hnotfree. constructor.
      apply not_eq_sym. assumption.
      assumption.
    (* TPApp *)
    inversion_clear Hexp. inversion_clear Hnotfree. destruct H1 as [H1_1 H1_2].
    apply typerule_app with (tau:=tau0).
      apply IHexp1; assumption.
      apply IHexp2; assumption.
    (* TPAbstr *)
    inversion_clear Hexp. inversion Hnotfree.
      (* id = id' *)
      clear H4 exp0 H1 id0. apply typerule_abstr with (tau:=tau0)(tau':=tau'0).
        rewrite TypeOfDoubleChangeEnv. assumption.
        assumption. 
      (* id <> id' *)
      clear H2 exp0 H1 id'0 H3 id0. 
      apply typerule_abstr with (tau:=tau0)(tau':=tau'0).
        rewrite DoubleChangeSwitch.
          apply IHexp; assumption.
          assumption.
        assumption.
    (* TPIf *)
    inversion_clear Hexp. inversion_clear Hnotfree. destruct H2 as [H2_1 [H2_2 H2_3]].
    constructor.
      apply IHexp1; assumption.
      apply IHexp2; assumption.
      apply IHexp3; assumption.
    (* TPLet *)
    inversion_clear Hexp. inversion_clear Hnotfree. apply typerule_let with (tau1:=tau1).
      apply IHexp1; assumption.
      destruct H1.
        destruct H1 as [H1_1 H1_2]. rewrite DoubleChangeSwitch.
          apply IHexp2; assumption.
          assumption.
        rewrite H1. rewrite TypeOfDoubleChangeEnv. assumption.
    (* TPRec *)
    inversion_clear Hexp. inversion Hnotfree.
      (* id = id' *)
      clear H3 exp0 H0 id0. constructor. rewrite TypeOfDoubleChangeEnv. assumption.
      (* id <> id' *)
      clear H1 exp0 H0 id'0 H2 id0. constructor. rewrite DoubleChangeSwitch.
        apply IHexp; assumption.
        assumption.
Qed.

Lemma substitution_and_typing : forall e e' exp id env tau tau',
  env |> e ::: tau -> 
  (TPChangeEnv env id tau) |> e' ::: tau' -> 
  TPSubstitutesInto e' id e exp -> 
  env |> exp ::: tau'.
Proof.
  intros e e' exp id env tau tau' He He' Hsubst.
  generalize dependent He'.
  generalize dependent He.
  generalize dependent tau'.
  generalize dependent tau.
  generalize dependent env.
  induction Hsubst; intros env tau tau' He He'.
    (**)
    inversion He'. clear H2 tau0 H0 env0 H c0. constructor. assumption.
    (**)
    inversion He'. clear H2 tau0 H id0 H0 env0.
    inversion H1; clear H1.
      (**)
      rewrite H3 in H. clear H3 tau0 H0 id0. rewrite H2 in H. apply TPChangeEnv_prop1 in H. rewrite H. assumption.
      (**)
      clear H4 tau0 H2 id0. inversion_clear He'. 
      assert (tau = tau'). apply TypeOfChangedEnvEq with (id:=id)(env:=env)(tau':=tau'). assumption.
      rewrite <- H2. assumption.
    (**)
    inversion He'; clear H3 tau0 H0 id0 H1 env0.
    constructor. apply TypeOfChangedEnvNeq with (id:=id)(tau:=tau); assumption.
    (**)
    inversion He'. clear H4 tau0 H1 exp2 H0 exp1 H exp0 H2 env0. constructor.
      apply IHHsubst1 with (tau:=tau); assumption.
      apply IHHsubst2 with (tau:=tau); assumption.
      apply IHHsubst3 with (tau:=tau); assumption.
    (**)
    inversion He'. clear H3 tau'0 H0 exp2 H exp1 H1 env0.
    apply typerule_app with (tau:=tau0).
      apply IHHsubst1 with (tau:=tau); assumption.
      apply IHHsubst2 with (tau:=tau); assumption.
    (**)
    inversion He'. clear H0 exp H id0 H1 env0.
    assert ((TPChangeEnv (TPChangeEnv env id tau) id tau0) = (TPChangeEnv env id tau0)).
      apply TypeOfDoubleChangeEnv with (tau:=tau).
    rewrite H in H2. apply typerule_abstr with (tau:=tau0)(tau':=tau'0).
      assumption.
      assumption.
    (**)
    apply rename_function_prop in H0. destruct H0 as [H0_1 [H0_2 H0_3]].
    inversion H0_3.
      (* id' = id'' *)
      clear H3 exp H0 id0. inversion He'. clear H5 tau'' H1 exp H0 id0 H3 env0.
      apply typerule_abstr with (tau:=tau0)(tau':=tau'0).
        apply IHHsubst2 with (tau:=tau).
          apply add_unfree_ids.
            rewrite H2 in H0_2. assumption.
            assumption.
          apply IHHsubst1 with (tau:=tau0).
            constructor. rewrite H2. constructor.
              apply not_eq_sym. assumption.
              constructor. reflexivity.
            rewrite DoubleChangeSwitch with (id:=id')(id':=id).
              rewrite TypeOfDoubleChangeEnv. assumption.
              apply not_eq_sym. assumption.
            assumption.
      (* id' <> id'' *)
      clear H1 exp H0 id'0 H2 id0. inversion He'. clear H6 tau'' H1 exp H0 id0.
      apply typerule_abstr with (tau:=tau0)(tau':=tau'0).
        apply IHHsubst2 with (tau:=tau).
          apply add_unfree_ids; assumption.
          rewrite DoubleChangeSwitch.
            apply IHHsubst1 with (tau:=tau0).
              constructor. constructor. reflexivity.
              rewrite DoubleChangeSwitch.
                apply add_unfree_ids; assumption.
                assumption.
            apply not_eq_sym. assumption.
          assumption.
    (**)
    inversion He'. clear H2 tau2 H3 exp2 H0 exp1 H id0.
    apply typerule_let with (tau1:=tau1).
      apply IHHsubst with (tau:=tau); assumption.
      rewrite TypeOfDoubleChangeEnv in H5. assumption.
    (**)
    apply rename_function_prop in H0. destruct H0 as [H0_1 [H0_2 H0_3]].
    inversion_clear H0_3. inversion_clear He'. destruct H0.
      destruct H0 as [H0_1' H0_2'].
      apply typerule_let with (tau1:=tau1).
        apply IHHsubst1 with (tau:=tau); assumption.
        apply IHHsubst3 with (tau:=tau).
          apply add_unfree_ids; assumption.
          rewrite DoubleChangeSwitch.
            apply IHHsubst2 with (tau:=tau1).
              constructor. constructor. reflexivity.
              rewrite DoubleChangeSwitch.
                apply add_unfree_ids; assumption.
                assumption.
            apply not_eq_sym. assumption.
      rewrite H0. rewrite H0 in H0_2. rewrite H0 in Hsubst2.
      rewrite H0 in IHHsubst2. rewrite H0 in H1. rewrite H0 in H0_1.
      clear H0 id''.
      apply typerule_let with (tau1:=tau1).
        apply IHHsubst1 with (tau:=tau); assumption.
        apply IHHsubst3 with (tau:=tau).
          apply add_unfree_ids. assumption.
          assumption.
          rewrite DoubleChangeSwitch.
            apply IHHsubst2 with (tau:=tau1).
              constructor. constructor. reflexivity.
              rewrite TypeOfDoubleChangeEnv. assumption.
            apply not_eq_sym. assumption.
    (**)
    inversion_clear He'. rewrite TypeOfDoubleChangeEnv in H.
    apply typerule_rec. assumption.
    (**)
    apply rename_function_prop in H0. destruct H0 as [H0_1 [H0_2 H0_3]].
    inversion_clear He'. inversion H0_3.
      (* id' = id'' *)
      clear H4 exp H1 id0. apply typerule_rec. apply IHHsubst2 with (tau:=tau).
        rewrite H3 in H0_2. apply add_unfree_ids; assumption.
        rewrite DoubleChangeSwitch. apply IHHsubst1 with (tau:=tau').
          rewrite H3. constructor. constructor. reflexivity.
          rewrite TypeOfDoubleChangeEnv. assumption.
      apply not_eq_sym. assumption.
      (* id' <> id'' *)
      clear H2 exp H1 id'0 H3 id0. apply typerule_rec. apply IHHsubst2 with (tau:=tau).
        apply add_unfree_ids; assumption.
        rewrite DoubleChangeSwitch. apply IHHsubst1 with (tau:=tau').
          constructor. constructor. reflexivity.
          rewrite DoubleChangeSwitch.
            apply add_unfree_ids; assumption.
            assumption.
        apply not_eq_sym. assumption.
Qed.

Theorem preservation : forall env e e' tau, env |> e ::: tau -> TPMakesSmallstep e e' -> env |> e' ::: tau.
Proof.
  intros env e e' tau Hwelltyped Hsmallstep.
  generalize dependent tau.
  generalize dependent env.
  induction Hsmallstep; intros env tau Hwelltyped.
    (* Op *)
    inversion_clear Hwelltyped.
    inversion_clear H.
    inversion_clear H1.
    destruct op; simpl; simpl in H; inversion H; constructor; simpl; reflexivity.
    (* Beta-V *)
    inversion_clear Hwelltyped. inversion_clear H1. inversion H4.
    rewrite <- H5 in H3.
    apply substitution_and_typing with (e:=v)(e':=exp)(id:=id)(tau:=tau0).
      assumption.
      assumption.
      assumption.
    (* App-Left *)
    inversion_clear Hwelltyped.
    apply typerule_app with (tau:=tau0).
      apply IHHsmallstep. assumption.
      assumption.
    (* App-Right *)
    inversion_clear Hwelltyped.
    apply typerule_app with (tau:=tau0).
      assumption.
      apply IHHsmallstep. assumption.
    (* Cond-Eval *)
    inversion_clear Hwelltyped.
    constructor.
      apply IHHsmallstep. assumption.
      assumption.
      assumption.
    (* Cond-True *)
    inversion_clear Hwelltyped. assumption.
    (* Cond-False *)
    inversion_clear Hwelltyped. assumption.
    (* Let-Eval *)
    inversion_clear Hwelltyped.
    apply typerule_let with (tau1:=tau1).
      apply IHHsmallstep.
        assumption.
      assumption.
    (* Let-Exec *)
    inversion_clear Hwelltyped.
    apply substitution_and_typing with (e:=v)(e':=exp)(id:=id)(tau:=tau1).
      assumption.
      assumption.
      assumption.
    (* Unfold *)
    inversion_clear Hwelltyped.
    apply substitution_and_typing with (e:=(TPRec id exp))(e':=exp)(id:=id)(tau:=tau).
      constructor. assumption.
      assumption.
      assumption.
Qed.

Definition TPClosed exp := forall id, TPIsNotFreeIn id exp.

Lemma closed_app: forall exp1 exp2, TPClosed (TPApp exp1 exp2) -> (TPClosed exp1 /\ TPClosed exp2).
Proof.
  intros exp1 exp2 H.
  unfold TPClosed in H. unfold TPClosed. split;
    intros id; specialize H with (id:=id); inversion H; destruct H2; assumption.
Qed.

Lemma closed_if: forall exp1 exp2 exp3, TPClosed (TPIf exp1 exp2 exp3) -> (TPClosed exp1 /\ TPClosed exp2 /\ TPClosed exp3).
Proof.
  intros exp1 exp2 exp3 H.
  unfold TPClosed in H. unfold TPClosed. split; try split;
    intros id; specialize H with (id:=id); inversion H; destruct H2 as [H2_1 [H2_2 H2_3]]; assumption.
Qed.

Lemma bool_value: forall env exp, env |> exp ::: TPTypeBool -> TPIsValue exp -> exp = TPFalse \/ exp = TPTrue.
Proof.
  intros env exp Hwelltyped Hvalue.
  induction Hvalue.
    (**)
    inversion Hwelltyped. destruct c; simpl in H1; try (contradict H1; now discriminate).
      (**)
      destruct b.
        right; reflexivity.
        left; reflexivity.
      (**)
      destruct op; simpl in H1; contradict H1; now discriminate.
    (**)
    inversion_clear Hwelltyped. contradict H0. discriminate.
    (**)
    inversion_clear Hwelltyped. inversion_clear H. destruct op; simpl in H1; contradict H1; discriminate.
Qed.

Lemma int_value: forall env exp, env |> exp ::: TPTypeInt -> TPIsValue exp -> exists n, exp = TPInt n.
Proof.
  intros env exp Hwelltyped Hvalue.
  induction Hvalue.
    (**)
    inversion Hwelltyped. destruct c; simpl in H1; try (contradict H1; now discriminate).
      (**)
      exists n. reflexivity.
      (**)
      destruct op; simpl in H1; contradict H1; now discriminate.
    (**)
    inversion_clear Hwelltyped. contradict H0. discriminate.
    (**)
    inversion_clear Hwelltyped. inversion_clear H. destruct op; simpl in H1; contradict H1; discriminate.
Qed.

Lemma closed_rec: forall exp id, TPClosed (TPExpRec id exp) -> TPClosed exp \/ (exists id', TPIsFreeIn id' exp).
Proof.
  intros exp id H. unfold TPClosed in H. admit.
Qed.

Theorem progress: forall env tau e, env |> e ::: tau -> TPClosed e -> (exists e', TPMakesSmallstep e e') \/ TPIsValue e.
Proof.
  intros env tau e Hwelltyped Hclosed.
  induction Hwelltyped.
    (**)
    right. constructor.
    (**)
    unfold TPClosed in Hclosed. specialize Hclosed with (id0:=id). inversion Hclosed. contradict H2. reflexivity.
    (**)
    left. apply closed_app in Hclosed. destruct Hclosed as [Hclosed1 Hclosed2].
    destruct IHHwelltyped1 as [Hexp1 | Hexp1]. assumption.
      (* exp1 makes smallstep *)
      destruct Hexp1 as [exp1' Hexp1]. exists (TPApp exp1' exp2).
      constructor. assumption.
      (* exp1 is value *)
      destruct IHHwelltyped2 as [Hexp2 | Hexp2]. assumption.
        (* exp2 makes smallstep *)
        destruct Hexp2 as [exp2' Hexp2]. exists (TPApp exp1 exp2').
        constructor; assumption.
        (* exp2 is value *)
        inversion Hexp1.
          rewrite <- H in Hwelltyped1. inversion Hwelltyped1. destruct c; try (simpl in H2; contradict H2; discriminate).
          (* exp2 is operator *)
          admit.
          (* exp2 is abstraction *)
          rewrite <- H in Hwelltyped1. inversion Hwelltyped1.
            admit.
            admit.
    (**)
    left. apply closed_if in Hclosed. destruct Hclosed as [Hclosed0 [Hclosed1 Hclosed2]].
    destruct IHHwelltyped1 as [Hexp0 | Hexp0]. assumption.
      (* exp0 makes smallstep *)
      destruct Hexp0 as [exp0' Hexp0]. exists (TPIf exp0' exp1 exp2).
      constructor. assumption.
      (* exp0 is value *)
      assert (exp0 = TPFalse \/ exp0 = TPTrue).
        apply bool_value with (env:=env); assumption.
      destruct H.
        (* exp0 = TPFalse *)
        exists exp2. rewrite H. constructor.
        (* exp0 = TPTrue *)
        exists exp1. rewrite H. constructor.
    (**)
    right. constructor.
    (**)
    assert (TPIsNotFreeIn id (TPRec id exp)).
      apply Hclosed.
    inversion H.
      left. exists exp. constructor.
      admit.
    admit.
    (**)
    left. admit.
Qed.

End TPTyping.

