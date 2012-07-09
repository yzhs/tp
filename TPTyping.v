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

(* A type environment is a function from identifiers (which have type
 * (string * nat)) to their types.  This function is represented here using a
 * list of identifier, type pairs. *)
Definition TPTypeEnv := list ((string * nat) * TPType).

(* This is basically how the environments were extended in lecture. *)
Definition change_env id tau env: TPTypeEnv := (id, tau) :: env.

Fixpoint find_first ident lst : option TPType :=
  match lst with
    | nil => None
    | (id, tau) :: ids => if ident_eq ident id then Some tau else find_first ident ids
  end.

Lemma change_env_consist: forall env id tau, find_first id (change_env id tau env) = Some tau.
Proof.
  intros env id tau.
  simpl.
  rewrite ident_eq_reflex.
  reflexivity.
Qed.

Lemma change_env_small: forall env id tau, change_env id tau env = (id, tau) :: nil -> env = nil.
Proof.
  intros env id tau H.
  unfold change_env in H.
  induction env.
  reflexivity.
  inversion H.
Qed.

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
                   find_first id env = Some tau ->
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
| typerule_abstr: forall env env' exp id tau tau',
                      env' = change_env id tau env ->
                      (TPHasType env' exp tau') ->
                      (TPHasType env (TPAbstr id exp) (TPTypeFun tau tau'))
| typerule_rec: forall env env' exp id tau,
                    env' = change_env id tau env ->
                    (TPHasType env' exp tau) ->
                    (TPHasType env (TPRec id exp) tau)
| typerule_let: forall env env' exp1 exp2 id tau1 tau2,
                    env' = change_env id tau1 env ->
                    (TPHasType env exp1 tau1) ->
                    (TPHasType env' exp2 tau2) ->
                    (TPHasType env (TPLet id exp1 exp2) tau2).

Notation "Env |> exp ::: tau" := (TPHasType Env exp tau) (at level 10, no associativity).

Lemma change_env_inversion: forall env env' id tau, env' = change_env id tau env -> env' |> TPId id ::: tau.
Proof.
  intros env env' id tau H.
  induction env; unfold change_env in H; rewrite H; apply typerule_id; simpl; rewrite ident_eq_reflex; reflexivity.
Qed.

Definition TPWellTyped env exp := exists tau, env |> exp ::: tau.

Example test1: forall env, TPHasType env (TPApp TPPlus (TPInt 1)) TPTypeIntToInt.
Proof.
  intros.
  apply typerule_app with (tau:=TPTypeInt); apply typerule_const; simpl; reflexivity.
Qed.

Example test2: forall env, env |> TPApp (TPApp TPPlus (TPInt 1)) (TPInt 1) ::: TPTypeInt.
Proof.
  intros.
  repeat (apply typerule_app with (tau:=TPTypeInt));
    apply typerule_const; simpl; reflexivity.
Qed.

Lemma type_unique: forall exp env tau tau', env |> exp ::: tau /\ env |> exp ::: tau' -> tau = tau'.
Proof.
  intros exp.
  induction exp; intros env tau tau' H; destruct H as [Htau Htau'].
  (* TPConst *)
  inversion_clear Htau; inversion_clear Htau'.
  induction c; simpl in H; simpl in H0; rewrite H; rewrite H0; reflexivity.
  (* TPId *)
  inversion_clear Htau; inversion_clear Htau'.
  rewrite H in H0; inversion_clear H0; reflexivity.
  (* TPApp *)
  inversion_clear Htau; inversion_clear Htau'.
  inversion H; try (
    assert (IH' := IHexp1 env (TPTypeFun tau0 tau) (TPTypeFun tau1 tau'));
    assert (Hpremise : env |> exp1 ::: (TPTypeFun tau0 tau) /\ env |> exp1 ::: (TPTypeFun tau1 tau'));
      [split; assumption | assert (Heq := IH' Hpremise); inversion Heq; reflexivity]
  ).
  (* TPAbstr *)
  induction (TPExpAbstr id exp).
  inversion_clear Htau; inversion_clear Htau'.
  unfold change_env in H; unfold change_env in H1.
  rewrite H in H0; rewrite H1 in H2; clear H; clear H1.
  apply IHexp with (env := env) (tau := TPTypeFun tau0 tau'0) (tau' := TPTypeFun tau1 tau'1).
  split.
  admit.
  (* TPIf *)
  apply IHexp2.
  split; assumption.
  (* TPLet *)
  admit.
  (* TPRec *)
  apply IHexp.
  unfold change_env in H; rewrite H in H0; clear H.
  unfold change_env in H1; rewrite H1 in H2; clear H1.
  clear env'; clear env'0.
  admit.
Qed.

Lemma TPSubst_preserves_types : forall n n' e e' exp id env tau tau',
  env |> e ::: tau -> env |> e' ::: tau' -> env |> TPId id ::: tau' -> (exp , n') = TPSubst n e e' id -> env |> exp ::: tau.
Proof.
  intros n n' e e' exp id env tau tau' He He' Hid Hsubst.
  generalize dependent n; induction e; intros n Hsubst; simpl in Hsubst.
  (* TPConst *)
    inversion_clear Hsubst.
    now assumption.
  (* TPId *)
    case_eq (ident_eq id0 id); intro Heq; rewrite Heq in Hsubst.
    inversion Hsubst.
    apply ident_eq_consist in Heq.
    rewrite Heq in He.
    assert (Htau : tau = tau').
    apply type_unique with (exp := TPExpId id) (env := env).
    split; [ | unfold TPId in Hid]; assumption.
    rewrite Htau; exact He'.
    inversion Hsubst; assumption.
  (* TPApp *)
    case_eq (TPSubst n e1 e' id); intros; rewrite H in Hsubst.
    case_eq (TPSubst n0 e2 e' id); intros; rewrite H0 in Hsubst.
    inversion Hsubst.
    destruct H3.
    clear Hsubst.
    admit.
  (* TPAbstr *)
    case_eq (ident_eq id0 id); intro Heq; rewrite Heq in Hsubst.
    inversion_clear Hsubst.
    apply ident_eq_consist in Heq.
    destruct Heq.
    admit.
    destruct (TPSubst n e e' id).
    inversion_clear Hsubst.
    admit.
  (* TPIf *)
  admit.
  (* TPLet *)
  admit.
  (* TPRec *)
  admit.
Qed.

Theorem preservation : forall env e e' tau n n', env |> e ::: tau -> TPMakesSmallstep n e (e', n') -> env |> e' ::: tau.
Proof.
  intros env e e' tau n n' Hwelltyped Hsmallstep.
  inversion Hwelltyped.
  (* case TPConst *)
  induction c; simpl in H; rewrite <- H1 in Hsmallstep; now inversion Hsmallstep.
  (* case TPId *)
  inversion Hsmallstep; rewrite <- H1 in Hsmallstep; now inversion Hsmallstep.
  (* case TPApp *)
  inversion Hsmallstep.
    (* case OP *)
    rewrite <- H5 in Hsmallstep; induction op; simpl; apply typerule_const;
    rewrite <- H5 in H2; inversion H2; rewrite H10 in H0; rewrite H9 in H;
    inversion H0; simpl in H12; inversion H; inversion H17; inversion H22;
    now reflexivity.
    (* case BETA-V *)
    rewrite <- H6 in H2; inversion H2.
    rewrite H9 in H; rewrite H10 in H0.

    apply TPSubst_preserves_types.
    admit.
    (* case APP-LEFT *)
    admit.
    (* case APP-RIGHT *)
    admit.
    (* case COND-EVAL *)
    apply typerule_cond.
      (* condition *)
      admit.
      (* then clause *)
      admit.
      (* else clause *)
      admit.
    (* case COND-TRUE *)
    admit.
    (* case COND-FALSE *)
    admit.
    (* case LET-EVAL *)
    admit.
    (* case LET-EXEC *)
    admit.
    *)
  (* case TPIf *)
  admit.
  (* case TPAbstr *)
  rewrite <- H2 in Hsmallstep; now inversion Hsmallstep.
  (* case TPRec *)
  rewrite <- H2 in Hsmallstep; now inversion Hsmallstep.
  (* case TPLet *)
  admit.
Qed.

End TPTyping.

