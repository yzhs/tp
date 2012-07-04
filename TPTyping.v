Module TPTyping.

Load TPSmallSteps.
Export TPSmallSteps.

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
    rewrite IHt2_1. rewrite IHt2_2. simpl. now reflexivity.
    (* Case: TPTypeVar *)
    apply string_eq_reflex.
Qed.

Definition TPTypeEnv := list ((string * nat) * TPType).

Fixpoint change_env id tau env: TPTypeEnv := match env with
| nil => (id, tau)::nil
| (id', tau')::env' => if ident_eq id id' then (id, tau)::env' else (id', tau')::(change_env id tau env')
end.

Lemma change_env_consist: forall env id tau, In (id, tau) (change_env id tau env).
Proof.
  intros env id tau.
  induction env; simpl.
    left. reflexivity.
    destruct a as (id', tau'). case_eq (ident_eq id id'); intros H; simpl.
      left. reflexivity.
      right. exact IHenv.
Qed.

Lemma change_env_small: forall env id tau, change_env id tau env = (id, tau) :: nil -> env = nil \/ (exists tau'', env = (id, tau'') :: nil).
Proof.
  intros env id tau H.
  induction env.
    left. reflexivity.
    right. destruct a as (id', tau'). case_eq (ident_eq id id'); intros H'; simpl in H; rewrite H' in H; inversion H;
      exists tau'. apply ident_eq_consist in H'. rewrite H'. reflexivity.
      symmetry in H1. apply ident_eq_consist in H1. rewrite H1 in H'. contradict H'. discriminate.
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
                   In (id, tau) env ->
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

Lemma change_env_inversion: forall env env' id tau, env' = change_env id tau env -> TPHasType env' (TPId id) tau.
Proof.
  intros env env' id tau H.
  induction env.
    simpl in H. rewrite H. constructor. simpl. left. reflexivity.
    destruct a as [id' tau']. constructor. rewrite H. simpl.
    case_eq (ident_eq id id'); intros H'; simpl.
      left. reflexivity.
      right. apply change_env_consist.
Qed.

Definition TPWellTyped env exp := exists tau, TPHasType env exp tau.

Example test1: forall env, TPHasType env (TPApp TPPlus (TPInt 1)) TPTypeIntToInt.
Proof.
  intros.
  apply typerule_app with (tau:=TPTypeInt); apply typerule_const; simpl; reflexivity.
Qed.

Example test2: forall env, TPHasType env (TPApp (TPApp TPPlus (TPInt 1)) (TPInt 1)) TPTypeInt.
Proof.
  intros.
  repeat (apply typerule_app with (tau:=TPTypeInt));
    apply typerule_const; simpl; reflexivity.
Qed.

End TPTyping.

