Module TPTyping.

Load TPSmallSteps.
Import TPSmallSteps.

Inductive TPType :=
| TPTypeUnit
| TPTypeBool
| TPTypeInt
| TPTypeFun (t1 t2 : TPType)
| TPTypeVar (id : string)
| TPTypeError.

Inductive TPTypeEquation :=
| TPTypeEq (t1 t2 : TPType).

Inductive Subst' :=
| Subst (a b : TPType)
| Error.

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
    (* Case: TP_fun *)
    simpl in H. apply andb_prop in H. destruct H as [H H'].
    rewrite IHt1_1 with (t2:=t2_1).
    rewrite IHt1_2 with (t2:=t2_2).
    now reflexivity. now exact H'. now exact H.
    (* Case: TP_var *)
    simpl in H. apply string_eq_consist in H. rewrite H.
    now reflexivity.
  (* <= *)
    rewrite H. clear H. clear t1.
    induction t2; simpl; try reflexivity.
    (* Case: TP_fun *)
    rewrite IHt2_1. rewrite IHt2_2. simpl. now reflexivity.
    (* Case: TP_var *)
    apply string_eq_reflex.
Qed.

Fixpoint TPTypeComplexity t :=
  match t with
    | TPTypeFun t1 t2 => plus (plus (TPTypeComplexity t1) (TPTypeComplexity t2)) (1%nat)
    | _ => 1%nat
  end.

Definition TPTypeEquationComplexity t :=
  match t with
    | TPTypeEq t1 t2 => plus (TPTypeComplexity t1) (TPTypeComplexity t2)
  end.

Definition TPTypeEquationListComplexity eqlist := fold_left plus (map TPTypeEquationComplexity eqlist) 0%nat.

Require Import Recdef.

Function unify (types : list TPTypeEquation) {measure TPTypeEquationListComplexity} : list Subst' :=
  match types with
    | nil => nil
    | ((TPTypeEq (TPTypeFun t1 t2) (TPTypeFun t1' t2')) :: lst) => unify ((TPTypeEq t1 t1') :: (TPTypeEq t2 t2') :: lst)
    | (TPTypeEq (TPTypeVar id) t) :: lst => (Subst t (TPTypeVar id)) :: unify lst
    | (TPTypeEq t (TPTypeVar id)) :: lst => (Subst t (TPTypeVar id)) :: unify lst
    | (TPTypeEq t1 t2) :: lst => if TPType_eq t1 t2 then unify lst else Error :: nil
  end.
Proof.
  intros.
  induction lst.
  now intuition.
  (*unfold complexity.*)
Admitted.

Inductive TPTypingJudgement :=
  | TPTypingJudge (env : list (string * TPType)) (exp : TPExp) (type : TPType).

Definition TPTypeOfOp op :=
  match op with
    | TPOperatorPlus | TPOperatorMinus | TPOperatorMult | TPOperatorDiv | TPOperatorMod => TPTypeFun TPTypeInt (TPTypeFun TPTypeInt TPTypeInt)
    | _ => TPTypeFun TPTypeInt (TPTypeFun TPTypeInt TPTypeBool)
  end.

Fixpoint typing_rules env exp {struct exp} :=
  match exp with
    | TPExpConst TPConstantUnit => TPTypeUnit
    | TPExpConst (TPConstantBool _) => TPTypeBool
    | TPExpConst (TPConstantInt _) => TPTypeInt
    | TPExpConst (TPConstantOp op) => TPTypeOfOp op
    | TPExpConst TPConstantExn => TPTypeError
    | TPExpConst TPConstantHang => TPTypeError
    | TPExpId id => match find (fun a => string_eq id (fst a)) env with | Some (a,b) => b | None => TPTypeVar "" end
    | TPExpApp e1 e2 =>
      match typing_rules env e1 with
        | TPTypeFun t1 t2 => if TPType_eq (typing_rules env e2) t1 then t2 else TPTypeError
        | _ => TPTypeError
      end
    | TPExpAbstr id e => typing_rules env e
    | TPExpIf e1 e2 e3 => if negb (TPType_eq (typing_rules env e1) TPTypeBool) then TPTypeError else if negb (TPType_eq (typing_rules env e2) (typing_rules env e3)) then TPTypeError else typing_rules env e2
    | TPExpLet id e1 e2 => typing_rules ((id, typing_rules env e1) :: env) e2
    | TPExpRec id e => typing_rules env e
  end.

End TPTyping.