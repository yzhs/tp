Module TPConcreteTyping.

Load TPSyntax.
Import TPSyntax.
Load TPSmallSteps.
Import TPSmallSteps.
Load TPTyping.
Import TPTyping.

Inductive TPTypeEquation :=
| TPTypeEq (t1 t2 : TPType).

Inductive Subst' :=
| Subst (a b : TPType)
| Error.

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

End TPConcreteTyping.