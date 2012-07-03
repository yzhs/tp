Module TPSmallSteps.

Load TPSyntax.
Export TPSyntax.

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

(* TODO: rewrite using sets (ListSet?) *)
Fixpoint TPFreeVars exp :=
  match exp with
    | TPExpConst _ => nil
    | TPExpId id => id :: nil
    | TPExpApp exp1 exp2 => app (TPFreeVars exp1) (TPFreeVars exp2)
    | TPExpIf exp1 exp2 exp3 => app (TPFreeVars exp1) (app (TPFreeVars exp2) (TPFreeVars exp3))
    | TPExpAbstr id exp => filter (string_neq id) (TPFreeVars exp)
    | TPExpLet id e1 e2 => app (filter (string_neq id) (TPFreeVars e2)) (TPFreeVars e1)
    | TPExpRec id exp => filter (string_neq id) (TPFreeVars exp)
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

(* Substitute id in e by e' *)
Fixpoint TPSubst e e' id :=
  match e with
    | TPExpConst c => e
    | TPExpId id' => if string_eq id' id then e' else TPExpId id'
    | TPExpIf e1 e2 e3 => TPExpIf (TPSubst e1 e' id) (TPSubst e2 e' id) (TPSubst e3 e' id)
    | TPExpApp e1 e2 => TPExpApp (TPSubst e1 e' id) (TPSubst e2 e' id)
    | TPExpAbstr id' e => if string_eq id' id then e else TPExpAbstr id' (TPSubst e e' id)
    | TPExpLet id' e1 e2 => TPExpLet id' (TPSubst e1 e' id) (if string_eq id id' then e2 else TPSubst e2 e' id)
    | TPExpRec id' e => if string_eq id' id then e else TPExpRec id' (TPSubst e e' id)
  end.
Inductive TPMakesSmallstep: TPExp -> TPExp -> Prop :=
| smallstep_op: forall n1 n2 op, TPMakesSmallstep (TPApp (TPApp (TPOp op) (TPInt n1)) (TPInt n2)) (TPEvalOp op (TPInt n1) (TPInt n2))
| smallstep_betav: forall id exp v, TPIsValue v -> TPMakesSmallstep (TPApp (TPAbstr id exp) v) (TPSubst exp v id)
| smallstep_appleft: forall exp1 exp1' exp2, TPMakesSmallstep exp1 exp1' -> TPMakesSmallstep (TPApp exp1 exp2) (TPApp exp1' exp2)
| smallstep_appright: forall exp exp' v, TPIsValue v -> TPMakesSmallstep exp exp' -> TPMakesSmallstep (TPApp v exp) (TPApp v exp')
| smallstep_condeval: forall exp0 exp0' exp1 exp2, TPMakesSmallstep exp0 exp0' -> TPMakesSmallstep (TPIf exp0 exp1 exp2) (TPIf exp0' exp1 exp2)
| smallstep_condtrue: forall exp1 exp2, TPMakesSmallstep (TPIf TPTrue exp1 exp2) exp1
| smallstep_condfalse: forall exp1 exp2, TPMakesSmallstep (TPIf TPFalse exp1 exp2) exp2
| smallstep_leteval: forall id exp1 exp1' exp2, TPMakesSmallstep exp1 exp1' -> TPMakesSmallstep (TPLet id exp1 exp2) (TPLet id exp1' exp2)
| smallstep_letexec: forall id exp v, TPIsValue v -> TPMakesSmallstep (TPLet id v exp) (TPSubst exp v id).

Inductive NonEmptyList (A: Type) :=
| Singleton: A -> NonEmptyList A
| Cons: A -> NonEmptyList A -> NonEmptyList A.

Implicit Arguments Singleton [A].
Implicit Arguments Cons [A].

Definition first {A: Type}(l: NonEmptyList A) := match l with
| Singleton a => a
| Cons a l' => a
end.

Fixpoint last {A: Type}(l: NonEmptyList A) := match l with
| Singleton a => a
| Cons a l' => (last l')
end.

Fixpoint length {A: Type}(l: NonEmptyList A) := match l with
| Singleton a => 1%nat
| Cons a l' => S (length l')
end.

Fixpoint nth_default {A: Type}(def: A)(n: nat)(l: NonEmptyList A) := match n,l with
| O, l => first l
| S n', Cons a l' => nth_default def n' l'
| S n', Singleton a => def
end.

Definition TPMultipleSmallsteps exp exp':= 
exists steps: NonEmptyList TPExp, 
first steps = exp ->
last steps = exp' ->
forall n, (n < ((length steps)-1))%nat -> TPMakesSmallstep (nth_default TPExn n steps) (nth_default TPExn (n+1) steps).

Definition step0 :=  (TPLet "square" (TPAbstr "x" (TPApp (TPApp TPMult (TPId "x")) (TPId "x"))) (TPApp (TPId "square")(TPApp (TPId "square") (TPInt 5)))).
Definition step1 := (TPApp (TPAbstr "x" (TPApp (TPApp TPMult (TPId "x")) (TPId "x")))(TPApp (TPAbstr "x" (TPApp (TPApp TPMult (TPId "x")) (TPId "x"))) (TPInt 5))).
Definition step2 := (TPApp (TPAbstr "x" (TPApp (TPApp TPMult (TPId "x")) (TPId "x")))(TPApp (TPApp TPMult (TPInt 5)) (TPInt 5))).
Definition step3 := (TPApp (TPAbstr "x" (TPApp (TPApp TPMult (TPId "x")) (TPId "x")))(TPInt 25)).
Definition step4 := (TPApp (TPApp TPMult (TPInt 25)) (TPInt 25)).
Definition step5 := TPInt 625.

Lemma less_nat_cases: forall k n: nat, (k < (S n) <-> k < n \/ k = n)%nat.
Proof.
  intros k n.
  split; intros H.
  (* => *)
    apply lt_n_Sm_le in H.
    case_eq (beq_nat k n); intros Heq.
      (* Case: true *)
      right. apply beq_nat_true_iff in Heq. exact Heq.
      (* Case: false *)
      left. apply beq_nat_false_iff in Heq.
      apply nat_total_order in Heq. destruct Heq as [Heq | Heq].
        (* Case: k < n *)
        exact Heq.
        (* Case: k > n *)
        apply le_lt_trans with (n:=k) in Heq.
          contradict Heq. apply lt_irrefl.
          exact H. 
  (* <= *)
    destruct H as [H | H].
      apply lt_S. exact H.
      rewrite H. constructor.
Qed.

Example test1: TPMultipleSmallsteps step0 step5.
Proof.
  unfold TPMultipleSmallsteps.
  exists (Cons step0 (Cons step1 (Cons step2 (Cons step3 (Cons step4 (Singleton step5)))))).
  intros Hfirst Hlast n Hn.
  simpl in Hfirst. simpl in Hlast. simpl in Hn.
  
  repeat ((try (apply lt_n_Sm_le in Hn; apply le_n_0_eq in Hn; symmetry in Hn)) || (try (apply less_nat_cases in Hn; destruct Hn as [Hn | H]))); try rename H into Hn;
  rewrite Hn; simpl; repeat constructor.
Qed.

End TPSmallSteps.
