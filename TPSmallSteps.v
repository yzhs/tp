Module TPSmallSteps.

Require Import String.
Open Scope string_scope.

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

Fixpoint TPFreeVars exp :=
  match exp with
    | TPExpConst _ => nil
    | TPExpId id => id :: nil
    | TPExpApp exp1 exp2 => app (TPFreeVars exp1) (TPFreeVars exp2)
    | TPExpIf exp1 exp2 exp3 => app (TPFreeVars exp1) (app (TPFreeVars exp2) (TPFreeVars exp3))
    | TPExpAbstr id exp => filter (ident_eq id) (TPFreeVars exp)
    | TPExpLet id e1 e2 => app (filter (ident_eq id) (TPFreeVars e2)) (TPFreeVars e1)
    | TPExpRec id exp => filter (ident_eq id) (TPFreeVars exp)
  end.

(*
Fixpoint subst free_ids e e' id :=
  match e with
    | TPConstant c => c
    | TPExpId id' => if string_eq id' id then e' else id'
    | TPExpAbstr id' e => if string_eq id' id then e else
      let id'' := new_id free_ids id' in TPExpAbstr id'' (subst (id'' :: free_ids) (subst free_ids e' (TPExpId id'') id) e' id)
    | _ => TPConstant TPunit
  end.
*)

Definition new_id highest_id id := (TPId (id, S highest_id), S highest_id).

(* Substitute id in e by e' *)
Fixpoint TPSubst (highest_id : nat) e e' id : TPExp * nat :=
  match e with
    | TPExpConst c => (e, highest_id)
    | TPExpId id' =>
      if ident_eq id' id
        then (e', highest_id)
        else (TPExpId id', highest_id)
    | TPExpIf e1 e2 e3 =>
      let (e1', n1) := TPSubst highest_id e1 e' id in
        let (e2', n2) := TPSubst n1 e2 e' id in
          let (e3', n3) := TPSubst n2 e3 e' id in
            (TPIf e1' e2' e3', n3)
    | TPExpApp e1 e2 =>
      let (e1', n1) := TPSubst highest_id e1 e' id in
        let (e2', n2) := TPSubst n1 e2 e' id in
         (TPExpApp e1' e2', n2)
    | TPExpAbstr id' e =>
      if ident_eq id' id
        then (e, highest_id)
        else let (e1, n) := TPSubst highest_id e e' id in (TPExpAbstr id' e1, n)
    | TPExpLet id' e1 e2 =>
      let (e1', n1) := TPSubst highest_id e1 e' id in
        let (e2', n2) := TPSubst n1 e2 e' id in
          (TPExpLet id' e1' (if ident_eq id' id then e2 else e2'), n2)
    | TPExpRec id' e =>
      if ident_eq id' id
        then (e, highest_id)
        else let (e'', n) := TPSubst highest_id e e' id in (TPExpRec id' e'', n)
  end.

(* TODO Figure out, whether this definition is correct. *)
Inductive TPMakesSmallstep: nat -> TPExp -> TPExp * nat -> Prop :=
| smallstep_op: forall idx n1 n2 op,
  TPMakesSmallstep idx (TPApp (TPApp (TPOp op) (TPInt n1)) (TPInt n2)) (TPEvalOp op (TPInt n1) (TPInt n2), idx)
| smallstep_betav: forall idx id exp v,
  TPIsValue v -> TPMakesSmallstep idx (TPApp (TPAbstr id exp) v) (TPSubst idx exp v id)
| smallstep_appleft: forall idx idx' exp1 exp1' exp2,
  TPMakesSmallstep idx exp1 (exp1', idx') -> TPMakesSmallstep idx (TPApp exp1 exp2) (TPApp exp1' exp2, idx')
| smallstep_appright: forall idx idx' exp exp' v,
  TPIsValue v -> TPMakesSmallstep idx exp (exp', idx') -> TPMakesSmallstep idx' (TPApp v exp) (TPApp v exp', idx')
| smallstep_condeval: forall idx idx' exp0 exp0' exp1 exp2,
  TPMakesSmallstep idx exp0 (exp0', idx') -> TPMakesSmallstep idx' (TPIf exp0 exp1 exp2) (TPIf exp0' exp1 exp2, idx')
| smallstep_condtrue: forall idx exp1 exp2,
  TPMakesSmallstep idx (TPIf TPTrue exp1 exp2) (exp1, idx)
| smallstep_condfalse: forall idx exp1 exp2,
  TPMakesSmallstep idx (TPIf TPFalse exp1 exp2) (exp2, idx)
| smallstep_leteval: forall idx idx' id exp1 exp1' exp2,
  TPMakesSmallstep idx exp1 (exp1', idx') -> TPMakesSmallstep idx' (TPLet id exp1 exp2) (TPLet id exp1' exp2, idx')
| smallstep_letexec: forall idx id exp v,
  TPIsValue v -> TPMakesSmallstep idx (TPLet id v exp) (TPSubst idx exp v id).

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
forall idx n, (n < ((length steps)-1))%nat -> TPMakesSmallstep idx (nth_default TPExn n steps) (nth_default TPExn (n+1) steps, idx).

Definition step0 := (TPLet ("square", 0%nat) (TPAbstr ("x", 1%nat) (TPApp (TPApp TPMult (TPId ("x", 1%nat))) (TPId ("x",1%nat)))) (TPApp (TPId ("square", 0%nat))(TPApp (TPId ("square", 0%nat)) (TPInt 5)))).
Definition step1 := (TPApp (TPAbstr ("x", 1%nat) (TPApp (TPApp TPMult (TPId ("x", 1%nat))) (TPId ("x", 1%nat))))(TPApp (TPAbstr ("x", 1%nat) (TPApp (TPApp TPMult (TPId ("x", 1%nat))) (TPId ("x", 1%nat)))) (TPInt 5))).
Definition step2 := (TPApp (TPAbstr ("x", 1%nat) (TPApp (TPApp TPMult (TPId ("x", 1%nat))) (TPId ("x", 1%nat))))(TPApp (TPApp TPMult (TPInt 5)) (TPInt 5))).
Definition step3 := (TPApp (TPAbstr ("x", 1%nat) (TPApp (TPApp TPMult (TPId ("x", 1%nat))) (TPId ("x", 1%nat))))(TPInt 25)).
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
  intros Hfirst Hlast n idx Hn.
  clear Hfirst. clear Hlast. simpl in Hn.
  
  repeat ((try (apply lt_n_Sm_le in Hn; apply le_n_0_eq in Hn; symmetry in Hn)) || (try (apply less_nat_cases in Hn; destruct Hn as [Hn | H])));
  try rename H into Hn; rewrite Hn; simpl; repeat constructor.
  apply smallstep_appright with (idx := n).
  now apply TPAbstrIsValue.
  assert (H : TPSubst n (TPApp (TPApp TPMult (TPId ("x", 1%nat))) (TPId ("x", 1%nat))) (TPInt 5) ("x", 1%nat) = (TPApp (TPApp TPMult (TPInt 5)) (TPInt 5), n)).
  simpl; unfold TPApp; unfold TPMult; now reflexivity.
  rewrite <- H.
  apply smallstep_betav.
  now apply TPConstIsValue.
  apply smallstep_appright with (idx := n).
  now apply TPAbstrIsValue.
  apply smallstep_op.
Qed.

End TPSmallSteps.

