Module TPSyntaxExpressions.

Load TPSyntaxConstants.
Export TPSyntaxConstants.

Load TPSyntaxIdentifiers.
Import TPSyntaxIdentifiers.

Inductive TPExp :=
 | TPExpConst (c : TPConstant)
 | TPExpId (id : TPIdentifier)
 | TPExpApp (a b : TPExp)
 | TPExpAbstr (id : TPIdentifier) (exp : TPExp)
 | TPExpIf (exp1 exp2 exp3 : TPExp)
 | TPExpLet (id : string * nat) (exp1 exp2 : TPExp)
 | TPExpRec (id : string * nat) (exp : TPExp).

(* Shorthands *)
Definition TPOp op := (TPExpConst (TPConstantOp op)).

Definition TPUnit := (TPExpConst TPConstantUnit).
Definition TPBool b := (TPExpConst (TPConstantBool b)).
Definition TPFalse := (TPExpConst (TPConstantBool false)).
Definition TPTrue := (TPExpConst (TPConstantBool true)).
Definition TPInt n := (TPExpConst (TPConstantInt n)).

Definition TPPlus := (TPExpConst (TPConstantOp TPOperatorPlus)).
Definition TPMinus := (TPExpConst (TPConstantOp TPOperatorMinus)).
Definition TPMult := (TPExpConst (TPConstantOp TPOperatorMult)).
Definition TPDiv := (TPExpConst (TPConstantOp TPOperatorDiv)).
Definition TPMod := (TPExpConst (TPConstantOp TPOperatorMod)).
Definition TPLess := (TPExpConst (TPConstantOp TPOperatorLess)).
Definition TPLessEq := (TPExpConst (TPConstantOp TPOperatorLessEq)).
Definition TPGreater := (TPExpConst (TPConstantOp TPOperatorGreater)).
Definition TPGreaterEq := (TPExpConst (TPConstantOp TPOperatorGreaterEq)).
Definition TPEq := (TPExpConst (TPConstantOp TPOperatorEq)).
Definition TPNeq := (TPExpConst (TPConstantOp TPOperatorNeq)).

Definition TPExn := (TPExpConst TPConstantExn).
Definition TPHang := (TPExpConst TPConstantHang).

Definition TPConst c := TPExpConst c.
Definition TPId id := TPExpId id.
Definition TPApp a b := TPExpApp a b.
Definition TPAbstr id exp := TPExpAbstr id exp.
Definition TPIf exp1 exp2 exp3 := TPExpIf exp1 exp2 exp3.
Definition TPLet id exp1 exp2 := TPExpLet id exp1 exp2.
Definition TPRec id exp := TPExpRec id exp.

(* Boolean version of expression equality *)
Fixpoint TPExp_eq exp1 exp2 :=
  match exp1, exp2 with
    | TPExpConst c1, TPExpConst c2 => TPConstant_eq c1 c2
    | TPExpId (id1, n1), TPExpId (id2, n2) => andb (string_eq id1 id2) (beq_nat n1 n2)
    | TPExpApp exp11 exp12, TPExpApp exp21 exp22 =>
      andb (TPExp_eq exp11 exp21) (TPExp_eq exp12 exp22)
    | TPExpAbstr (id1, n1) exp1, TPExpAbstr (id2, n2) exp2 =>
      andb (string_eq id1 id2) (andb (beq_nat n1 n2) (TPExp_eq exp1 exp2))
    | TPExpIf e11 e12 e13, TPExpIf e21 e22 e23 =>
      andb (TPExp_eq e11 e21) (andb (TPExp_eq e12 e22) (TPExp_eq e13 e23))
    | TPExpLet (id1, n1) e11 e12, TPExpLet (id2, n2) e21 e22 =>
      andb (string_eq id1 id2) (andb (beq_nat n1 n2) (andb (TPExp_eq e11 e21) (TPExp_eq e12 e22)))
    | TPExpRec (id1, n1) e1, TPExpRec (id2, n2) e2 =>
      andb (string_eq id1 id2) (andb (beq_nat n1 n2) (TPExp_eq e1 e2))
    | _, _ => false
  end.

(* Consistency lemma *)
Lemma TPExp_eq_consist: forall exp1 exp2: TPExp, (TPExp_eq exp1 exp2) = true <-> exp1 = exp2.
Proof.
  intros exp1 exp2.
  split; intros H.
    (* => *)
    generalize dependent exp2.
    (* The following creates all possible cases of exp1 and exp2 and immediately
       solves all cases where the constructors of exp1 and exp2 are different. *)
    induction exp1; destruct exp2; intros H; try discriminate; simpl in H;
      try (induction id; now intuition); try induction id; try induction id0.
    (* Case: TPExpConst *)
    apply TPConstant_eq_consist in H; rewrite H; now reflexivity.
    (* Case: TPExpId *)
    apply andb_prop in H; destruct H; apply string_eq_consist in H.
    symmetry in H0; apply beq_nat_eq in H0; rewrite H; rewrite H0; now reflexivity.
    (* Case: TPExpApp *)
    apply andb_prop in H; destruct H as [H H'].
    rewrite IHexp1_1 with (exp2:=exp2_1).
    rewrite IHexp1_2 with (exp2:=exp2_2).
    now reflexivity. now exact H'. now exact H.
    (* Case: TPExpAbstr *)
    apply andb_prop in H. destruct H as [H H'].
    apply string_eq_consist in H; rewrite H.
    rewrite IHexp1 with (exp2:=exp2).
    apply andb_prop in H'.
    destruct H'; symmetry in H0; apply beq_nat_eq in H0; rewrite H0; now reflexivity.
    apply andb_prop in H'; destruct H' as [H0 H1]; now exact H1.
    (* Case: TPExpIf *)
    apply andb_prop in H; destruct H as [H H'];
    apply andb_prop in H'; destruct H' as [H' H''].
    rewrite IHexp1_1 with (exp2:=exp2_1).
    rewrite IHexp1_2 with (exp2:=exp2_2).
    rewrite IHexp1_3 with (exp2:=exp2_3).
    now reflexivity. now exact H''. now exact H'. now exact H.
    (* Case: TPExpLet *)
    apply andb_prop in H; destruct H as [H H'];
    apply andb_prop in H'; destruct H' as [H' H''].
    apply string_eq_consist in H; rewrite H.
    apply andb_prop in H''; destruct H''.
    rewrite IHexp1_1 with (exp2:=exp2_1).
    rewrite IHexp1_2 with (exp2:=exp2_2).
    symmetry in H'; apply beq_nat_eq in H'; rewrite H'; now reflexivity.
    now exact H1. now exact H0.
    (* Case: TPExpRec *)
    apply andb_prop in H; destruct H as [H H'].
    apply string_eq_consist in H; rewrite H.
    rewrite IHexp1 with (exp2:=exp2); apply andb_prop in H'; destruct H'.
    symmetry in H0; apply beq_nat_eq in H0; rewrite H0; now reflexivity.
    now exact H1.
    (* <= *)
    rewrite H; clear H; clear exp1; induction exp2; simpl; try induction id.
    (* Case TPExpConst *)
    now apply TPConstant_eq_reflex.
    (* Case TPExpId *)
    apply andb_true_intro; split.
    now apply string_eq_reflex.
    symmetry; now apply beq_nat_refl.
    (* Case TPExpApp *)
    apply andb_true_intro; split; now assumption.
    (* Case TPExpAbstr *)
    apply andb_true_intro; split.
    now apply string_eq_reflex.
    apply andb_true_intro; split.
    symmetry; now apply beq_nat_refl.
    now exact IHexp2.
    (* Case TPExpIf *)
    rewrite IHexp2_1; rewrite IHexp2_2; simpl; now exact IHexp2_3.
    (* Case TPExpLet *)
    rewrite string_eq_reflex; rewrite IHexp2_1; rewrite IHexp2_2; 
    simpl; apply andb_true_intro; split.
    symmetry; now apply beq_nat_refl.
    now reflexivity.
    (* Case TPExpRec *)
    rewrite string_eq_reflex; rewrite IHexp2; simpl; apply andb_true_intro; split; symmetry.
    now apply beq_nat_refl. now reflexivity.
Qed.

Inductive TPIsValue: TPExp -> Prop :=
| TPConstIsValue: forall c, TPIsValue (TPExpConst c)
| TPAbstrIsValue: forall id exp, TPIsValue (TPAbstr id exp)
| TPAppIsValue: forall op exp, TPIsValue exp -> TPIsValue (TPApp (TPOp op) exp).

Fixpoint TPIsValue_bool (exp : TPExp) : bool :=
  match exp with
    | TPExpConst _ => true
    | TPExpAbstr _ _ => true
    | TPExpApp (TPExpConst (TPConstantOp _)) exp => TPIsValue_bool exp
    | _ => false
  end.

Lemma TPIsValue_consist: forall exp, TPIsValue_bool exp = true <-> TPIsValue exp.
Proof.
  intros exp. split; intros H.
  (* => *)
    induction exp; try ((contradict H; discriminate) || constructor).
    (* Case exp: TPExpApp *)
    destruct exp1; simpl in H; try (contradict H; discriminate).
      destruct c; try (contradict H; discriminate).
      constructor. apply IHexp2. exact H.
  (* <= *)
    induction exp; inversion H; simpl; try reflexivity.
    (* Case: TPOp *)
    apply IHexp2. exact H1.
Qed.

Lemma TPIsValue_cases: forall exp, TPIsValue exp <-> (exists c, exp = TPConst c) \/ (exists id, exists exp', exp = TPAbstr id exp') \/ (exists op, exists exp', (exp = TPApp (TPOp op) exp' /\ TPIsValue exp')).
Proof.
  intros exp. split; intros H.
  (* => *)
  inversion H.
    left. exists c. reflexivity.
    right. left. exists id. exists exp0. reflexivity.
    right. right. exists op. exists exp0. split.
      reflexivity.
      exact H0.
    (* <= *)
    destruct H as [[c H] | [[id [exp' H]] | [op [exp' [H H']]]]].
      rewrite H. constructor.
      rewrite H. constructor.
      rewrite H. constructor. exact H'.
Qed.

End TPSyntaxExpressions.

