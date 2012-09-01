Module TPSemanticFreeVariables.

Load TPSyntaxExpressions.
Export TPSyntaxExpressions.

Load TPSyntaxIdentifiers.
Export TPSyntaxIdentifiers.

Inductive TPIsFreeIn: TPIdentifier -> TPExp -> Prop :=
| free_id: forall id, TPIsFreeIn id (TPExpId id)
| free_app: forall id exp1 exp2, (TPIsFreeIn id exp1 \/ TPIsFreeIn id exp2) -> TPIsFreeIn id (TPExpApp exp1 exp2)
| free_if: forall id exp1 exp2 exp3, (TPIsFreeIn id exp1 \/ TPIsFreeIn id exp2 \/ TPIsFreeIn id exp3) -> TPIsFreeIn id (TPExpIf exp1 exp2 exp3)
| free_abstr: forall id id' exp, id <> id' ->  TPIsFreeIn id exp -> TPIsFreeIn id (TPExpAbstr id' exp)
| free_let: forall id id' exp' exp, (id <> id' /\ TPIsFreeIn id exp) \/ TPIsFreeIn id exp' -> TPIsFreeIn id (TPExpLet id' exp' exp)
| free_rec: forall id id' exp, id <> id' -> TPIsFreeIn id exp -> TPIsFreeIn id (TPExpRec id' exp).

Inductive TPIsNotFreeIn: TPIdentifier -> TPExp -> Prop :=
| notfree_const: forall id c, TPIsNotFreeIn id (TPExpConst c)
| notfree_id: forall id id', id <> id' -> TPIsNotFreeIn id (TPExpId id')
| notfree_app: forall id exp1 exp2, (TPIsNotFreeIn id exp1 /\ TPIsNotFreeIn id exp2) -> TPIsNotFreeIn id (TPExpApp exp1 exp2)
| notfree_if: forall id exp1 exp2 exp3, (TPIsNotFreeIn id exp1 /\ TPIsNotFreeIn id exp2 /\ TPIsNotFreeIn id exp3) -> TPIsNotFreeIn id (TPExpIf exp1 exp2 exp3)
| notfree_abstr_eq: forall id exp, TPIsNotFreeIn id (TPExpAbstr id exp)
| notfree_abstr_neq: forall id id' exp, id <> id' -> TPIsNotFreeIn id exp -> TPIsNotFreeIn id (TPExpAbstr id' exp)
| notfree_let: forall id id' exp' exp, ((TPIsNotFreeIn id exp /\ id <> id') \/ id = id') -> TPIsNotFreeIn id exp' -> TPIsNotFreeIn id (TPExpLet id' exp' exp)
| notfree_rec_eq: forall id exp, TPIsNotFreeIn id (TPExpRec id exp)
| notfree_rec_neq: forall id id' exp, id <> id' -> TPIsNotFreeIn id exp -> TPIsNotFreeIn id (TPExpRec id' exp).

Lemma TPIsNotFreeIn_consist: forall exp id, ~ TPIsFreeIn id exp <-> TPIsNotFreeIn id exp.
Proof.
  intros exp id. split; intros H.
  (* => *)
  generalize dependent id.
  induction exp; intros id' H.
    (**)
    constructor.
    (**)
    constructor. compute in H. intros H'. apply H. rewrite H'. constructor.
    (**)
    constructor. compute in H. split.
      apply IHexp1. intros H'. apply H. constructor. left. assumption. 
      apply IHexp2. intros H'. apply H. constructor. right. assumption.
    (**)
    case_eq (ident_eq id' id); intros Hid.
      apply ident_eq_consist in Hid. rewrite Hid. constructor.
      apply ident_eq_consist_conv in Hid. constructor.
        assumption. 
        compute in H. apply IHexp. intros H'. apply H. constructor.
          assumption.
          assumption.
    (**)
    constructor. compute in H. split.
      apply IHexp1. intros H'. apply H. constructor. left. assumption.
      split.
        apply IHexp2. intros H'. apply H. constructor. right. left. assumption.
        apply IHexp3. intros H'. apply H. constructor. right. right. assumption.
    (**)
    compute in H. constructor. case_eq (ident_eq id' id); intros Hid.
      apply ident_eq_consist in Hid. right. assumption.
      apply ident_eq_consist_conv in Hid. left. split. 
        apply IHexp2. intros H'. apply H. constructor. left. split; assumption.
        assumption.
    (**)
    compute in H. case_eq (ident_eq id' id); intros Hid.
      apply ident_eq_consist in Hid. rewrite Hid. apply IHexp1. intros H'. apply H. constructor. right. rewrite Hid. assumption.
      apply ident_eq_consist_conv in Hid. apply IHexp1. intros H'. apply H. constructor. right. assumption. 
    (**)
    compute in H. case_eq (ident_eq id' id); intros Hid. 
      apply ident_eq_consist in Hid. rewrite Hid. constructor.
      apply ident_eq_consist_conv in Hid. constructor.
        assumption.
        apply IHexp. intros H'. apply H. constructor; assumption.
  (* <= *)
  generalize dependent id. induction exp; intros id' H H'.
    (**)
    inversion_clear H. inversion_clear H'.
    (**)
    inversion_clear H. inversion H'. contradiction.
    (**)
    inversion_clear H. inversion_clear H'. destruct H0. destruct H.
      contradict H. apply IHexp1. assumption.
      contradict H. apply IHexp2. assumption.
    (**)
    inversion H.
      inversion_clear H'. contradict H1. assumption.
      inversion_clear H'. specialize IHexp with (id:=id'). destruct IHexp; assumption.
    (**)
    inversion_clear H. inversion_clear H'. destruct H0. destruct H1. destruct H as [H | [H | H]].
      contradict H. apply IHexp1. assumption.
      contradict H. apply IHexp2. assumption.
      contradict H. apply IHexp3. assumption.
    (**)
    inversion_clear H'. destruct H0 as [[H0 H1] | H0].
      inversion_clear H. destruct H2 as [H2 | H2].
        specialize IHexp2 with (id:=id'). destruct H2 as [H2_1 H2_2]. destruct IHexp2; assumption.
        contradict H0. assumption.
      inversion_clear H. destruct H1 as [H1 | H1];
        specialize IHexp1 with (id:=id'); destruct IHexp1; assumption.
    (**)
    inversion H.
      inversion_clear H'. contradict H1. assumption.
      inversion_clear H'. specialize IHexp with (id:=id'). destruct IHexp. assumption. assumption.
Qed.

Lemma TPIsFreeIn_consist: forall exp id, ~ TPIsNotFreeIn id exp <-> TPIsFreeIn id exp.
Admitted.

End TPSemanticFreeVariables.