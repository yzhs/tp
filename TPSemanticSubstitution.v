Module TPSemanticSubstitution.

Load TPSemanticFreeVariables.
Export TPSemanticFreeVariables.

(* The function that implements alpha conversion *)
Parameter rename_function: TPExp -> TPExp -> TPIdentifier -> TPIdentifier.
Axiom rename_function_prop: forall exp1 exp2 id id', id' = rename_function exp1 exp2 id -> id <> id' /\ TPIsNotFreeIn id' exp1 /\ TPIsNotFreeIn id' exp2.

Inductive TPSubstitutesInto: TPExp -> TPIdentifier -> TPExp -> TPExp -> Prop := 
| subst_const: forall id c sexp, 
               TPSubstitutesInto (TPExpConst c) id sexp (TPExpConst c)
| subst_id_eq: forall id sexp,
               TPSubstitutesInto (TPId id) id sexp sexp
| subst_id_neq: forall id id' sexp,
                id <> id' -> 
                TPSubstitutesInto (TPId id') id sexp (TPId id')
| subst_if: forall id e1 e2 e3 e1' e2' e3' sexp,
            TPSubstitutesInto e1 id sexp e1' -> 
            TPSubstitutesInto e2 id sexp e2' -> 
            TPSubstitutesInto e3 id sexp e3' -> 
            TPSubstitutesInto (TPIf e1 e2 e3) id sexp (TPIf e1' e2' e3')
| subst_app: forall id e1 e2 e1' e2' sexp,
             TPSubstitutesInto e1 id sexp e1' -> 
             TPSubstitutesInto e2 id sexp e2' -> 
             TPSubstitutesInto (TPExpApp e1 e2) id sexp (TPExpApp e1' e2')
| subst_abstr_eq: forall id e sexp,
                  TPSubstitutesInto (TPExpAbstr id e) id sexp (TPExpAbstr id e)
| subst_abstr_neq: forall id id' id'' e e' e'' sexp,
                   id <> id' ->
                   id'' = rename_function sexp (TPExpAbstr id' e) id ->
                   TPSubstitutesInto e id' (TPId id'') e' ->
                   TPSubstitutesInto e' id sexp e'' ->
                   TPSubstitutesInto (TPExpAbstr id' e) id sexp (TPExpAbstr id'' e'')
| subst_let_eq: forall id e1 e2 e1' sexp,
                TPSubstitutesInto e1 id sexp e1' -> 
                TPSubstitutesInto (TPExpLet id e1 e2) id sexp (TPExpLet id e1' e2)
| subst_let_neq: forall id id' id'' e1 e2 e1' e2' e2'' sexp,
                 id <> id' -> 
                 id'' = rename_function sexp (TPExpLet id' e1 e2) id ->
                 TPSubstitutesInto e1 id sexp e1' ->
                 TPSubstitutesInto e2 id' (TPId id'') e2' ->
                 TPSubstitutesInto e2' id sexp e2'' -> 
                 TPSubstitutesInto (TPExpLet id' e1 e2) id sexp (TPExpLet id'' e1' e2'')
| subst_rec_eq: forall id e sexp,
                TPSubstitutesInto (TPExpRec id e) id sexp (TPExpRec id e)
| subst_rec_neq: forall id id' id'' e e' e'' sexp,
                 id <> id' ->
                 id'' = rename_function sexp (TPExpRec id' e) id ->
                 TPSubstitutesInto e id' (TPId id'') e' ->
                 TPSubstitutesInto e' id sexp e'' ->
                 TPSubstitutesInto (TPExpRec id' e) id sexp (TPExpRec id'' e'').

Lemma chained_subst: forall id id' sexp sexp' exp exp' exp'' exp''', id <> id' -> TPSubstitutesInto exp id sexp exp' -> TPSubstitutesInto exp' id' sexp' exp'' -> TPSubstitutesInto exp id' sexp' exp''' -> TPSubstitutesInto exp''' id sexp exp''.
Proof.
  intros id id' sexp sexp' exp exp' exp'' exp''' Hexp1 Hexp' Hexp2 Hexp'''.
Admitted.

Lemma substitution_is_defined: forall exp id sexp, exists exp', TPSubstitutesInto exp id sexp exp'.
Proof.
  intros exp.
  induction exp; intros id' sexp.
    (* TPConst *)
    exists (TPExpConst c). constructor.
    (* TPId *)
    case_eq (ident_eq id' id); intros Hid.
      apply ident_eq_consist in Hid. exists sexp. rewrite Hid. constructor.
      apply ident_eq_consist_conv in Hid. exists (TPExpId id). constructor. assumption.
    (* TPApp *)
      specialize IHexp1 with (id:=id')(sexp:=sexp). destruct IHexp1 as [exp1' Hexp1].
      specialize IHexp2 with (id:=id')(sexp:=sexp). destruct IHexp2 as [exp2' Hexp2].
      exists (TPExpApp exp1' exp2'). constructor; assumption.
    (* TPAbstr *)
    case_eq (ident_eq id' id); intros Hid.
      apply ident_eq_consist in Hid. exists (TPExpAbstr id exp). rewrite Hid. constructor.
      apply ident_eq_consist_conv in Hid. 
      assert (exists exp' : TPExp, TPSubstitutesInto exp id' sexp exp').
        apply IHexp.
      destruct H as [exp0 Hexp0].
      assert (exists exp', TPSubstitutesInto exp id  (TPId (rename_function sexp (TPExpAbstr id exp) id')) exp').
        apply IHexp.
      destruct H as [exp' Hexp'].
      assert (exists exp'', TPSubstitutesInto exp id' sexp exp'').
        apply IHexp.
      destruct H as [exp'' Hexp''].
      exists (TPExpAbstr (rename_function sexp (TPExpAbstr id exp) id') exp'').
      apply subst_abstr_neq with (e':=exp').
        assumption.
        reflexivity.
        assumption.
        apply chained_subst with (id':=id)(sexp':=(TPId (rename_function sexp (TPExpAbstr id exp) id')))(exp:=exp)(exp':=exp0).
          assumption.
          assumption.
          admit.
          assumption.
    (* TPIf *)
      specialize IHexp1 with (id:=id')(sexp:=sexp). destruct IHexp1 as [exp1' Hexp1].
      specialize IHexp2 with (id:=id')(sexp:=sexp). destruct IHexp2 as [exp2' Hexp2].
      specialize IHexp3 with (id:=id')(sexp:=sexp). destruct IHexp3 as [exp3' Hexp3].
      exists (TPExpIf exp1' exp2' exp3').
      constructor; assumption.
    (* TPLet *)
    admit.
    (* TPRec *)
    admit.
Qed.

Lemma substitution_is_deterministic: forall exp id v exp1 exp2, TPSubstitutesInto exp id v exp1 -> TPSubstitutesInto exp id v exp2 -> exp1 = exp2.
Proof.
  intros exp id v exp1 exp2 Hexp1.
  generalize dependent exp2.
  induction Hexp1; intros exp2 Hexp2; inversion Hexp2; try (now reflexivity).
    (**)
    contradict H0. reflexivity.
    (**)
    contradict H. rewrite H0. reflexivity.
    (**)
    rewrite IHHexp1_1 with (exp2:=e1'0).
    rewrite IHHexp1_2 with (exp2:=e2'0).
    rewrite IHHexp1_3 with (exp2:=e3'0).
    reflexivity.
    assumption.
    assumption.
    assumption.
    (**)
    rewrite IHHexp1_1 with (exp2:=e1'0).
    rewrite IHHexp1_2 with (exp2:=e2'0).
    reflexivity.
    assumption.
    assumption.
    (**)
    contradict H1. reflexivity.
    (**)
    contradict H. rewrite H1. reflexivity.
    (**)
    clear H6 id0. clear H1 id'0. clear H2 e0. clear H7 sexp0.
    rewrite <- H8 in Hexp2. clear H8 exp2. clear H.
    rewrite <- H4 in H0.
    rewrite IHHexp1_2 with (exp2:=e''0).
      rewrite H0. reflexivity.
      rewrite IHHexp1_1 with (exp2:=e'0).
        assumption.
        rewrite H0. assumption.
    (**)
    rewrite IHHexp1 with (exp2:=e1'0). reflexivity. assumption.
    (**)
    contradict H2. reflexivity.
    (**)
    contradict H. symmetry. assumption.
    (**)
    clear H8 sexp0 H7 id0 H3 e3 H2 e0 H1 id'0.
    rewrite <- H5 in H0. rewrite H0.
    rewrite IHHexp1_1 with (exp2:=e1'0).
    rewrite IHHexp1_3 with (exp2:=e2''0).
    reflexivity.
    rewrite IHHexp1_2 with (exp2:=e2'0).
      assumption.
      rewrite H0. assumption.
    assumption.
    (**)
    contradict H1. reflexivity.
    (**)
    contradict H. symmetry. assumption.
    (**)
    rewrite <- H4 in H0. rewrite H0.
    rewrite IHHexp1_2 with (exp2:=e''0).
      reflexivity.
      rewrite IHHexp1_1 with (exp2:=e'0).
        assumption.
        rewrite H0. assumption.
Qed.

Lemma unfree_id_in_subst_exp: forall exp exp' sexp id, TPIsNotFreeIn id sexp -> TPSubstitutesInto exp id sexp exp' -> TPIsNotFreeIn id exp'.
Proof.
Admitted.

Lemma subst_doesnt_free_different_ids: forall exp exp' sexp id id', id <> id' -> TPIsNotFreeIn id' exp -> TPSubstitutesInto exp id sexp exp' -> TPIsNotFreeIn id' exp'.
Proof.
Admitted.

Lemma subst_doesnt_unfree_different_ids: forall exp exp' sexp id id', id <> id' -> TPIsFreeIn id' exp -> TPSubstitutesInto exp id sexp exp' -> TPIsFreeIn id' exp'.
Proof.
  intros exp exp' sexp id id' Hid Hfree Hsubst.
  generalize dependent id'.
  induction Hsubst; intros id0 Hid Hfree.
    (**)
    assumption.
    (**)
    inversion Hfree. contradict Hid. symmetry. assumption. 
    (**)
    assumption.
    (**)
    constructor. inversion Hfree. destruct H1 as [H1 | [H1 | H1]].
      left. apply IHHsubst1; assumption.
      right. left. apply IHHsubst2; assumption.
      right. right. apply IHHsubst3; assumption.
    (**)
    constructor. inversion Hfree. destruct H1.
      left. apply IHHsubst1; assumption.
      right. apply IHHsubst2; assumption.
    (**)
    inversion_clear Hfree. constructor; assumption.
    (**)
    inversion_clear Hfree. apply rename_function_prop in H0. destruct H0 as [H0_1 [H0_2 H0_3]].
    admit.
    (**)
    inversion_clear Hfree. constructor. destruct H.
      left. assumption.
      right. apply IHHsubst; assumption.
    (**)
    apply rename_function_prop in H0. destruct H0 as [H0_1 [H0_2 H0_3]].
    inversion_clear H0_3. 
    inversion_clear Hfree. constructor. destruct H0.
      admit. admit.
    (**)
    inversion_clear Hfree. constructor; assumption.
    (**)
    apply rename_function_prop in H0. destruct H0 as [H0_1 [H0_2 H0_3]].
    inversion_clear Hfree. admit.
Qed.

Lemma free_id_in_subst_exp: forall exp exp' sexp id, TPIsFreeIn id sexp -> TPSubstitutesInto exp id sexp exp' -> TPIsFreeIn id exp'.
Proof.
Admitted.

End TPSemanticSubstitution.