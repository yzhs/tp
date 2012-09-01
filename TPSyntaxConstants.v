Module TPSyntaxConstants.

Require Export ZArith.

Load TPSyntaxOperators.
Export TPSyntaxOperators.

Inductive TPConstant :=
 | TPConstantUnit
 | TPConstantBool (b : bool)
 | TPConstantInt (n : Z)
 | TPConstantOp (op : TPOperator)
 | TPConstantExn
 | TPConstantHang.

(* Boolean version of constant equality *)
Fixpoint TPConstant_eq c1 c2 :=
  match c1, c2 with
    | TPConstantUnit, TPConstantUnit => true
    | TPConstantBool b1, TPConstantBool b2 => bool_eq b1 b2
    | TPConstantInt n1, TPConstantInt n2 => Zeq_bool n1 n2
    | TPConstantOp op1, TPConstantOp op2 => TPOperator_eq op1 op2
    | TPConstantExn, TPConstantExn => true
    | TPConstantHang, TPConstantHang => true
    | _, _ => false
  end.

(* Consistency lemma *)
Lemma TPConstant_eq_consist: forall c1 c2: TPConstant, TPConstant_eq c1 c2 = true <-> c1 = c2.
Proof.
  intros c1 c2.
  split; intros H.
    (* => *)
    destruct c1; destruct c2; simpl in H; try (discriminate || reflexivity).
    apply bool_eq_ok in H; rewrite H; reflexivity.
    apply Zeq_bool_eq in H; rewrite H; reflexivity.
    apply TPOperator_eq_consist in H; rewrite H; reflexivity.
    (* <= *)
    destruct c1; destruct c2; simpl in H; simpl; try discriminate; try reflexivity.
    inversion H. destruct b0; reflexivity.
    inversion H. apply Zeq_is_eq_bool. reflexivity.
    inversion H. apply TPOperator_eq_consist. reflexivity.
Qed.

Lemma TPConstant_eq_reflex: forall c: TPConstant, TPConstant_eq c c = true.
Proof.
  intros c.
  induction c; simpl.
    (* Case TPunit*)
    now reflexivity.
    (* Case TPbool*)
    destruct b; simpl; now reflexivity.
    (* Case TPint*)
    induction n. compute. reflexivity.
    induction p; auto.
    induction p; auto.
    (* Case TPop*)
    now apply TPOperator_eq_reflex.
    (* Case TPexn*)
    now reflexivity.
    (* Case TPhang*)
    now reflexivity.
Qed.

End TPSyntaxConstants.