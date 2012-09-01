Module TPSyntaxOperators.

Inductive TPOperator :=
 | TPOperatorPlus
 | TPOperatorMinus
 | TPOperatorMult
 | TPOperatorDiv
 | TPOperatorMod
 | TPOperatorLess
 | TPOperatorLessEq
 | TPOperatorGreater
 | TPOperatorGreaterEq
 | TPOperatorEq
 | TPOperatorNeq.

(* Boolean version of operator equality *)
Definition TPOperator_eq op1 op2 :=
  match op1, op2 with
    | TPOperatorPlus, TPOperatorPlus => true
    | TPOperatorMinus, TPOperatorMinus => true
    | TPOperatorMult, TPOperatorMult => true
    | TPOperatorDiv, TPOperatorDiv => true
    | TPOperatorMod, TPOperatorMod => true
    | TPOperatorLess, TPOperatorLess => true
    | TPOperatorLessEq, TPOperatorLessEq => true
    | TPOperatorGreater, TPOperatorGreater => true
    | TPOperatorGreaterEq, TPOperatorGreaterEq => true
    | TPOperatorEq, TPOperatorEq => true
    | TPOperatorNeq, TPOperatorNeq => true
    | _, _ => false
  end.

(* Consistency lemma *)
Lemma TPOperator_eq_consist: forall op1 op2, TPOperator_eq op1 op2 = true <-> op1 = op2.
Proof.
  intros op1 op2.
  split; intros H.
    (* => *)
    destruct op1; destruct op2; (discriminate || reflexivity).
    (* <= *)
    destruct op1; destruct op2; simpl; solve [discriminate | reflexivity].
Qed.

Lemma TPOperator_eq_reflex: forall op, TPOperator_eq op op = true.
Proof.
  intros op.
  destruct op; simpl; reflexivity.
Qed.

End TPSyntaxOperators.