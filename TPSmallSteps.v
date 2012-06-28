Module TPSmallSteps.

Load TPSyntax.
Export TPSyntax.

Open Scope Z_scope.

Definition eval op n1 n2 :=
  match op,  n1, n2 with
    | TPplus,     TPconst (TPint n), TPconst (TPint n') => TPconst (TPint (n + n'))
    | TPminus,    TPconst (TPint n), TPconst (TPint n') => TPconst (TPint (n - n'))
    | TPmult,     TPconst (TPint n), TPconst (TPint n') => TPconst (TPint (n * n'))
    | TPdiv,      TPconst (TPint n), TPconst (TPint n') => TPconst (TPint (n / n'))
    | TPmod,      TPconst (TPint n), TPconst (TPint n') => TPconst (TPint (n mod n'))
    | TPless,     TPconst (TPint n), TPconst (TPint n') => TPconst (TPbool (Zlt_bool n n'))
    | TPlesseq,   TPconst (TPint n), TPconst (TPint n') => TPconst (TPbool (Zle_bool n n'))
    | TPgreater,  TPconst (TPint n), TPconst (TPint n') => TPconst (TPbool (Zgt_bool n n'))
    | TPgreatereq,TPconst (TPint n), TPconst (TPint n') => TPconst (TPbool (Zge_bool n n'))
    | TPeq,       TPconst (TPint n), TPconst (TPint n') => TPconst (TPbool (Zeq_bool n n'))
    | TPneq,      TPconst (TPint n), TPconst (TPint n') => TPconst (TPbool (Zneq_bool n n'))
    | _, _, _ => TPconst TPhang
  end.

(* TODO: rewrite using sets (ListSet?) *)
Fixpoint free exp :=
  match exp with
    | TPconst _ => nil
    | TPid id => id :: nil
    | TPapp exp1 exp2 => app (free exp1) (free exp2)
    | TPif exp1 exp2 exp3 => app (free exp1) (app (free exp2) (free exp3))
    | TPabst id exp => filter (string_neq id) (free exp)
    | TPlet id e1 e2 => app (filter (string_neq id) (free e2)) (free e1)
    | TPrec id exp => filter (string_neq id) (free exp)
  end.

(*
Fixpoint new_id free_ids id :=

Fixpoint subst free_ids e e' id :=
  match e with
    | TPconst c => c
    | TPid id' => if string_eq id' id then e' else id'
    | TPabst id' e => if string_eq id' id then e else
      let id'' := new_id free_ids id' in TPabst id'' (subst (id'' :: free_ids) (subst free_ids e' (TPid id'') id) e' id)
    | _ => TPconst TPunit
  end.
*)

Fixpoint subst e e' id :=
  match e with
    | TPconst c => e
    | TPid id' => if string_eq id' id then e' else TPid id'
    | TPif e1 e2 e3 => TPif (subst e1 e' id) (subst e2 e' id) (subst e3 e' id)
    | TPapp e1 e2 => TPapp (subst e1 e' id) (subst e2 e' id)
    | TPabst id' e => if string_eq id' id then e else TPabst id' (subst e e' id)
    | TPlet id' e1 e2 => TPlet id' (subst e1 e' id) (if string_eq id id' then e2 else subst e2 e' id)
    | TPrec id' e => if string_eq id' id then e else TPrec id' (subst e e' id)
  end.

Fixpoint small_step exp :=
  match exp with
    | TPapp (TPabst id e1) e2 =>
      if TPisvalue e2
        then subst e1 e2 id                        (* BETA-V *)
        else TPapp (small_step e1) e2              (* APP-LEFT *)
    | TPapp e1 exp2 =>
      match e1 with
        | TPapp (TPconst (TPop op)) exp1 =>
          if TPisvalue exp1 then
            if TPisvalue exp2 then
              eval op exp1 exp2                    (* OP *)
              else TPapp e1 (small_step exp2)      (* APP-RIGHT *)
            else TPapp (small_step e1) exp2        (* APP-LEFT *)
        | _ => if TPisvalue exp2
          then TPapp (small_step e1) exp2
          else TPapp e1 (small_step exp2)
      end
    | TPif (TPconst (TPbool true)) e2 e3 => e2     (* COND-TRUE *)
    | TPif (TPconst (TPbool false)) e2 e3 => e3    (* COND-FALSE *)
    | TPif e1 e2 e3 => TPif (small_step e1) e2 e3  (* COND-EVAL *)
    | TPlet id e1 e2 =>
      if TPisvalue e1 then
        subst e2 e1 id                             (* LET-EXEC *)
        else TPlet id (small_step e1) e2           (* LET-EVAL *)
    | TPrec id e => subst e (TPrec id e) id        (* UNFOLD *)
 (* | _ => if TPisvalue exp then exp else TPconst TPhang *)
    | _ => exp
 end.

(*Compute small_step (small_step (TPapp (TPabst "x" (TPapp (TPapp (TPconst( TPop TPplus)) (TPid "x")) (TPconst (TPint 1)))) (TPconst (TPint 2)))).*)

Theorem op_rule_implemented: forall exp op exp1 exp2, exp = (TPapp (TPapp (TPconst(TPop op)) exp1) exp2) /\ andb (TPisvalue exp1) (TPisvalue exp2) = true -> small_step exp = eval op exp1 exp2.
Proof.
  intros exp op exp1 exp2 H.
  destruct H as [H H']. apply andb_prop in H'. destruct H' as [H' H''].
  rewrite H.
  simpl. rewrite H'. rewrite H''.
  reflexivity.
Qed.

Theorem beta_v_rule_implemented: forall exp exp' id exp'', (exp = TPapp (TPabst id exp') exp'' /\ TPisvalue exp'' = true) -> small_step exp = subst exp' exp'' id.
Proof.
  intros exp exp' id exp'' H. destruct H as [H H'].
  apply TPisvalue_consist in H'.
  destruct H' as [[x H0] | [[s [x H0]] | [x [ x0 [H0 H1]]]]];
  rewrite H0; rewrite H0 in H; clear H0; clear exp''; rewrite H; clear H; simpl.
    reflexivity.
    reflexivity.
    rewrite H1. reflexivity.
Qed.

Theorem app_left_rule_implemented: forall exp1 exp2, small_step exp1 = exp2 -> forall exp3, small_step (TPapp exp1 exp3) = (TPapp exp2 exp3).
Proof.
  (* TODO *)
Admitted.

Theorem app_right_rule_implemented: forall exp1 exp2, small_step exp1 = exp2 -> forall v, TPisvalue v = true -> small_step (TPapp v exp1) = (TPapp v exp2).
Proof.
  (* TODO *)
Admitted.

Theorem cond_eval_rule_implemented: forall exp exp', (small_step exp = exp' /\ exp <> (TPconst (TPbool true)) /\ exp <> (TPconst (TPbool false))) -> forall exp1 exp2, small_step (TPif exp exp1 exp2) = TPif exp' exp1 exp2.
Proof.
  intros exp exp' H exp1 exp2.
  destruct H as [H H'].
  destruct H' as [Hnot_true Hnot_false].

  rewrite <- H. clear H. clear exp'.
  induction exp; simpl; try reflexivity.
    (* Case: TPconst *)
    destruct c; compute; try reflexivity.
      (* Case: TPbool *)
      destruct b.
      contradict Hnot_true. reflexivity.
      contradict Hnot_false. reflexivity.
Qed.

Theorem cond_true_rule_implemented: forall exp1 exp2, small_step (TPif (TPconst (TPbool true)) exp1 exp2) = exp1.
Proof.
  intros exp1 exp2. simpl. reflexivity.
Qed.

Theorem cond_false_rule_implemented: forall exp1 exp2, small_step (TPif (TPconst (TPbool false)) exp1 exp2) = exp2.
Proof.
  intros exp1 exp2. simpl. reflexivity.
Qed.

Theorem let_eval_rule_implemented: forall exp exp', small_step exp = exp' -> forall id exp1, small_step (TPlet id exp exp1) = TPlet id exp' exp1.
Proof.
  (* TODO *)
Admitted.

Theorem let_exec_rule_implemented: forall id v, TPisvalue v = true -> forall exp, small_step (TPlet id v exp) = subst exp v id.
Proof.
  (* TODO *)
Admitted.

End TPSmallSteps.
