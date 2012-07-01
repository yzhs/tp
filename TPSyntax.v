Module TPSyntax.

Require Export ZArith.
Require Export List.
Require Export String.
Require Import Ascii.

Open Scope Z_scope.

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

Inductive TPConstant :=
 | TPConstantUnit
 | TPConstantBool (b : bool)
 | TPConstantInt (n : Z)
 | TPConstantOp (op : TPOperator)
 | TPConstantExn
 | TPConstantHang.

Inductive TPExp :=
 | TPExpConst (c : TPConstant)
 | TPExpId (id : string)
 | TPExpApp (a b : TPExp)
 | TPExpAbstr (id : string) (exp : TPExp)
 | TPExpIf (exp1 exp2 exp3 : TPExp)
 | TPExpLet (id : string) (exp1 exp2 : TPExp)
 | TPExpRec (id : string) (exp : TPExp).

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


Fixpoint TPIsValue (exp : TPExp) : bool :=
  match exp with
    | TPExpConst _ => true
    | TPExpAbstr _ _ => true
    | TPExpApp (TPExpConst (TPConstantOp _)) exp => TPIsValue exp
    | _ => false
  end.

Lemma TPIsValue_consist: forall exp, TPIsValue exp = true <-> (exists c, exp = TPConst c) \/ (exists id, exists exp', exp = TPAbstr id exp') \/ (exists op, exists exp', (exp = TPApp (TPOp op) exp' /\ TPIsValue exp' = true)).
Proof.
  intros exp. split; intros H.
  (* => *)
  induction exp; try (contradict H; discriminate).
  (* Case exp: TPconst *)
  left. exists c. now reflexivity.
  (* Case exp: TPApp *)
  destruct exp1; simpl in H; try (contradict H; discriminate).
    (* Case exp1: TPconst *)
    destruct c; try (contradict H; discriminate).
      destruct IHexp2.
        (* Condition: TPisvalue exp2 = true *)
        exact H.
        (* Case: First exist is true *)
        destruct H0. right. right. exists op. exists exp2. split. reflexivity. rewrite H0.  simpl. reflexivity.
        (* Case: Second or third exist is true *)
        destruct H0. 
        (* Case: Second exist is true *)
        destruct H0. destruct H0. right. right. exists op. exists exp2. split. reflexivity. rewrite H0.  simpl. reflexivity.
        (* Case: Third exist is true *)
        destruct H0. destruct H0. destruct H0. right. right. exists op. exists exp2. split. reflexivity. rewrite H0.  simpl. exact H1.
  (* Case exp: TPabst *)
  right. left. exists id. exists exp. reflexivity.
  (* <= *)
  destruct H.
    (* Case: First exist is true *)
    destruct H. rewrite H. compute. now reflexivity.
    (* Case: Second or third exist is true *)
    destruct H.
    (* Case: Second exist is true *)
    destruct H. destruct H. rewrite H. compute. now reflexivity.
    (* Case: Third exist is true *)
    destruct H. destruct H. destruct H. rewrite H. simpl. exact H0.
Qed.

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

(* Very ugly boolean version of ascii equality *)
Definition ascii_eq a1 a2 := match a1, a2 with
| Ascii b1 b2 b3 b4 b5 b6 b7 b8, Ascii b1' b2' b3' b4' b5' b6' b7' b8'
  => (bool_eq b1 b1' && bool_eq b2 b2' && bool_eq b3 b3' &&
      bool_eq b4 b4' && bool_eq b5 b5' && bool_eq b6 b6' &&
      bool_eq b7 b7' && bool_eq b8 b8')%bool
end.

(* Consistency Lemma *)
Lemma ascii_eq_consist: forall a1 a2: ascii, ascii_eq a1 a2 = true <-> a1 = a2.
Proof.
  intros a1 a2.
  split; intros H.
  (* => *)
    destruct a1 as [b1 b2 b3 b4 b5 b6 b7 b8].
    destruct a2 as [b1' b2' b3' b4' b5' b6' b7' b8'].
    simpl in H.
    repeat (apply andb_prop in H; destruct H).
    apply bool_eq_ok in H; rewrite H.
    apply bool_eq_ok in H0; rewrite H0.
    apply bool_eq_ok in H1; rewrite H1.
    apply bool_eq_ok in H2; rewrite H2.
    apply bool_eq_ok in H3; rewrite H3.
    apply bool_eq_ok in H4; rewrite H4.
    apply bool_eq_ok in H5; rewrite H5.
    apply bool_eq_ok in H6; rewrite H6.
    reflexivity.
  (* <= *)
    rewrite <- H. destruct a1 as [b1 b2 b3 b4 b5 b6 b7 b8]; simpl.
    destruct b1; simpl;
    destruct b2; simpl;
    destruct b3; simpl;
    destruct b4; simpl;
    destruct b5; simpl;
    destruct b6; simpl;
    destruct b7; simpl;
    destruct b8; simpl; reflexivity.
Qed.

Lemma ascii_eq_reflex: forall a: ascii, ascii_eq a a = true.
Proof.
  intros. destruct a as [b1 b2 b3 b4 b5 b6 b7 b8].
  destruct b1; simpl;
  destruct b2; simpl;
  destruct b3; simpl;
  destruct b4; simpl;
  destruct b5; simpl;
  destruct b6; simpl;
  destruct b7; simpl;
  destruct b8; simpl; reflexivity.
Qed.

Fixpoint string_eq s1 s2 := match s1, s2 with
| EmptyString, EmptyString => true
| String a1 s1', String a2 s2' => if ascii_eq a1 a2 then string_eq s1' s2' else false
| _, _ => false
end.

(* Consistency Lemma *)
Lemma string_eq_consist: forall s1 s2: string, string_eq s1 s2 = true <-> s1 = s2.
Proof.
  split; intros H.
    generalize dependent s2.
    (* => *)
    induction s1; destruct s2; intros H; simpl in H.
      (* Base case *)
      now reflexivity.
      (* Base case *)
      contradict H. now discriminate.
      (* Step *)
      contradict H. now discriminate.
      (* Step *)
        case_eq (ascii_eq a a0); intros; rewrite H0 in H.
        (* Case: true *)
        apply ascii_eq_consist in H0. rewrite H0.
        specialize IHs1 with (s2:=s2). rewrite IHs1.
        reflexivity. exact H.
        (* Case: false *)
        contradict H. discriminate.
   (* <= *)
    rewrite H. clear H. clear s1.
    induction s2; simpl.
      (* Base case *)
      reflexivity.
      (* Step *)
      rewrite ascii_eq_reflex. exact IHs2.
Qed.

Lemma string_eq_reflex: forall s: string, string_eq s s = true.
Proof.
  intros s.
  induction s; simpl.
    (* Base case *)
    now reflexivity.
    (* Step *)
    rewrite ascii_eq_reflex. now exact IHs.
Qed.

Definition string_neq s1 s2 := negb (string_eq s1 s2).

(* Boolean version of expression equality *)
Fixpoint TPExp_eq exp1 exp2 :=
  match exp1, exp2 with
    | TPExpConst c1, TPExpConst c2 => TPConstant_eq c1 c2
    | TPExpId id1, TPExpId id2 => string_eq id1 id2
    | TPExpApp exp11 exp12, TPExpApp exp21 exp22 => andb (TPExp_eq exp11 exp21) (TPExp_eq exp12 exp22)
    | TPExpAbstr id1 exp1, TPExpAbstr id2 exp2 => andb (string_eq id1 id2) (TPExp_eq exp1 exp2)
    | TPExpIf e11 e12 e13, TPExpIf e21 e22 e23 => andb (TPExp_eq e11 e21) (andb (TPExp_eq e12 e22) (TPExp_eq e13 e23))
    | TPExpLet id1 e11 e12, TPExpLet id2 e21 e22 => andb (string_eq id1 id2) (andb (TPExp_eq e11 e21) (TPExp_eq e12 e22))
    | TPExpRec id1 e1, TPExpRec id2 e2 => andb (string_eq id1 id2) (TPExp_eq e1 e2)
    | _, _ => false
  end.

(* Consistency lemma *)
Lemma TPExp_eq_consist: forall exp1 exp2: TPExp, (TPExp_eq exp1 exp2) = true <-> exp1 = exp2.
Proof.
  intros exp1 exp2.
  split; intros H.
    (* => *)
    generalize dependent exp2.
    induction exp1; destruct exp2; intros H; try discriminate; simpl in H.
    (* Case: TPExpConst *)
    apply TPConstant_eq_consist in H. rewrite H. now reflexivity.
    (* Case: TPExpId *)
    apply string_eq_consist in H. rewrite H. now reflexivity.
    (* Case: TPExpApp *)
    apply andb_prop in H. destruct H as [H H'].
    rewrite IHexp1_1 with (exp2:=exp2_1).
    rewrite IHexp1_2 with (exp2:=exp2_2).
    now reflexivity. now exact H'. now exact H.
    (* Case: TPExpAbstr *)
    apply andb_prop in H. destruct H as [H H'].
    apply string_eq_consist in H. rewrite H.
    rewrite IHexp1 with (exp2:=exp2).
    now reflexivity. now exact H'.
    (* Case: TPExpIf *)
    apply andb_prop in H. destruct H as [H H'].
    apply andb_prop in H'. destruct H' as [H' H''].
    rewrite IHexp1_1 with (exp2:=exp2_1).
    rewrite IHexp1_2 with (exp2:=exp2_2).
    rewrite IHexp1_3 with (exp2:=exp2_3).
    now reflexivity.
    now exact H''. now exact H'. now exact H.
    (* Case: TPExpLet *)
    apply andb_prop in H. destruct H as [H H'].
    apply andb_prop in H'. destruct H' as [H' H''].
    apply string_eq_consist in H. rewrite H.
    rewrite IHexp1_1 with (exp2:=exp2_1).
    rewrite IHexp1_2 with (exp2:=exp2_2).
    now reflexivity.
    now exact H''. now exact H'.
    (* Case: TPExpRec *)
    apply andb_prop in H. destruct H as [H H'].
    apply string_eq_consist in H. rewrite H.
    rewrite IHexp1 with (exp2:=exp2).
    now reflexivity.
    now exact H'.
    (* <= *)
    rewrite H. clear H. clear exp1.
    induction exp2; simpl.
    (* Case TPExpConst *)
    now apply TPConstant_eq_reflex.
    (* Case TPExpId *)
    now apply string_eq_reflex.
    (* Case TPExpApp *)
    rewrite IHexp2_1. rewrite IHexp2_2.
    simpl. now reflexivity.
    (* Case TPExpAbstr *)
    rewrite string_eq_reflex. rewrite IHexp2.
    simpl. now reflexivity.
    (* Case TPExpIf *)
    rewrite IHexp2_1. rewrite IHexp2_2. rewrite IHexp2_3.
    simpl. now reflexivity.
    (* Case TPExpLet *)
    rewrite string_eq_reflex. rewrite IHexp2_1. rewrite IHexp2_2. 
    simpl. now reflexivity.
    (* Case TPExpRec *)
    rewrite string_eq_reflex. rewrite IHexp2.
    simpl. now reflexivity.
Qed.

End TPSyntax.
