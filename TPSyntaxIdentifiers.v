Module TPSyntaxIdentifiers.

Require Export String.
Require Import Ascii.
Require Import Arith.

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

(* Boolean version of string equality *)
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

(* Boolean version of string inequality *)
Definition string_neq s1 s2 := negb (string_eq s1 s2).

Definition TPIdentifier: Set := (string * nat)%type.

(* Boolean version of identifier inequality *)
Definition ident_eq i1 i2 :=
  match i1, i2 with
    | (id1, num1), (id2, num2) => andb (string_eq id1 id2) (beq_nat num1 num2)
  end.

Lemma ident_eq_reflex: forall id, ident_eq id id = true.
Proof.
  induction id.
  simpl.
  apply andb_true_intro.
  split.
  now apply string_eq_reflex.
  apply beq_nat_true_iff.
  reflexivity.
Qed.

(* Consistency Lemma *)
Lemma ident_eq_consist: forall id1 id2, ident_eq id1 id2 = true <-> id1 = id2.
Proof.
  induction id1; induction id2; simpl.
  split; intro H.
  (* => *)
    apply andb_prop in H.
    destruct H as [H1 H2].
    apply string_eq_consist in H1.
    symmetry in H2; apply beq_nat_eq in H2.
    rewrite H1; rewrite H2; now reflexivity.
  (* <= *)
    apply andb_true_intro.
    split; [apply string_eq_consist | apply beq_nat_true_iff]; inversion H; reflexivity.
Qed.

Lemma ident_eq_consist_conv: forall id id', ident_eq id id' = false <-> id <> id'.
Admitted.

End TPSyntaxIdentifiers.