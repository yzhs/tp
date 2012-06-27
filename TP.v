(* De TP Gedöns *)

Require Import ZArith.
Require Import Syntax.
Require Import String.
Require Import Ascii.
Require Import List.

Open Scope Z_scope.

(* String definition *)

Inductive TPop' :=
 | TPplus
 | TPminus
 | TPmult
 | TPdiv
 | TPmod
 | TPless
 | TPlesseq
 | TPgreater
 | TPgreatereq
 | TPeq
 | TPneq
.

Inductive TPconst' :=
 | TPunit
 | TPbool (b : bool)
 | TPint (n : Z)
 | TPop (op : TPop')
 | TPexn
 | TPhang
.

Inductive TPExp :=
 | TPconst (c : TPconst')
 | TPid (id : string)
 | TPapp (a b : TPExp)
 | TPabst (id : string) (exp : TPExp)
 | TPif (exp1 exp2 exp3 : TPExp)
 | TPlet (id : string) (exp1 exp2 : TPExp)
 | TPrec (id : string) (exp : TPExp)
.

Fixpoint TPisvalue (exp : TPExp) : bool :=
  match exp with
    | TPconst _ => true
    | TPabst _ _ => true
    | TPapp (TPconst (TPop _)) exp => TPisvalue exp
    | _ => false
  end.

(* Small step semantics *)
(* {{{ *)
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

SearchPattern (list _ -> bool).

(* Boolean version of operator equality *)
Definition TPop_eq op1 op2 :=
  match op1, op2 with
    | TPplus, TPplus => true
    | TPminus, TPminus => true
    | TPmult, TPmult => true
    | TPdiv, TPdiv => true
    | TPmod, TPmod => true
    | TPless, TPless => true
    | TPlesseq, TPlesseq => true
    | TPgreater, TPgreater => true
    | TPgreatereq, TPgreatereq => true
    | TPeq, TPeq => true
    | TPneq, TPneq => true
    | _, _ => false
  end.

(* Consistency lemma *)
Lemma TPop_eq_consist: forall op1 op2: TPop', TPop_eq op1 op2 = true <-> op1 = op2.
Proof.
  intros op1 op2.
  split; intros H.
    (* => *)
    destruct op1; destruct op2; solve [discriminate | reflexivity].
    (* <= *)
    destruct op1; destruct op2; simpl; solve [discriminate | reflexivity].
Qed.

Lemma TPop_eq_reflex: forall op: TPop', TPop_eq op op = true.
Proof.
  intros op.
  destruct op; simpl; reflexivity.
Qed.

(* Boolean version of constant equality *)
Fixpoint TPconst_eq c1 c2 :=
  match c1, c2 with
    | TPunit, TPunit => true
    | TPbool b1, TPbool b2 => bool_eq b1 b2
    | TPint n1, TPint n2 => Zeq_bool n1 n2
    | TPop op1, TPop op2 => TPop_eq op1 op2
    | TPexn, TPexn => true
    | TPhang, TPhang => true
    | _, _ => false
  end.

(* Consistency lemma *)
Lemma TPconst_eq_consist: forall c1 c2: TPconst', TPconst_eq c1 c2 = true <-> c1 = c2.
Proof.
  intros c1 c2.
  split; intros H.
    (* => *)
    destruct c1; destruct c2; simpl in H; try discriminate; try reflexivity.
    apply bool_eq_ok in H; rewrite H; reflexivity.
    apply Zeq_bool_eq in H; rewrite H; reflexivity.
    apply TPop_eq_consist in H; rewrite H; reflexivity.
    (* <= *)
    destruct c1; destruct c2; simpl in H; simpl; try discriminate; try reflexivity.
    inversion H. destruct b0; reflexivity.
    inversion H. apply Zeq_is_eq_bool. reflexivity.
    inversion H. apply TPop_eq_consist. reflexivity.
Qed.

Lemma TPconst_eq_reflex: forall c: TPconst', TPconst_eq c c = true.
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
    now apply TPop_eq_reflex.
    (* Case TPexn*)
    now reflexivity.
    (* Case TPhang*)
    now reflexivity.
Qed.

(* }}} *)

(*Definition string_eq s1 s2 := andb (prefix s1 s2) (prefix s2 s1).*)

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
    | TPconst c1, TPconst c2 => TPconst_eq c1 c2
    | TPid id1, TPid id2 => string_eq id1 id2
    | TPapp exp11 exp12, TPapp exp21 exp22 => andb (TPExp_eq exp11 exp21) (TPExp_eq exp12 exp22)
    | TPabst id1 exp1, TPabst id2 exp2 => andb (string_eq id1 id2) (TPExp_eq exp1 exp2)
    | TPif e11 e12 e13, TPif e21 e22 e23 => andb (TPExp_eq e11 e21) (andb (TPExp_eq e12 e22) (TPExp_eq e13 e23))
    | TPlet id1 e11 e12, TPlet id2 e21 e22 => andb (string_eq id1 id2) (andb (TPExp_eq e11 e21) (TPExp_eq e12 e22))
    | TPrec id1 e1, TPrec id2 e2 => andb (string_eq id1 id2) (TPExp_eq e1 e2)
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
    (* Case: TPconst *)
    apply TPconst_eq_consist in H. rewrite H. now reflexivity.
    (* Case: TPid *)
    apply string_eq_consist in H. rewrite H. now reflexivity.
    (* Case: TPapp *)
    apply andb_prop in H. destruct H as [H H'].
    rewrite IHexp1_1 with (exp2:=exp2_1).
    rewrite IHexp1_2 with (exp2:=exp2_2).
    now reflexivity. now exact H'. now exact H.
    (* Case: TPabst *)
    apply andb_prop in H. destruct H as [H H'].
    apply string_eq_consist in H. rewrite H.
    rewrite IHexp1 with (exp2:=exp2).
    now reflexivity. now exact H'.
    (* Case: TPif *)
    apply andb_prop in H. destruct H as [H H'].
    apply andb_prop in H'. destruct H' as [H' H''].
    rewrite IHexp1_1 with (exp2:=exp2_1).
    rewrite IHexp1_2 with (exp2:=exp2_2).
    rewrite IHexp1_3 with (exp2:=exp2_3).
    now reflexivity.
    now exact H''. now exact H'. now exact H.
    (* Case: TPlet *)
    apply andb_prop in H. destruct H as [H H'].
    apply andb_prop in H'. destruct H' as [H' H''].
    apply string_eq_consist in H. rewrite H.
    rewrite IHexp1_1 with (exp2:=exp2_1).
    rewrite IHexp1_2 with (exp2:=exp2_2).
    now reflexivity.
    now exact H''. now exact H'.
    (* Case: TPrec *)
    apply andb_prop in H. destruct H as [H H'].
    apply string_eq_consist in H. rewrite H.
    rewrite IHexp1 with (exp2:=exp2).
    now reflexivity.
    now exact H'.
    (* <= *)
    rewrite H. clear H. clear exp1.
    induction exp2; simpl.
    (* Case TPconst *)
    now apply TPconst_eq_reflex.
    (* Case TPid *)
    now apply string_eq_reflex.
    (* Case TPapp *)
    rewrite IHexp2_1. rewrite IHexp2_2.
    simpl. now reflexivity.
    (* Case TPabst *)
    rewrite string_eq_reflex. rewrite IHexp2.
    simpl. now reflexivity.
    (* Case TPif *)
    rewrite IHexp2_1. rewrite IHexp2_2. rewrite IHexp2_3.
    simpl. now reflexivity.
    (* Case TPlet *)
    rewrite string_eq_reflex. rewrite IHexp2_1. rewrite IHexp2_2. 
    simpl. now reflexivity.
    (* Case TPrec *)
    rewrite string_eq_reflex. rewrite IHexp2.
    simpl. now reflexivity.
Qed.

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
    | _ => if TPisvalue exp then exp else TPconst TPhang
  end.

Compute small_step (small_step (TPapp (TPabst "x" (TPapp (TPapp (TPconst( TPop TPplus)) (TPid "x")) (TPconst (TPint 1)))) (TPconst (TPint 2)))).

Inductive TPtype :=
| TP_unit
| TP_bool
| TP_int
| TP_fun (t1 t2 : TPtype)
| TP_var (id : string)
| TP_error.

Inductive TPtype_equality :=
| TP_eq (t1 t2 : TPtype).

Inductive Subst' :=
| Subst (a b : TPtype)
| Error.

Fixpoint type_eq t1 t2 :=
  match t1, t2 with
    | TP_unit, TP_unit => true
    | TP_bool, TP_bool => true
    | TP_int, TP_int => true
    | TP_fun t1 t2, TP_fun t3 t4 => andb (type_eq t1 t3) (type_eq t2 t4)
    | TP_var id1, TP_var id2 => string_eq id1 id2
    | TP_error, TP_error => true
    | _, _ => false
  end.

Lemma type_eq_consist: forall t1 t2: TPtype, type_eq t1 t2 = true <-> t1 = t2.
Proof.
  intros t1 t2. split; intros H.
  (* => *)
    generalize dependent t2.
    induction t1; destruct t2; intros H; try (discriminate || reflexivity).
    (* Case: TP_fun *)
    simpl in H. apply andb_prop in H. destruct H as [H H'].
    rewrite IHt1_1 with (t2:=t2_1).
    rewrite IHt1_2 with (t2:=t2_2).
    now reflexivity. now exact H'. now exact H.
    (* Case: TP_var *)
    simpl in H. apply string_eq_consist in H. rewrite H.
    now reflexivity.
  (* <= *)
    rewrite H. clear H. clear t1.
    induction t2; simpl; try reflexivity.
    (* Case: TP_fun *)
    rewrite IHt2_1. rewrite IHt2_2. simpl. now reflexivity.
    (* Case: TP_var *)
    apply string_eq_reflex.
Qed.  

Fixpoint complexity_type t :=
  match t with
    | TP_fun t1 t2 => plus (plus (complexity_type t1) (complexity_type t2)) (1%nat)
    | _ => 1%nat
  end.

Definition complexity_type_eq t :=
  match t with
    | TP_eq t1 t2 => plus (complexity_type t1) (complexity_type t2)
  end.

Definition complexity types := fold_left plus (map complexity_type_eq types) 0%nat.

Require Import Recdef.

Function unify (types : list TPtype_equality) {measure complexity} : list Subst' :=
  match types with
    | nil => nil
    | ((TP_eq (TP_fun t1 t2) (TP_fun t1' t2')) :: lst) => unify ((TP_eq t1 t1') :: (TP_eq t2 t2') :: lst)
    | (TP_eq (TP_var id) t) :: lst => (Subst t (TP_var id)) :: unify lst
    | (TP_eq t (TP_var id)) :: lst => (Subst t (TP_var id)) :: unify lst
    | (TP_eq t1 t2) :: lst => if type_eq t1 t2 then unify lst else Error :: nil
  end.
Proof.
  intros.
  induction lst.
  now intuition.
  unfold complexity.
Admitted.


Inductive Typing_judgement :=
  | tj (env : list (string * TPtype)) (exp : TPExp) (type : TPtype).

Definition typeof op :=
  match op with
    | TPplus | TPminus | TPmult | TPdiv | TPmod => TP_fun TP_int (TP_fun TP_int TP_int)
    | _ => TP_fun TP_int (TP_fun TP_int TP_bool)
  end.

Fixpoint typing_rules env exp {struct exp} :=
  match exp with
    | TPconst TPunit => TP_unit
    | TPconst (TPbool _) => TP_bool
    | TPconst (TPint _) => TP_int
    | TPconst (TPop op) => typeof op
    | TPconst TPexn => TP_error
    | TPconst TPhang => TP_error
    | TPid id => match find (fun a => string_eq id (fst a)) env with | Some (a,b) => b | None => TP_var "" end
    | TPapp e1 e2 =>
      match typing_rules env e1 with
        | TP_fun t1 t2 => if type_eq (typing_rules env e2) t1 then t2 else TP_error
        | _ => TP_error
      end
    | TPabst id e => typing_rules env e
    | TPif e1 e2 e3 => if negb (type_eq (typing_rules env e1) TP_bool) then TP_error else if negb (type_eq (typing_rules env e2) (typing_rules env e3)) then TP_error else typing_rules env e2
    | TPlet id e1 e2 => typing_rules ((id, typing_rules env e1) :: env) e2
    | TPrec id e => typing_rules env e
  end.
