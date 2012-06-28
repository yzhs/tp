Module TPTyping.

Load TPSmallSteps.
Import TPSmallSteps.

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
  (*unfold complexity.*)
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

End TPTyping.