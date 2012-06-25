(* De TP Gedöns *)

Require Import ZArith.
Require Import Syntax.
Require Import String.
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
(* }}} *)

Definition string_eq s1 s2 := andb (prefix s1 s2) (prefix s2 s1).
Definition string_neq s1 s2 := negb (string_eq s1 s2).

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
    | _, _ => false
  end.

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
