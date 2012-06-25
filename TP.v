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
            else TPapp e1 (small_step exp2)        (* APP-RIGHT *)
          else TPapp (small_step e1) exp2          (* APP-LEFT *)
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
      else TPlet id (small_step e1) e2             (* LET-EVAL *)
    | TPrec id e => subst e (TPrec id e) id        (* UNFOLD *)
    | _ => TPconst TPhang
  end.

