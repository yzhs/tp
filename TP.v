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

Fixpoint TPisvalue (exp : TPExp) : Prop :=
 match exp with
 | TPconst _ => True
 | TPabst _ _ => True
 | TPapp (TPconst (TPop _)) exp => TPisvalue exp
 | _ => False
end.

(* Small step semantics *)
(* {{{ *)
Definition eval op n1 n2 :=
  match op,  n1, n2 with
    | TPplus,     TPint n, TPint n' => TPint (n + n')
    | TPminus,    TPint n, TPint n' => TPint (n - n')
    | TPmult,     TPint n, TPint n' => TPint (n * n')
    | TPdiv,      TPint n, TPint n' => TPint (n / n')
    | TPmod,      TPint n, TPint n' => TPint (n mod n')
    | TPless,     TPint n, TPint n' => TPbool (Zlt_bool n n')
    | TPlesseq,   TPint n, TPint n' => TPbool (Zle_bool n n')
    | TPgreater,  TPint n, TPint n' => TPbool (Zgt_bool n n')
    | TPgreatereq,TPint n, TPint n' => TPbool (Zge_bool n n')
    | TPeq,       TPint n, TPint n' => TPbool (Zeq_bool n n')
    | TPneq,      TPint n, TPint n' => TPbool (Zneq_bool n n')
    | _, _, _ => TPhang
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

Fixpoint free exp :=
  match exp with
    | TPconst _ => nil
    | TPid id => id :: nil
    | TPapp exp1 exp2 => app (free exp1) (free exp2)
    | TPif exp1 exp2 exp3 => app (free exp1) (app (free exp2) (free exp3))
    | TPabst id exp => filter (Lfree 

Fixpoint subst (exp : TPexp) id

Definition small_step exp :=
  match exp with
    | TPapp (TPabst id exp1) exp2 => 
    | TPapp (TPapp (TPconst (TPop op)) exp1) exp2 =>  eval op exp1 exp2  (* OP *)

