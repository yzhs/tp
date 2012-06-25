(* De TP Gedöns *)

Require Import ZArith.
Require Import Syntax.
Require Import String.

(* String definition *)

Inductive TPOp' :=
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

Inductive TPConst' :=
 | TPunit
 | TPbool (b : bool)
 | TPint (n : Z)
 | TPOp (op : TPOp')
 | TPexn
.

Inductive TPExp :=
 | TPConst (c : TPConst')
 | TPid (id : string)
 | TPapp (a b : TPExp)
 | TPabst (id : string) (exp : TPExp)
 | TPif (exp1 exp2 exp3 : TPExp)
 | TPlet (id : string) (exp1 exp2 : TPExp)
 | TPrec (id : string) (exp : TPExp)
.

Fixpoint TPisvalue (exp : TPExp) : Prop :=
 match exp with
 | TPConst _ => True
 | TPabst _ _ => True
 | TPapp (TPConst (TPOp _)) exp => TPisvalue exp
 | _ => False
end.

(* Small step semantics *)