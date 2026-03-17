From mathcomp Require Import all_boot ssrnat ssralg.
From Stdlib Require Import Bool Wf_nat Lia CMorphisms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Record Merge (n m : nat) := MkMerge {
  mcode        : bitseq;
  mcode_size   : size mcode == n + m;
  mcode_count  : count id mcode == n;
}.

Fixpoint merge_seq {A : eqType} (c : bitseq) (l1 l2 : seq A) : seq A :=
  match c, l1, l2 with
  | [::], _, _=> [::]
  | true :: c', h :: t, _=> h :: merge_seq c' t  l2
  | false :: c', _, h :: t  => h :: merge_seq c' l1 t
  | _, _, _ => [::]
  end.

Definition merge_result {A : eqType} {n m } (m' : Merge n m) l1 l2 : seq A :=
  merge_seq (mcode m') l1 l2 .

Definition shuffle n m (n' : Merge n m ) : (n+m).-tuple bool.
Proof.
apply (@Tuple (n+m) _ (mcode n')).
apply mcode_size.
Defined.
