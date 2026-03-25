From Stdlib Require Import Bool Wf_nat Lia CMorphisms.
From OLlibs Require Import List_more PermutationT_more ShuffleT.
Import ListNotations.
From HB Require Import structures.
From mathcomp Require Import all_boot.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import choice fintype tuple finfun bigop finset binomial.
From mathcomp Require Import fingroup morphism perm.
Set Default Proof Using "Type".
Set Implicit Arguments.

Lemma perm_eq_length_2_inv {A : eqType} (l : seq A) a b :
  perm_eq l [:: a; b] ->
  { l = [:: a; b] } + { l = [:: b; a] }.
Proof.
move => p.
have Hsize : size l = 2 by rewrite (perm_size p).
move : p.
destruct l as [|x [|y [|? ?]]].
  by move/perm_size.
  by move/perm_size.
  move=> p.
  have Ha : a \in [:: x; y] by rewrite (perm_mem p) mem_head.
  have Hb : b \in [:: x; y] by rewrite (perm_mem p) inE mem_head orbT => //=.
  rewrite !inE in Ha Hb.
  case Hax: (a == x).
    move/eqP: Hax => Hax; subst a.
    case Hby: (b == y).
      by move/eqP: Hby => Hby; subst b; left.
      move: Hb; rewrite Hby orbF => /eqP Hbx; subst b.
      exfalso; move: p => /perm_mem /(_ y).
      rewrite !inE eq_refl orbT /=. 
      move => /eqP.
      rewrite orbb eq_sym.
      rewrite eq_sym in Hby.
      by rewrite Hby.
  move: Ha; rewrite Hax orFb => /eqP Hay; subst a.
  case Hbx: (b == x).
    by move/eqP: Hbx => Hbx; subst b; right.
    move: Hb; rewrite Hbx orFb => /eqP Hby; subst b.
    exfalso; move: p => /perm_mem /(_ x).
    rewrite !inE eq_refl /=. 
    rewrite eq_sym in Hax.
    by rewrite Hax.
    by move=> Hp; rewrite /= in Hsize.
Qed.

Lemma perm_eq_cons_app_inv {T : eqType} A (l l' : seq T) :
  perm_eq (A :: l) l' -> perm_eq l (rem A l').
Proof.
move=> Hperm //=.
have HinA : A \in l' by rewrite -(perm_mem Hperm) mem_head.
rewrite perm_sym.
have := perm_to_rem HinA.
rewrite perm_sym in Hperm.
move=> Hrem.
rewrite perm_sym in Hrem.
have H : perm_eq (A :: rem A l') (A :: l) := perm_trans Hrem Hperm.
by rewrite perm_cons in H.
Qed.

Lemma perm_eq_vs_cons_inv {T : eqType} A (l rest : seq T) :
  perm_eq l (A :: rest) ->
  { p & { q & l = p ++ A :: q /\ perm_eq (p ++ q) rest }}.
Proof.
move=> Hperm.
have HinA : A \in l by rewrite (perm_mem Hperm) mem_head.
case: (splitPr HinA) Hperm => p q Hperm.
exists p, q; split => //.
by rewrite -cat1s perm_catCA /= perm_cons in Hperm => //.
Qed.

Lemma perm_eq_app_middle {T : eqType} A (l1 l2 l1' l2' : seq T) :
  perm_eq (l1 ++ l2) (l1' ++ l2') ->
  perm_eq (l1 ++ A :: l2) (l1' ++ A :: l2').
Proof.
move=> Hperm.
rewrite (perm_catCA l1 [::A] l2) perm_sym (perm_catCA l1' [::A] l2').
by rewrite perm_cons perm_sym.
Qed.
