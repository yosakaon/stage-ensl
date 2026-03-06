From Stdlib Require Import Bool Wf_nat Lia CMorphisms.
From OLlibs Require Import List_more PermutationT_more ShuffleT.
Import ListNotations.
From HB Require Import structures.
From mathcomp Require Import all_boot.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import choice fintype tuple finfun bigop finset binomial.
From mathcomp Require Import fingroup morphism perm.
Require Import shuffle.
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

Lemma PermutationT_to_perm_eq {A : eqType} (l1 l2 : seq A) :
  PermutationT l1 l2 -> perm_eq l1 l2.
Proof.
elim.
  exact: perm_refl.
  by move=> a l1' l2' _ Hp; rewrite perm_cons.
  by move=> a b l /=; rewrite -cat1s -(cat1s a) perm_catCA.
  by move=> l1' l2' l3' _ H1 _ H2; exact: perm_trans H1 H2.
Qed.

Lemma perm_eq_to_PermutationT {A : eqType} (l1 l2 : seq A) :
  perm_eq l1 l2 -> PermutationT l1 l2.
Proof.
elim: l1 l2.
  move=> l2 /perm_size /= Hs.
    by rewrite (size0nil (esym Hs)).
    move=> a l1 IH l2 Hperm.
    have HinA : a \in l2 by rewrite -(perm_mem Hperm) mem_head.
    case: (splitPr HinA) Hperm => p q Hperm.
    apply: PermutationT_cons_app.
    apply: IH.
    rewrite -cat1s in Hperm.
    have : perm_eq (a :: l1) (a :: p ++ q).
      apply: perm_trans Hperm _.
      rewrite -cat1s catA perm_catC perm_sym -cat1s perm_catC catA.
      rewrite -cat1s !cats0 perm_catC.
      by rewrite perm_catC (perm_cat2r [::a]) perm_catC.
      by rewrite perm_cons.
Qed.

(* this one uses the translation, should be rm / a fin informative *)
Lemma perm_eq_shuffle {A : eqType} (l1 l2 l3 : seq A) (l3' : seq A) :
  shuffle l1 l2 l3 -> perm_eq l3 l3' ->
  { l1' & { l2' & perm_eq l1 l1' * perm_eq l2 l2' * shuffle l1' l2' l3' }}.
Proof.
move=> /shuffle_to_shuffleT Hsh Hperm.
have HpermT := perm_eq_to_PermutationT _ _ Hperm.
have [[l1' l2'] [Hl1' Hl2'] Hsh'] := PermutationT_shuffleT Hsh HpermT.
exact: (existT _ l1' (existT _ l2'
                        (PermutationT_to_perm_eq Hl1', PermutationT_to_perm_eq Hl2', shuffleT_to_shuffle Hsh'))).
Qed.

(* standalone proof with mathcomp *)
Lemma perm_eq_app_middle {T : eqType} A (l1 l2 l1' l2' : seq T) :
  perm_eq (l1 ++ l2) (l1' ++ l2') ->
  perm_eq (l1 ++ A :: l2) (l1' ++ A :: l2').
Proof.
move=> Hperm.
rewrite (perm_catCA l1 [::A] l2) perm_sym (perm_catCA l1' [::A] l2').
by rewrite perm_cons perm_sym.
Qed.

Lemma shuffle_perm_eq (A : eqType) (l1 l2 l3 l3' : seq A) :
  shuffle l1 l2 l3 ->
  perm_eq l3 l3' ->
  {l1' : seq A & {l2' : seq A & perm_eq l1 l1' * perm_eq l2 l2' * shuffle l1' l2' l3'}}.
Proof.
move=> [bs [Hsize [Hmask1 Hmask2]]] Hp.
apply: (catCA_perm_ind
          (P := fun s => {l1' & {l2' & perm_eq l1 l1' * perm_eq l2 l2' * shuffle l1' l2' s}}) _ Hp).
2: { exists l1, l2; split; [split|].
         exact: perm_refl.
         exact: perm_refl.
         exists bs; auto. }
move=> s1 s2 s3 [l1' [l2' [[Hp1 Hp2] Hs]]].
rewrite catA in Hs.
move: (shuffle_app_inv (s1++s2) s3 Hs) =>
      [a [a' [c [c' [[[Ha Hc] Hs12] Hs3]]]]].
move: (shuffle_app_inv s1 s2 Hs12) =>
      [a1 [a2 [c1 [c2 [[[Ha12 Hc12] Hs1'] Hs2']]]]].
subst.
exists (a2 ++ a1 ++ a'), (c2 ++ c1 ++ c').
split; [split|].
  rewrite (perm_trans Hp1) => //.
  by rewrite catA perm_cat2r perm_catC.
  by rewrite (perm_trans Hp2) //= catA perm_cat2r perm_catC.
  rewrite !catA.
  apply: (@shuffle_app_app _ (a2++a1) (c2++c1) (s2++s1) a' c' s3); last by exact: Hs3.
  exact: shuffle_cat_swap Hs1' Hs2'.
Qed.
