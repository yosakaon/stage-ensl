From Stdlib Require Import Bool Wf_nat Lia CMorphisms.
From OLlibs Require Import List_more PermutationT_more ShuffleT.
Import ListNotations.
From HB Require Import structures.
From mathcomp Require Import all_boot.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import choice fintype tuple finfun bigop finset binomial.
From mathcomp Require Import fingroup morphism perm.
Require Import shuffle perm_shuffle.
Set Default Proof Using "Type".
Set Implicit Arguments.

Definition atom := nat : Type.
Inductive formula := var (_ : bool) (_ : atom) | bin (_ : bool) (_ _ : formula).
Infix "⊗" := (bin true) (at level 34).
Infix "⅋" := (bin false) (at level 35).

Scheme Equality for formula.
Lemma formula_eqP : Equality.axiom formula_eq_dec.
Proof.
move=> x y.
case: formula_eq_dec => //= H; by constructor.
Qed.

HB.instance Definition _ := hasDecEq.Build formula formula_eqP.

Reserved Notation "⊢' l" (at level 65).
Inductive mll_shuffle : seq formula -> Type :=
| ax_shuffle b X : ⊢' [var b X; var (negb b) X]
| tr_shuffle l1 m1 l2 m2 n1 n2 A B :
  shuffle l1 m1 n1 -> shuffle l2 m2 n2 -> ⊢' l1 ++ A :: l2 -> ⊢' m1 ++ B :: m2 -> ⊢' n1 ++ A ⊗ B :: n2
| pr_shuffle l1 A B l2 : ⊢' l1 ++ A :: B :: l2 -> ⊢' l1 ++ A ⅋ B :: l2
where "⊢' l" := (mll_shuffle l).
Arguments ax_shuffle {_ _}, [_] _, _ _.
Arguments pr_shuffle [_ _ _ _] _, _ [_ _ _] _, _ _ _ [_] _.
Arguments tr_shuffle [_ _ _ _ _ _ _ _ _ _] _ _, [_ _ _ _ _ _ _ _] _ _ _ _, _ _ _ _ [_ _ _ _] _ _ _ _.

Fixpoint psize_shuffle l (pi : ⊢' l) :=
match pi with
| ax_shuffle _ _  => 1
| pr_shuffle _ _ _ _ pi1 => S (psize_shuffle pi1)
| tr_shuffle _ _ _ _ _ _ _ _ _ _ pi1 pi2=> S (psize_shuffle pi1 + psize_shuffle pi2)
end.

Reserved Notation "A ┴".
Fixpoint dual A :=
match A with
| var b X => var (negb b) X
| bin b B C => bin (negb b) (B┴) (C┴)
end
where "A ┴" := (dual A) (only parsing).
Notation "A 'ᗮ'" := (dual A) (left associativity, format "A ᗮ").

Instance ex_shuffle : Proper (perm_eq ==> iffT) mll_shuffle.
Proof.
move=> l1 l2 Hperm.
split => Hd.
 move: l2 Hperm.
 elim: Hd.
    (* ax_shuffle *)
   - move=> b X l2 h1.
     rewrite perm_sym in h1.
     case: (perm_eq_length_2_inv _ _ _ h1) => ->.
       exact: ax_shuffle.
       by rewrite -{2}(negbK b); exact: ax_shuffle.
    (* tr_shuffle *)
    - move=> l0 m1 l3 m2 n1 n2 A B s s0 H1 IH1 H2 IH2 l' Hp.
      have Hpinv : perm_eq l' (A ⊗ B :: (n1 ++ n2)).
        by rewrite perm_sym -cat1s perm_catCA /=.
      have [p [q [Heq Hpq]]] := perm_eq_vs_cons_inv (A ⊗ B) _ _ Hpinv.
      subst l'.
      have Hnn := shuffle_app_app s s0.
      have Hpq' : perm_eq (n1 ++ n2) (p ++ q) by rewrite perm_sym.
      have [l12' [l12'' [[Hl1 Hl2] Hsh]]] := shuffle_perm_eq _ _ Hnn Hpq'.
      have [l0' [l3' [m1' [m2' [[[Hl0 Hm1] sp] sq]]]]]:= shuffle_app_inv p q Hsh.
      apply (@tr_shuffle _ _ _ _ _ _ _ _ sp sq).
      by apply: IH1; apply: perm_eq_app_middle; rewrite Hl0 in Hl1.
      by apply: IH2; apply: perm_eq_app_middle; rewrite Hm1 in Hl2.
    (* pr_shuffle *)
    - move=> l0 A B l2 Hpr IH l3 Hp.
      have Hpinv : perm_eq l3 (A ⅋ B :: (l0 ++ l2)).
        by rewrite -cat1s perm_sym perm_catCA.
      have [p [q [Heq Hpq]]] := perm_eq_vs_cons_inv (A ⅋ B) _ _ Hpinv.
      subst l3.
      apply: pr_shuffle.
      apply: IH.
      rewrite perm_sym.
      by do 2! apply: perm_eq_app_middle.
    - (* sym *)
      move: l1 Hperm.
      elim: Hd.
    (* ax_shuffle *)
    - move=> b X l1 h1.
      case: (perm_eq_length_2_inv _ _ _ h1) => ->.
        exact: ax_shuffle.
        rewrite -{2}(negbK b); exact: ax_shuffle.
    (* tr_shuffle *)
    - move=> l0 m1 l3 m2 n1 n2 A B s s0 H1 IH1 H2 IH2 l' Hp.
      have Hpinv : perm_eq l' (A ⊗ B :: (n1 ++ n2)).
        by rewrite -cat1s perm_sym perm_catCA perm_sym.
      have [p [q [Heq Hpq]]] := perm_eq_vs_cons_inv (A ⊗ B) _ _ Hpinv.
      subst l'.
      have Hnn := shuffle_app_app s s0.
      have Hpq' : perm_eq (n1 ++ n2) (p ++ q) by rewrite perm_sym.
      have [l12' [l12'' [[Hl1 Hl2] Hsh]]] := shuffle_perm_eq _ _ Hnn Hpq'.
      have [l0' [l3' [m1' [m2' [[[Hl0 Hm1] sp] sq]]]]]:= shuffle_app_inv p q Hsh.
      apply (@tr_shuffle _ _ _ _ _ _ _ _ sp sq).
        by apply: IH1; apply: perm_eq_app_middle; rewrite perm_sym -Hl0.
        by apply: IH2; apply: perm_eq_app_middle; rewrite perm_sym -Hm1.
    (* pr_shuffle *)
    - move=> l1 A B l0 Hpr IH l3 Hp.
      have Hpinv : perm_eq l3 (A ⅋ B :: (l1 ++ l0)) by rewrite -cat1s perm_sym perm_catCA perm_sym.
      have [p [q [Heq Hpq]]] := perm_eq_vs_cons_inv (A ⅋ B) _ _ Hpinv.
      subst l3.
      apply: pr_shuffle; apply: IH.
      by rewrite perm_sym; do 2! apply: perm_eq_app_middle; rewrite perm_sym.
Qed.

Lemma ex_size_shuffle l' l (p : perm_eq l l') (pi : ⊢' l) : { pi' : ⊢' l' | psize_shuffle pi' = psize_shuffle pi }.
Proof.
induction pi in l', p |- *.
  rewrite perm_sym in p.
  destruct (perm_eq_length_2_inv _ _ _ p) as [-> | ->] => //=.
    - by exists (ax_shuffle b X).
    - by rewrite (negb_involutive_reverse (b)) negb_involutive; exists (ax_shuffle (~~ b) X).     
    - have tr1 := (tr_shuffle s s0 pi1 pi2).
      have Hpinv : perm_eq l' (A ⊗ B :: (n1 ++ n2)) by rewrite perm_sym -cat1s perm_catCA /=.
      have [p' [q [Heq Hpq]]] := perm_eq_vs_cons_inv (A ⊗ B) _ _ Hpinv.
      subst l'.
      have Hnn := shuffle_app_app s s0.
      have Hpq' : perm_eq (n1 ++ n2) (p' ++ q) by rewrite perm_sym.
      have [l12' [l12'' [[Hl1 Hl2] Hsh]]] := shuffle_perm_eq _ _ Hnn Hpq'.
      have [l0' [l3' [m1' [m2' [[[Hl0 Hm1] sp] sq]]]]]:= shuffle_app_inv p' q Hsh.
      have HpermA : perm_eq (l1 ++ A :: l2) (l0' ++ A :: l3'). 
        by rewrite perm_eq_app_middle => //=; rewrite Hl0 in Hl1.
    have HpermB : perm_eq (m1 ++ B :: m2) (m1' ++ B :: m2').
      by rewrite perm_eq_app_middle => //=; rewrite Hm1 in Hl2.
    have [HApq HsizeA] := IHpi1 _ HpermA.
    have [HBpq HsizeB] := IHpi2 _ HpermB.
    exists (tr_shuffle sp sq HApq HBpq).
    f_equal.
    by rewrite /= HsizeA HsizeB.
  - have Hpinv : perm_eq l' (A ⅋ B :: (l1 ++ l2)).
        by rewrite -cat1s perm_sym perm_catCA.
      have [p' [q [Heq Hpq]]] := perm_eq_vs_cons_inv (A ⅋ B) _ _ Hpinv.
      subst l'.
      have Hab : perm_eq (l1 ++ [:: A, B & l2]) (p' ++ [:: A, B & q]). 
        rewrite (perm_catCA l1 [::A;B] l2). 
        rewrite perm_sym (perm_catCA p' [::A;B] q).
        by rewrite !perm_cons.
      have [piAB HpiAB] := IHpi _ Hab.
      exists (pr_shuffle piAB) => /=.
      f_equal => //.
Qed.

Lemma ax_gen_shuffle A : ⊢' [A; A┴].
Proof.
induction A => //= ; last 2 first.
  by apply ax_shuffle.
  destruct b => //=.
  apply: (@pr_shuffle [::_] _ _ _ ).
  apply: (@tr_shuffle [::] [::] [::dual A1] [::dual A2] [::])=> //= ; last 2 first.
- by apply: shuffle_nil.
  by exists [:: true; false] => //=.
- apply: (@pr_shuffle [::]) => //=.  
  apply: (@tr_shuffle [A1] [A2] [::] [::] [::A1 ; A2]) => //=; last 2 first.
    by exists [:: true; false].
    by apply: shuffle_nil.
Qed.
