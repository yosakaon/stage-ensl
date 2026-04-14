From Stdlib Require Import Bool Wf_nat Lia CMorphisms.
From OLlibs Require Import List_more PermutationT_more ShuffleT.
Import ListNotations.
From HB Require Import structures.
From mathcomp Require Import all_boot.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import choice fintype tuple finfun bigop finset binomial.
From mathcomp Require Import fingroup morphism perm.
From mathcomp.zify Require Import zify.
Require Import perm_shuffle2 shuffle2.
Set Default Proof Using "Type".
Set Implicit Arguments.
Require Import Stdlib.Program.Equality.

Definition atom := nat : Type.
Inductive formula := var (_ : bool) (_ : atom) | bin (_ : bool) (_ _ : formula).
Infix "⊗" := (bin true) (at level 34).
Infix "⅋" := (bin false) (at level 35).

Scheme Equality for formula.
Lemma formula_eqP : Equality.axiom formula_eq_dec.
Proof. move=> x y. case: formula_eq_dec => //= H; by constructor. Qed.
HB.instance Definition _ := hasDecEq.Build formula formula_eqP.

Reserved Notation "A ┴".
Fixpoint dual A :=
match A with
| var b X => var (negb b) X
| bin b B C => bin (negb b) (B┴) (C┴)
end
where "A ┴" := (dual A) (only parsing).
Notation "A 'ᗮ'" := (dual A) (left associativity, format "A ᗮ").


Reserved Notation "⊢' l" (at level 65).
Reserved Notation "⊢'' l" (at level 65).
Inductive mll_shuffle : seq formula -> Type :=
| ax_shuffle b X : ⊢' [var b X; var (negb b) X]
| tr_shuffle nl1 nm1 nl2 nm2 l1 m1 l2 m2 n1 n2 A B :
  shuffling nl1 nm1 l1 m1 n1 ->
  shuffling nl2 nm2 l2 m2 n2 ->
  ⊢' l1 ++ A :: l2 ->
  ⊢' m1 ++ B :: m2 ->
  ⊢' n1 ++ A ⊗ B :: n2
| pr_shuffle l1 A B l2 : ⊢' l1 ++ A :: B :: l2 -> ⊢' l1 ++ A ⅋ B :: l2
where "⊢' l" := (mll_shuffle l).

Arguments ax_shuffle {_ _}, [_] _, _ _.
Arguments pr_shuffle [_ _ _ _] _, _ [_ _ _] _, _ _ _ [_] _.
Arguments tr_shuffle [_ _ _ _ _ _ _ _ _ _] _ _, [_ _ _ _ _ _ _ _] _ _ _ _, _ _ _ _ [_ _ _ _] _ _ _ _.

Inductive mll_shuffle_nondep : seq formula -> Type :=
| ax_shuffle_nondep b X : ⊢'' [var b X; var (negb b) X]
| tr_shuffle_nondep nl1 nm1 nl2 nm2 l1 m1 l2 m2 n1 n2 A B :
  shuffling nl1 nm1 l1 m1 n1 -> 
  shuffling nl2 nm2 l2 m2 n2 ->
  ⊢'' l1 ++ A :: l2 ->
  ⊢'' m1 ++ B :: m2 ->
  ⊢'' n1 ++ A ⊗ B :: n2
| pr_shuffle_nondep Γ Δ A B Γ1 Γ2 :
 Γ =  Γ1 ++ [:: A, B & Γ2] -> 
 Δ =  Γ1 ++ A ⅋ B :: Γ2 -> 
 ⊢'' Γ -> ⊢'' Δ

where "⊢'' l" := (mll_shuffle_nondep l).

Arguments ax_shuffle_nondep {_ _}, [_] _, _ _.
Arguments pr_shuffle_nondep [_ _ _ _] _, _ [_ _ _] _, _ _ _ [_] _.
Arguments tr_shuffle_nondep [_ _ _ _ _ _ _ _ _ _] _ _, [_ _ _ _ _ _ _ _] _ _ _ _, _ _ _ _ [_ _ _ _] _ _ _ _.

Lemma mll_shuffle_to_nondep l : mll_shuffle l -> mll_shuffle_nondep l.
Proof.
  intro π. induction π.
  - exact (ax_shuffle_nondep b X).
  - exact (tr_shuffle_nondep A B s s0 IHπ1 IHπ2).
    exact (pr_shuffle_nondep _ _ erefl erefl IHπ).
Qed.

Lemma mll_shuffle_nondep_to l : mll_shuffle_nondep l -> mll_shuffle l.
Proof.
  intro π. induction π.
  - exact (ax_shuffle b X).
  - exact (tr_shuffle A B s s0 IHπ1 IHπ2).
  - subst. 
    exact (pr_shuffle IHπ).
Qed.

Fixpoint psize_shuffle l (pi : ⊢' l) :=
match pi with
| ax_shuffle _ _  => 1
| pr_shuffle _ _ _ _ pi1 => S (psize_shuffle pi1)
| tr_shuffle _ _ _ _ _ _ _ _ _ _ _ _ _ _ pi1 pi2 => S (psize_shuffle pi1 + psize_shuffle pi2)
end.

Fixpoint psize_shuffle_nondep l (pi : ⊢'' l) :=
match pi with
| ax_shuffle_nondep _ _  => 1
| pr_shuffle_nondep _ _ _ _ _ _ _ _ pi1 => S (psize_shuffle_nondep pi1)
| tr_shuffle_nondep _ _ _ _ _ _ _ _ _ _ _ _ _ _ pi1 pi2 => S (psize_shuffle_nondep pi1 +
                                                                psize_shuffle_nondep pi2)
end.

Lemma ax_gen_shuffle A : ⊢' [A; A┴].
Proof.
induction A => //= ; last 2 first.
  by apply ax_shuffle.
  destruct b => //=.
  apply: (@pr_shuffle [::_] _ _ _ ) => //=.
  apply: (@tr_shuffle 0 0 1 1 [::] [::] [::dual A1] [::dual A2] [::] [::dual A1; dual A2] _ _).
      by exists (@MkMerge 0 0 [::] erefl erefl) => //=. 
      by exists (@MkMerge 1 1 [::true; false] erefl erefl).
      all: try rewrite cat0s => //.         
  apply: (@pr_shuffle [::]) => //=.  
  apply: (@tr_shuffle 1 1 0 0 [A1] [A2] [::] [::] [::A1 ; A2]) => //=; last 2 first.
    by exists (@MkMerge 1 1 [::true; false] erefl erefl).
    by exists (@MkMerge 0 0 [::] erefl erefl) => //=. 
Qed.

Lemma ex_size_shuffle l' l (p : perm_eq l l') (pi : ⊢' l) : { pi' : ⊢' l' | psize_shuffle pi' = psize_shuffle pi }.
Proof.
induction pi in l', p |- *.
  rewrite perm_sym in p.
  destruct (perm_eq_length_2_inv _ _ _ p) as [-> | ->] => //=.
    - by exists (ax_shuffle b X).
    - by rewrite (negb_involutive_reverse (b)) negb_involutive; exists (ax_shuffle (~~ b) X).     
    - have tr1 := (tr_shuffle _ _ s s0 pi1 pi2).
      have Hpinv : perm_eq l' (A ⊗ B :: (n1 ++ n2)) by rewrite perm_sym -cat1s perm_catCA /=.
      have [p' [q [Heq Hpq]]] := perm_eq_vs_cons_inv (A ⊗ B) _ _ Hpinv.
      subst l'.
      have Hnn := shuffling_app_app s s0.
      have Hpq' : perm_eq (n1 ++ n2) (p' ++ q) by rewrite perm_sym.
      have [l12' [l12'' [[Hl1 Hl2] Hsh]]] := shuffling_perm_eq Hnn Hpq'.
      have [l0' [l3' [m1' [m2' [[[Hl0 Hm1] sp] sq]]]]]:= shuffling_app_inv Hsh.
      have HpermA : perm_eq (l1 ++ A :: l2) (l0' ++ A :: l3'). 
        by rewrite perm_eq_app_middle => //=; rewrite Hl0 in Hl1.
       have HpermB : perm_eq (m1 ++ B :: m2) (m1' ++ B :: m2').
      by rewrite perm_eq_app_middle => //=; rewrite Hm1 in Hl2.
    have [HApq HsizeA] := IHpi1 _ HpermA.
    have [HBpq HsizeB] := IHpi2 _ HpermB.
    exists (tr_shuffle _ _ sp sq HApq HBpq).
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

Lemma ex_size_shuffle_nondep l' l (p : perm_eq l l') (pi : ⊢'' l) : { pi' : ⊢'' l' | psize_shuffle_nondep pi' = psize_shuffle_nondep pi }.
Proof.
induction pi in l', p |- *.
  rewrite perm_sym in p.
  destruct (perm_eq_length_2_inv _ _ _ p) as [-> | ->] => //=.
    - by exists (ax_shuffle_nondep b X).
    - by rewrite (negb_involutive_reverse (b)) negb_involutive; exists (ax_shuffle_nondep (~~ b) X). 
    - have tr1 := (tr_shuffle_nondep _ _ s s0 pi1 pi2).
      have Hpinv : perm_eq l' (A ⊗ B :: (n1 ++ n2)) by rewrite perm_sym -cat1s perm_catCA /=.
      have [p' [q [Heq Hpq]]] := perm_eq_vs_cons_inv (A ⊗ B) _ _ Hpinv.
      subst l'.
      have Hnn := shuffling_app_app s s0.
      have Hpq' : perm_eq (n1 ++ n2) (p' ++ q) by rewrite perm_sym.
      have [l12' [l12'' [[Hl1 Hl2] Hsh]]] := shuffling_perm_eq Hnn Hpq'.
      have [l0' [l3' [m1' [m2' [[[Hl0 Hm1] sp] sq]]]]]:= shuffling_app_inv Hsh.
      have HpermA : perm_eq (l1 ++ A :: l2) (l0' ++ A :: l3'). 
        by rewrite perm_eq_app_middle => //=; rewrite Hl0 in Hl1.
       have HpermB : perm_eq (m1 ++ B :: m2) (m1' ++ B :: m2').
      by rewrite perm_eq_app_middle => //=; rewrite Hm1 in Hl2.
    have [HApq HsizeA] := IHpi1 _ HpermA.
    have [HBpq HsizeB] := IHpi2 _ HpermB.
    exists (tr_shuffle_nondep _ _ sp sq HApq HBpq).
    f_equal.
    by rewrite /= HsizeA HsizeB.
    - subst Γ Δ.
      have Hpinv : perm_eq l' (A ⅋ B :: (Γ1 ++  Γ2)).
        by rewrite -cat1s perm_sym perm_catCA.
      have [p' [q [Heq Hpq]]] := perm_eq_vs_cons_inv (A ⅋ B) _ _ Hpinv.
      subst l'.
      have Hab : perm_eq (Γ1 ++ [:: A, B &  Γ2]) (p' ++ [:: A, B & q]). 
        rewrite (perm_catCA  Γ1 [::A;B]  Γ2). 
        rewrite perm_sym (perm_catCA p' [::A;B] q).
        by rewrite !perm_cons.
      have [piAB HpiAB] := IHpi _ Hab.
      exists (pr_shuffle_nondep _ _ _ _ _  erefl erefl piAB).
      by rewrite /= HpiAB.
Qed.

Instance ex_shuffle : Proper (perm_eq ==> iffT) mll_shuffle.
Proof.
move=> l l' p; split => pi.
by destruct (ex_size_shuffle _ p pi).
rewrite perm_sym in p.
by destruct (ex_size_shuffle _ p pi).
Qed.

Instance ex_shuffle_nondep : Proper (perm_eq ==> iffT) mll_shuffle_nondep.
Proof.
move=> l l' p; split => pi.
by destruct (ex_size_shuffle_nondep _ p pi).
rewrite perm_sym in p.
by destruct (ex_size_shuffle_nondep _ p pi).
Qed.

Inductive parr_equiv Σ : crelation (⊢'' Σ) :=
| parr_equiv_swap :
  forall Γ Δ Δ' A B C D Γ1 Γ2 Γ3   
         (eqΓ : Γ = Γ1  ++ [:: A, B & (Γ2  ++ [:: C, D & Γ3])]) 
         (eqΔa : Δ = Γ1  ++ A ⅋ B :: Γ2  ++ [:: C, D & Γ3]) 
         (eqΔb : Δ = (Γ1  ++ A ⅋ B ::  Γ2) ++ [:: C, D & Γ3]) 
         (eqΣ : Σ = (Γ1  ++ [:: A ⅋ B &  Γ2]) ++ C ⅋ D :: Γ3) 
         (eqΓr : Γ = (Γ1  ++ [:: A, B & Γ2]) ++ [:: C, D & Γ3])
         (eqΔ'a : Δ' = (Γ1  ++ [:: A, B &  Γ2]) ++ C ⅋ D :: Γ3) 
         (eqΔ'b : Δ' = Γ1  ++ [:: A, B & (Γ2 ++ C ⅋ D :: Γ3)]) 
         (eqΔ' : Σ = Γ1  ++ A ⅋ B :: (Γ2 ++ C ⅋ D :: Γ3))
         (π : ⊢'' Γ),
    parr_equiv
      (@pr_shuffle_nondep Δ Σ C D (Γ1 ++ [:: A ⅋ B & Γ2]) Γ3 eqΔb eqΣ
         (@pr_shuffle_nondep Γ Δ A B Γ1 (Γ2 ++ [:: C, D & Γ3]) eqΓ eqΔa π))
      (@pr_shuffle_nondep Δ' Σ A B Γ1 (Γ2 ++ C ⅋ D :: Γ3) eqΔ'b eqΔ'
         (@pr_shuffle_nondep Γ Δ' C D (Γ1 ++ [:: A, B & Γ2]) Γ3 eqΓr eqΔ'a π)).

Lemma test_invol Σ (π1 : ⊢'' Σ) (π2 : ⊢'' Σ) (π3 : ⊢'' Σ) :
  parr_equiv π1 π2 -> parr_equiv π3 π2 -> π1 = π3.
Proof.

Qed.

Lemma commutation_parr A B C D (π : ⊢'' [:: A; B; C; D]) :
  parr_equiv
  (pr_shuffle_nondep [:: A ⅋ B] [::] erefl erefl (pr_shuffle_nondep [::] [:: C; D] erefl erefl π))
  (pr_shuffle_nondep [::] [:: C ⅋ D] erefl erefl (pr_shuffle_nondep [:: A; B] [::] erefl erefl π)).
Proof.
apply (@parr_equiv_swap [:: A ⅋ B; C ⅋ D] [:: A; B; C; D] [:: A ⅋ B; C; D] [:: A; B; C ⅋ D]
         A B C D [::] [::] [::]).
Qed.
