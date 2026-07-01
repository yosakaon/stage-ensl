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
| tr_shuffle l1 m1 l2 m2 n1 n2 A B :
  shuffling (length l1) (length m1) l1 m1 n1 ->
  shuffling (length l2) (length m2) l2 m2 n2 ->
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
| tr_shuffle_nondep l1 m1 l2 m2 n1 n2 A B :
  shuffling (length l1) (length m1) l1 m1 n1 -> 
  shuffling (length l2) (length m2) l2 m2 n2 ->
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
  - exact (tr_shuffle_nondep _ _ _ _  s s0 IHπ1 IHπ2).
    exact (pr_shuffle_nondep _ _ erefl erefl IHπ).
Qed.

Lemma mll_shuffle_nondep_to l : mll_shuffle_nondep l -> mll_shuffle l.
Proof.
  intro π. induction π.
  - exact (ax_shuffle b X).
  - exact (tr_shuffle _ _  _ _ s s0 IHπ1 IHπ2).
  - subst. 
    exact (pr_shuffle IHπ).
Qed.

Fixpoint psize_shuffle l (pi : ⊢' l) :=
match pi with
| ax_shuffle _ _  => 1
| pr_shuffle _ _ _ _ pi1 => S (psize_shuffle pi1)
| tr_shuffle _ _ _ _ _ _ _ _ _ _ pi1 pi2 => S (psize_shuffle pi1 + psize_shuffle pi2)
end.

Fixpoint psize_shuffle_nondep l (pi : ⊢'' l) :=
match pi with
| ax_shuffle_nondep _ _  => 1
| pr_shuffle_nondep _ _ _ _ _ _ _ _ pi1 => S (psize_shuffle_nondep pi1)
| tr_shuffle_nondep _ _ _ _ _ _ _ _ _ _  pi1 pi2 => S (psize_shuffle_nondep pi1 +
                                                                psize_shuffle_nondep pi2)
end.

Lemma ax_gen_shuffle A : ⊢' [A; A┴].
Proof.
induction A => //= ; last 2 first.
  by apply ax_shuffle.
  destruct b => //=.
  apply: (@pr_shuffle [::_] _ _ _ ) => //=.
  apply: (@tr_shuffle [::] [::] [::dual A1] [::dual A2] [::] [::dual A1; dual A2] _ _).
      by exists (@MkMerge 0 0 [::] erefl erefl) => //=. 
      by exists (@MkMerge 1 1 [::true; false] erefl erefl).
      all: try rewrite cat0s => //.         
  apply: (@pr_shuffle [::]) => //=.  
  apply: (@tr_shuffle [A1] [A2] [::] [::] [::A1 ; A2]) => //=; last 2 first.
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
    - have tr1 := (tr_shuffle _ _ _ _ s s0 pi1 pi2).
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
    exists (tr_shuffle _ _ _ _ sp sq HApq HBpq).
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
    - have tr1 := (tr_shuffle_nondep _ _ _ _ s s0 pi1 pi2).
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
    exists (tr_shuffle_nondep _ _ _ _ sp sq HApq HBpq).
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

Reserved Notation "⊢_pr l" (at level 65).

Inductive pr_nondep : seq formula -> Type :=
| prr_nondep Γ Δ A B Γ1 Γ2 :
 Γ =  Γ1 ++ [:: A, B & Γ2] -> 
 Δ =  Γ1 ++ A ⅋ B :: Γ2 -> 
 ⊢_pr Γ -> ⊢_pr Δ
where "⊢_pr l" := (pr_nondep l).

(*Inductive parr_equiv Σ : crelation (⊢'' Σ) :=
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
         (@pr_shuffle_nondep Γ Δ' C D (Γ1 ++ [:: A, B & Γ2]) Γ3 eqΓr eqΔ'a π)).*)

Inductive parr_equiv Σ : crelation (⊢_pr Σ) :=
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
         (π : ⊢_pr Γ),
    parr_equiv
      (@prr_nondep Δ Σ C D (Γ1 ++ [:: A ⅋ B & Γ2]) Γ3 eqΔb eqΣ
         (@prr_nondep Γ Δ A B Γ1 (Γ2 ++ [:: C, D & Γ3]) eqΓ eqΔa π))
      (@prr_nondep Δ' Σ A B Γ1 (Γ2 ++ C ⅋ D :: Γ3) eqΔ'b eqΔ'
         (@prr_nondep Γ Δ' C D (Γ1 ++ [:: A, B & Γ2]) Γ3 eqΓr eqΔ'a π)).

Inductive cclos_refl_sym_trans A (R : crelation A) : crelation A :=
| crst_step x y : R x y -> cclos_refl_sym_trans R x y
| crst_refl x : cclos_refl_sym_trans R x x
| crst_sym x y : cclos_refl_sym_trans R x y -> cclos_refl_sym_trans R y x
| crst_trans x y z :
    cclos_refl_sym_trans R x y -> cclos_refl_sym_trans R y z ->
    cclos_refl_sym_trans R x z.

Inductive parr_equiv_gen : forall Σ, crelation (⊢_pr Σ) :=
| peg_base
    (Σ : seq formula)
    (π π' : ⊢_pr Σ) :
    parr_equiv π π' ->
    @parr_equiv_gen Σ π π'
| peg_congr
    (Σ0 Δ : seq formula)
    (A B : formula)
    (Γ1 Γ2 : seq formula)
    (eqΓ : Σ0 = Γ1 ++ [:: A, B & Γ2])
    (eqΔ : Δ = Γ1 ++ A ⅋ B :: Γ2)
    (π π' : ⊢_pr Σ0) :
    @parr_equiv_gen Σ0 π π' ->
    @parr_equiv_gen Δ
      (prr_nondep _ _ Γ1 Γ2 eqΓ eqΔ π)
      (prr_nondep _ _ Γ1 Γ2 eqΓ eqΔ π').

Definition parr_equiv_cl Σ :=
  cclos_refl_sym_trans (@parr_equiv_gen Σ).

Instance parr_equiv_cl_Equivalence (Σ : seq formula) :
    Equivalence (@parr_equiv_cl Σ).
Proof.
constructor.
- move => π.
  rewrite /parr_equiv_cl.
  by apply crst_refl.
- move => π1 π2 H.
  rewrite /parr_equiv_cl.
  rewrite /parr_equiv_cl in H.
  by apply: crst_sym.
- move => π1 π2 π3 H12 H23.
  rewrite /parr_equiv_cl.
  rewrite /parr_equiv_cl in H12.
  rewrite /parr_equiv_cl in H23.
  exact: crst_trans H12 H23.
Qed.

(**)
Lemma parr_equiv_into_cl Σ (π1 π2 : ⊢_pr Σ) :
  parr_equiv π1 π2 -> parr_equiv_cl π1 π2.
Proof.
  move => H.
  constructor.
  by constructor.
Qed.

(* congruence *)
Lemma parr_equiv_cl_cong Σ Δ A B Γ1 Γ2 eqΓ eqΔ (π π' : ⊢_pr Σ) :
  parr_equiv_cl π π' -> parr_equiv_cl
    (@prr_nondep Σ Δ A B Γ1 Γ2 eqΓ eqΔ π)
    (@prr_nondep Σ Δ A B Γ1 Γ2 eqΓ eqΔ π').
Proof.
  move => H.
  elim: H => [p p' hgen | p | p p' IH | p p' p'' _ IH1 _ IH2].
- apply: crst_step.
  exact: peg_congr hgen.
- exact: crst_refl.
- exact: crst_sym.
- apply (crst_trans IH1 IH2).
Qed.

Lemma parr_equiv_sym (Σ : seq formula) π1 π2 : parr_equiv_cl π1 π2 -> @parr_equiv_cl Σ π2 π1.
Proof. by symmetry. Qed.

Lemma parr_equiv_trans  (Σ : seq formula) π1 π2 π3 : 
  parr_equiv_cl π1 π2 -> parr_equiv_cl π2 π3 -> @parr_equiv_cl Σ π1 π3.
Proof. by transitivity π2. Qed.

Lemma test_invol Σ (π1 : ⊢_pr Σ) (π2 : ⊢_pr Σ) (π3 : ⊢_pr Σ) :
  parr_equiv π1 π2 -> parr_equiv π3 π2 -> π1 = π3.
Proof.
move => H1 H2.
destruct H1. dependent destruction H2. subst.
have hΓ : Γ5 = Γ2 by move: (app_inv_tail _ _  _ x2).
subst.
by rewrite (eq_irrelevance eqΓ0 eqΓ) (eq_irrelevance eqΔb0 eqΔb) (eq_irrelevance eqΣ0 eqΣ).
Qed.

Lemma commutation_parr A B C D (π : ⊢_pr [:: A; B; C; D]) :
  parr_equiv
  (prr_nondep _ _ [:: A ⅋ B] [::] erefl erefl (prr_nondep _ _ [::] [:: C; D] erefl erefl π))
  (prr_nondep _ _ [::] [:: C ⅋ D] erefl erefl (prr_nondep _ _ [:: A; B] [::] erefl erefl π)).
Proof.
apply (@parr_equiv_swap _ _ _ _ _ _ _ _ [::] [::]).
Qed.

Lemma middle A B C D ΓlAB ΓrAB ΓlCD ΓrCD :
  ΓlAB ++ A ⅋ B :: ΓrAB = ΓlCD ++ C ⅋ D :: ΓrCD ->
  ΓlAB <> ΓlCD ->
  { Γm & ΓlCD = ΓlAB ++ A ⅋ B :: Γm & ΓrAB = Γm ++ C ⅋ D :: ΓrCD } + 
  { Γm & ΓlAB = ΓlCD ++ C ⅋ D :: Γm & ΓrCD = Γm ++ A ⅋ B :: ΓrAB }.
Proof.
move=> eqABCD neqL.
have Heq : ΓlAB ++ A ⅋ B :: ΓrAB = ΓlCD ++ C ⅋ D :: ΓrCD by congruence.
apply elt_eq_elt_trichotT in Heq as [ [ [Γm H1 H2] | [H1 _] ] | [Γm H1 H2] ] => //=.
  by left; exists Γm => //.
  by right; exists Γm => //=.
Qed.

Inductive rule_equiv (A B C D : formula) Σ : crelation (⊢_pr Σ) :=
| rule_parr_equiv :
  forall Δ_AB Δ_CD Σ'
         ΓlAB ΓrAB ΓlCD ΓrCD
         ΓlCD' ΓrCD' ΓlAB' ΓrAB'
         (eqAB : Σ = ΓlAB ++ A ⅋ B :: ΓrAB)
         (eqCD : Σ = ΓlCD ++ C ⅋ D :: ΓrCD)
         (eqΔ_AB : Δ_AB = ΓlAB ++ [:: A, B & ΓrAB])
         (eqΔ_CD : Δ_CD = ΓlCD ++ [:: C, D & ΓrCD])
         (eqCD_in_AB : Δ_AB = ΓlCD' ++ C ⅋ D :: ΓrCD')
         (eqAB_in_CD : Δ_CD = ΓlAB' ++ A ⅋ B :: ΓrAB')
         (eq1 : Σ' = ΓlCD' ++ [:: C, D & ΓrCD'])
         (eq2 : Σ' = ΓlAB' ++ [:: A, B & ΓrAB'])
         (neq2 : ΓlAB <> ΓlCD)
         (π : ⊢_pr Σ'),
    @rule_equiv A B C D Σ
      (@prr_nondep Δ_AB Σ A B ΓlAB ΓrAB eqΔ_AB eqAB
         (@prr_nondep Σ' Δ_AB C D ΓlCD' ΓrCD' eq1 eqCD_in_AB π))
      (@prr_nondep Δ_CD Σ C D ΓlCD ΓrCD eqΔ_CD eqCD
         (@prr_nondep Σ' Δ_CD A B ΓlAB' ΓrAB' eq2 eqAB_in_CD π)).

From OLlibs Require Import List_more.

Lemma F_up_r A B :  A ⅋ B <> B.
Proof.
induction B in A |- *.
- intros [=].
- intros [=]. subst.
  apply (IHB2 _ H2).
Qed.

Lemma F_up_l A B :  A ⅋ B <> A.
Proof.
induction A in B |- *.
- intros [=].
- intros [=]. subst.
  apply (IHA1 _ H1).
Qed.

Lemma F_up_r2 A B C : A ⅋ (B ⅋ C) <> C.
Proof.
induction C in A, B |- *.
- intros [=].
- intros [=]. subst.
  apply (IHC2 _ _ H2).
Qed.

Lemma F_up_r3 A B C : (B ⅋ C) ⅋ A <> B.
Proof.
induction B in C, A |- *.
- intros [=].
- intros [=]. subst.
  apply (IHB1 _ _ H1).
Qed.


Lemma parr_middle_case A B C Σ Σ' D Δ_AB Δ_CD
         ΓlAB ΓrAB ΓlCD ΓrCD
         ΓlCD' ΓrCD' ΓlAB' ΓrAB'
         (eqAB : Σ = ΓlAB ++ A ⅋ B :: ΓrAB)
         (eqCD : Σ = ΓlCD ++ C ⅋ D :: ΓrCD)
         (eqΔ_AB : Δ_AB = ΓlAB ++ [:: A, B & ΓrAB])
         (eqΔ_CD : Δ_CD = ΓlCD ++ [:: C, D & ΓrCD])
         (eqCD_in_AB : Δ_AB = ΓlCD' ++ C ⅋ D :: ΓrCD')
         (eqAB_in_CD : Δ_CD = ΓlAB' ++ A ⅋ B :: ΓrAB')
         (eq1 : Σ' = ΓlCD' ++ [:: C, D & ΓrCD'])
         (eq2 : Σ' = ΓlAB' ++ [:: A, B & ΓrAB'])
         (neq2 : ΓlAB <> ΓlCD) :
  (ΓlAB = ΓlAB' /\ ΓrCD = ΓrCD') \/ (ΓlCD = ΓlCD' /\ ΓrAB = ΓrAB').
Proof.
subst.
decomp_list_eq eqCD.
- left.
  subst. list_simpl in *.
  have H' : (ΓrCD =  ΓrCD').
  { rewrite 2!app_comm_cons app_assoc in eqCD_in_AB.
    decomp_list_eq eqCD_in_AB; subst; list_simpl in *.
    - exfalso.
      remember (l ++ C :: D :: l0 ++ (C ⅋ D) :: ΓrCD') as l1.
      remember (l ++ (C ⅋ D) :: l0 ++ C :: D :: ΓrCD') as l2.
      assert (l1 <> l2) as H.
      { subst. intros H%app_inv_head. injection H as [= H].
        symmetry in H. apply (F_up_l H). }
      clear Heql1 Heql2.
      decomp_list_eq eq2; subst; list_simpl in *.
      + clear H.
        apply app_inv_head in eqAB_in_CD.
        injection eqAB_in_CD as [= H].
        apply (F_up_l H).
      + injection eq1 as [= ->].
        apply app_inv_head in eqAB_in_CD. injection eqAB_in_CD as [= ->].
        contradiction H. reflexivity.
      + clear H.
        apply app_inv_head in eqAB_in_CD.
        injection eqAB_in_CD as [= H]. symmetry in H.
        apply (F_up_l H).
    - reflexivity.
    - exfalso.
      clear eqCD_in_AB0.
      rewrite app_comm_cons app_assoc in eqAB_in_CD.
      remember (ΓlAB ++ A  ⅋ B :: l) as l1. clear Heql1.
      rewrite 2!app_comm_cons app_assoc in eq2.
      remember (ΓlCD' ++ C :: D :: l0) as l2. clear Heql2.
      decomp_list_eq eq2; subst; list_simpl in *.
      + apply (f_equal (@rev _)) in eqAB_in_CD. list_simpl in eqAB_in_CD.
        apply app_inv_head in eqAB_in_CD.
        injection eqAB_in_CD as [= H]. symmetry in H.
        apply (F_up_r  H).
      + apply (f_equal (@rev _)) in eqAB_in_CD. list_simpl in eqAB_in_CD.
        apply app_inv_head in eqAB_in_CD.
        injection eqAB_in_CD as [= H]. symmetry in H.
        apply (F_up_r H).
      + destruct l3; list_simpl in *.
        * injection eq1 as [= <- <-].
          apply (f_equal (@rev _)) in eqAB_in_CD. list_simpl in eqAB_in_CD.
          apply app_inv_head in eqAB_in_CD.
          injection eqAB_in_CD as [= H]. symmetry in H.
          apply (F_up_r2 H).
        * injection eq1 as [= <- <-].
          apply (f_equal (@rev _)) in eqAB_in_CD. list_simpl in eqAB_in_CD.
          apply app_inv_head in eqAB_in_CD.
          injection eqAB_in_CD as [= H]. symmetry in H.
          apply (F_up_r H). }
  subst.
  rewrite 2!app_comm_cons in eqCD_in_AB. rewrite app_assoc in eqCD_in_AB.
  apply app_inv_tail in eqCD_in_AB.
  subst. list_simpl in *.
  remember (l ++ C :: D :: ΓrCD') as l0. clear Heql0.
  decomp_list_eq eqAB_in_CD; subst; list_simpl in *.
  + apply app_inv_head in eq2.
    injection eq2 as [= HN _]. symmetry in HN.
    exfalso. apply (F_up_l HN).
  + easy.
  + apply app_inv_head in eq2.
    injection eq2 as [= HN _].
    exfalso. apply (F_up_l HN).
- right. subst. by repeat split.
- right.
  subst. list_simpl in *.
  have H' : (ΓrAB = ΓrAB').
  { rewrite 2!app_comm_cons app_assoc in eqAB_in_CD.
    decomp_list_eq eqAB_in_CD; subst; list_simpl in *.
    - exfalso.
      remember (l ++ A :: B :: l0 ++ A ⅋ B :: ΓrAB') as l1.
      remember (l ++ A ⅋ B :: l0 ++ A :: B :: ΓrAB') as l2.
      assert (l1 <> l2) as H.
      { subst. intros H%app_inv_head. injection H as [= H].
        symmetry in H. apply (F_up_l H). }
      clear Heql1 Heql2.
      decomp_list_eq eq2; subst; list_simpl in *.
      + clear H.
        apply app_inv_head in eqCD_in_AB.
        injection eqCD_in_AB as [= H]. symmetry in H.
        apply (F_up_l H).
      + injection eq1 as [= ->].
        apply app_inv_head in eqCD_in_AB. injection eqCD_in_AB as [= ->].
        contradiction H. reflexivity.
      + clear H.
        apply app_inv_head in eqCD_in_AB.
        injection eqCD_in_AB as [= H].
        apply (F_up_l H).
    - reflexivity.
    - exfalso.
      clear eqAB_in_CD0.
      rewrite app_comm_cons app_assoc in eqCD_in_AB.
      remember (ΓlCD ++ C ⅋ D :: l) as l1. clear Heql1.
      rewrite 2!app_comm_cons app_assoc in eq2.
      remember (ΓlAB' ++ A :: B :: l0) as l2. clear Heql2.
      decomp_list_eq eq2; subst; list_simpl in *.
      + destruct l3; list_simpl in *.
        * injection eq1 as [= -> ->].
          apply (f_equal (@rev _)) in eqCD_in_AB. list_simpl in eqCD_in_AB.
          apply app_inv_head in eqCD_in_AB.
          injection eqCD_in_AB as [= H]. symmetry in H.
          apply (F_up_r2  H).
        * injection eq1 as [= -> ->].
          apply (f_equal (@rev _)) in eqCD_in_AB. list_simpl in eqCD_in_AB.
          apply app_inv_head in eqCD_in_AB.
          injection eqCD_in_AB as [= H]. symmetry in H.
          apply (F_up_r H).
      + apply (f_equal (@rev _)) in eqCD_in_AB. list_simpl in eqCD_in_AB.
        apply app_inv_head in eqCD_in_AB.
        injection eqCD_in_AB as [= H]. symmetry in H.
        apply (F_up_r H).
      + apply (f_equal (@rev _)) in eqCD_in_AB. list_simpl in eqCD_in_AB.
        apply app_inv_head in eqCD_in_AB.
        injection eqCD_in_AB as [= H]. symmetry in H.
        apply (F_up_r H). }
  subst.
  rewrite 2!app_comm_cons in eqAB_in_CD. rewrite app_assoc in eqAB_in_CD.
  apply app_inv_tail in eqAB_in_CD.
  subst. list_simpl in *.
  remember (l ++ A :: B :: ΓrAB') as l0. clear Heql0.
  decomp_list_eq eqCD_in_AB; subst; list_simpl in *.
  + apply app_inv_head in eq2.
    injection eq2 as [= HN _].
    exfalso. apply (F_up_l HN).
  + easy.
  + apply app_inv_head in eq2.
    injection eq2 as [= HN _]. symmetry in HN.
    exfalso. apply (F_up_l HN).
Qed.

Ltac solve_f_up H :=
  exfalso;
  apply app_inv_head in H;
  let H_inj := fresh "H_inj" in
  injection H as [= H_inj];
  first
    [ apply (F_up_l H_inj)
    | apply (F_up_r3 H_inj)
    | symmetry in H_inj; apply (F_up_l H_inj)
    | symmetry in H_inj; apply (F_up_r3 H_inj) ].

Lemma decomp_par A B l l' r r' : (A ⅋ B) \notin l ->
(A ⅋ B) \notin l' ->
l ++ (A ⅋ B :: r) = l' ++ (A ⅋ B :: r') ->
l = l' /\ r = r'.
Proof.
move => Hl Hl' H1.
split.
decomp_list_eq H1 => //=.
subst.
exfalso.
rewrite mem_cat in Hl'.
apply/negP: Hl'.
by rewrite negbK mem_head orbT.
subst.
exfalso.
by rewrite mem_cat mem_head orbT in Hl.
decomp_list_eq H1 => //=.
subst.
rewrite mem_cat mem_head orbT in Hl'.
by exfalso.
subst.
rewrite mem_cat mem_head orbT in Hl.
by exfalso.
Qed.

Lemma parr_middle_case2 A B C Σ Σ' D Δ_AB Δ_CD
         ΓlAB ΓrAB ΓlCD ΓrCD
         ΓlCD' ΓrCD' ΓlAB' ΓrAB'
         (eqAB : Σ = ΓlAB ++ A ⅋ B :: ΓrAB)
         (eqCD : Σ = ΓlCD ++ C ⅋ D :: ΓrCD)
         (eqΔ_AB : Δ_AB = ΓlAB ++ [:: A, B & ΓrAB])
         (eqΔ_CD : Δ_CD = ΓlCD ++ [:: C, D & ΓrCD])
         (eqCD_in_AB : Δ_AB = ΓlCD' ++ C ⅋ D :: ΓrCD')
         (eqAB_in_CD : Δ_CD = ΓlAB' ++ A ⅋ B :: ΓrAB')
         (eq1 : Σ' = ΓlCD' ++ [:: C, D & ΓrCD'])
         (eq2 : Σ' = ΓlAB' ++ [:: A, B & ΓrAB'])
         (neq2 : ΓlAB <> ΓlCD) :
  (ΓlAB = ΓlAB' /\ ΓrCD = ΓrCD') \/ (ΓlCD = ΓlCD' /\ ΓrAB = ΓrAB').
Proof.
suff key : forall X Y Z W lXY rXY lZW rZW lZW' rZW' lXY' rXY' Σ Σ',
  Σ  = lXY ++ X⅋Y :: rXY ->
  Σ  = lZW ++ Z⅋W :: rZW ->
  lXY ++ [:: X, Y & rXY] = lZW' ++ Z⅋W :: rZW' ->
  lZW ++ [:: Z, W & rZW] = lXY' ++ X⅋Y :: rXY' ->
  Σ' = lZW' ++ [:: Z, W & rZW'] ->
  Σ' = lXY' ++ [:: X, Y & rXY'] ->
  (exists l, lXY = lZW ++ Z⅋W :: l) ->  (* ZW strictement avant XY *)
  lZW = lZW' /\ rXY = rXY'. (*  lXY = lXY' /\ rZW = rZW'. ? verifier *)
rewrite eqAB in eqCD.
decomp_list_eq eqCD; last 2 first.
by case: neq2.
right.
apply: (key A B C D  ΓlAB ΓrAB ΓlCD ΓrCD  ΓlCD' ΓrCD' ΓlAB' ΓrAB' Σ Σ') => //=.
rewrite eqAB eqCD0 /= -app_assoc /=. 
by rewrite eqCD1.
by rewrite -eqCD_in_AB.
by rewrite -eqAB_in_CD.
by exists l.
left.
apply: (key C D A B ΓlCD ΓrCD ΓlAB ΓrAB ΓlAB' ΓrAB' ΓlCD' ΓrCD' Σ Σ') => //=.
by rewrite eqAB /= eqCD1 /= -eqCD0 /= -app_assoc /=.
by rewrite -eqAB_in_CD.
by rewrite -eqCD_in_AB.
by exists l.
move=> X Y Z W lXY rXY lZW rZW lZW' rZW' lXY' rXY' s s' H1 H2 H3 H4 H5 H6 [l Hl].
subst.
split.
rewrite /= -app_assoc in H2.
move: H2 => /app_inv_head; inversion 1 as [HrZW].
subst.
decomp_list_eq H3 => //=; subst; list_simpl in *.
decomp_list_eq H6 => //=.
subst; list_simpl in *.
all: try by subst; list_simpl in *; by solve_f_up H4.
decomp_list_eq H6 => //=.
all: try by subst; list_simpl in *; solve_f_up H4.
decomp_list_eq H0; subst; list_simpl in *.
decomp_list_eq H6 => //=.
all: try by subst; list_simpl in *; solve_f_up H4.
by [].
decomp_list_eq H6 => //=.
all: try by subst; list_simpl in *; solve_f_up H4.
subst; list_simpl in *.
apply app_inv_head in H4.
injection H4 as [= H].
subst; list_simpl in *.
rewrite /= in H1.
have := congr1 behead H1 => /= H2 /=.
by subst; list_simpl in *; solve_f_up H2.
list_simpl in *; subst.
apply app_inv_head in H2; subst.
decomp_list_eq H3; subst; list_simpl in *.
injection H2 as [=]; subst.
decomp_list_eq H6; subst; list_simpl in *.
all: try by subst; list_simpl in *; solve_f_up H4.
injection H2 as [=]; subst.
decomp_list_eq H4.
subst; list_simpl in *.
apply app_inv_head in H6; injection H6 as [=]. 
destruct l0 as [| f l0'].
injection H1 as [= H_W1 _]; subst; list_simpl.
injection H as [= H_W2 _]; subst.
exfalso; by apply (F_up_l H_W2).
injection H1 as [=].
injection H as [=].
subst; list_simpl in *.
decomp_list_eq H1.
subst; list_simpl in *.
by solve_f_up H2.
done.
all: try by subst; list_simpl in *; solve_f_up H2.
subst; list_simpl in *; solve_f_up H6.
subst; list_simpl in *.
all: try by solve_f_up H6. 
injection H2 as [=]; subst; list_simpl in *.
decomp_list_eq H4; subst; list_simpl in *.
by solve_f_up H6.
subst; list_simpl in *.
apply app_inv_head in H6.
injection H6 as [=]; subst.
all: try solve_f_up H1.
all: by solve_f_up H6.
Qed.

(*Inductive rule_equiv1 (A B C D : formula) : forall (Σ : seq formula), crelation (⊢_pr Σ) :=
| rule_parr_equiv1 : 
  forall (Σ_interne Σ_externe : seq formula)
         (Ctx : ⊢_pr Σ_interne -> ⊢_pr Σ_externe)
         Δ_AB Δ_CD Σ'
         ΓlAB ΓrAB ΓlCD ΓrCD
         ΓlCD' ΓrCD' ΓlAB' ΓrAB'
         Γm
         (eqAB : Σ_interne = ΓlAB ++ A ⅋ B :: ΓrAB) 
         (eqCD : Σ_interne = ΓlCD ++ C ⅋ D :: ΓrCD)
         (eqΔ_AB : Δ_AB = ΓlAB ++ [:: A, B & ΓrAB])
         (eqΔ_CD : Δ_CD = ΓlCD ++ [:: C, D & ΓrCD])
         (eqCD_in_AB : Δ_AB = ΓlCD' ++ C ⅋ D :: ΓrCD')
         (eqAB_in_CD : Δ_CD = ΓlAB' ++ A ⅋ B :: ΓrAB')
         (eq1 : Σ' = ΓlCD' ++ [:: C, D & ΓrCD'])
         (eq2 : Σ' = ΓlAB' ++ [:: A, B & ΓrAB'])
         (neq2 : (ΓlAB = ΓlCD ++ C ⅋ D :: Γm /\ ΓlCD' = ΓlCD /\ ΓrAB' = ΓrAB)
                 \/
                   (ΓlCD = ΓlAB ++ A ⅋ B :: Γm /\ ΓlAB' = ΓlAB /\ ΓrCD' = ΓrCD))
         (π : ⊢_pr Σ'),
    @rule_equiv1 A B C D Σ_externe
      (Ctx (@prr_nondep Δ_AB Σ_interne A B ΓlAB ΓrAB eqΔ_AB eqAB
              (@prr_nondep Σ' Δ_AB C D ΓlCD' ΓrCD' eq1 eqCD_in_AB π)))
      (Ctx (@prr_nondep Δ_CD Σ_interne C D ΓlCD ΓrCD eqΔ_CD eqCD
              (@prr_nondep Σ' Δ_CD A B ΓlAB' ΓrAB' eq2 eqAB_in_CD π))).*)

(* sert a nommer les deux cas *)
Inductive middle_s A B C D ΓlAB ΓrAB ΓlCD ΓrCD : Type :=
| middleABl : forall Γm,
    ΓlCD = ΓlAB ++ A ⅋ B :: Γm ->
    ΓrAB = Γm ++ C ⅋ D :: ΓrCD ->
    middle_s A B C D ΓlAB ΓrAB ΓlCD ΓrCD
| middleCDl : forall Γm,
    ΓlAB = ΓlCD ++ C ⅋ D :: Γm ->
    ΓrCD = Γm ++ A ⅋ B :: ΓrAB ->
    middle_s A B C D ΓlAB ΓrAB ΓlCD ΓrCD.

Lemma middleP A B C D ΓlAB ΓrAB ΓlCD ΓrCD :
  ΓlAB ++ A ⅋ B :: ΓrAB = ΓlCD ++ C ⅋ D :: ΓrCD ->
  ΓlAB <> ΓlCD -> middle_s A B C D ΓlAB ΓrAB ΓlCD ΓrCD.
Proof.
move => eqABCD neqL.
case: (middle A B C D _ _ eqABCD neqL) => [[Γm h1 h2] | [Γm h1 h2]].
  exact: middleABl Γm h1 h2.
  exact: middleCDl Γm h1 h2.
Qed.

Lemma rule_equiv_sym A B C D Σ (π1 π2 : ⊢_pr Σ) :
  rule_equiv A B C D π1 π2 -> rule_equiv C D A B π2 π1.
Proof.
move=> H; dependent destruction H; subst.
apply: rule_parr_equiv => //=.
by symmetry.
Qed.

Lemma commutation_rule A B C D (π : ⊢_pr [:: A; B; C; D]) :
  rule_equiv A B C D
  (prr_nondep A B [::] [:: C ⅋ D] erefl erefl (prr_nondep C D [:: A; B] [::] erefl erefl π))
  (prr_nondep C D [:: A ⅋ B] [::] erefl erefl (prr_nondep A B [::] [:: C; D] erefl erefl π)).
Proof.
apply: rule_parr_equiv.
intros [=]. 
Qed.

Lemma collision_exfalso (L1 L2 R1 R2 R3 R4 : seq.seq formula) X Y :
  size L1 < size L2 ->
  L1 ++ X :: R1 = L2 ++ R2 ->
  L1 ++ X ⅋ Y :: R3 = L2 ++ R4 ->
  False.
Proof.
  move=> Hlt Eq1 Eq2.
  have HX: X = seq.nth X L2 (size L1).
    move: (congr1 (fun s => seq.nth X s (size L1)) Eq1).
    by rewrite !nth_cat Hlt ltnn subnn /=.
  have HP: X ⅋ Y = seq.nth X L2 (size L1).
    move: (congr1 (fun s => seq.nth X s (size L1)) Eq2).
    by rewrite !nth_cat Hlt ltnn subnn /=.
    have H_abs: X = X ⅋ Y.
    by rewrite -HP in HX.
  symmetry in H_abs.
  exact: (F_up_l H_abs).
Qed.

Lemma collision_exfalso2 (L1 L2 R1 R2 R3 R4 : seq.seq formula) X Y C D :
  size L1 = (size L2).+1 ->
  L1 ++ [:: X, Y & R1] = L2 ++ [:: C, D & R2] ->
  L2 ++ [:: C, D & R3] = L1 ++ X ⅋ Y :: R4 ->
  False.
Proof.
  move=> Hsz Eq1 Eq2.
  have HX: X = D.
    move: (congr1 (fun s => seq.nth X s (size L1)) Eq1).
    rewrite !nth_cat !ltnn subnn /= !Hsz /= ltnNge /= leqnSn /= subSn //=.
    by rewrite subnn /=.
  have HP: X ⅋ Y = D.
    move: (congr1 (fun s => seq.nth X s (size L1)) Eq2).
    rewrite !nth_cat ltnn subnn /= Hsz ltnNge leqnSn subSn /=.
    by rewrite subnn.
    done.
  have H_abs: X = X ⅋ Y by rewrite -HX in HP.
  symmetry in H_abs.
  exact: (F_up_l H_abs).
Qed.

Lemma test_invol_rule Σ A B C D (π1 : ⊢_pr Σ) (π2 : ⊢_pr Σ) (π3 : ⊢_pr Σ) :
  rule_equiv A B C D π1 π2 -> rule_equiv A B C D π3 π2 -> π1 = π3.
Proof.
move => H1 H2.
dependent destruction H1; dependent destruction H2; subst.
have eq1s := eq1. symmetry in eq1s.
case : (parr_middle_case _ _ _ _ _ _ _ _ _ _
         eqAB erefl erefl erefl eqCD_in_AB eqAB_in_CD erefl eq1s neq2) => //=.
- move => [H1 H2]. subst.
  have eq0s := eq0. symmetry in eq0s.
  case : (parr_middle_case _ _ _ _ _ _ _ _ _ _
           eqAB0 erefl erefl erefl eqCD_in_AB0 eqAB_in_CD0 erefl eq0s neq0).
    move => [H' H].
    have H'' : (ΓrAB = ΓrAB0).
      move: eqAB eqAB0 => -> E.
      rewrite H' in E.
      move : E => /app_inv_head E.
      by have := congr1 behead E.
    have H''' : (ΓlCD' = ΓlCD'0).
      rewrite -H eq1 in eq0.
      by move : eq0 => /app_inv_tail E.
    subst.
    rewrite (eq_irrelevance eqCD_in_AB eqCD_in_AB0) (eq_irrelevance eq0 eq1).
    by rewrite (eq_irrelevance eqAB eqAB0).
- move => [H1 H2].
  subst.
  have H'' : (ΓrAB' = ΓrAB).
  move: eqAB eqAB0 => -> E.
  move: eq0s eq1s => <- E'.
  exfalso.
  move: eq0 eqAB_in_CD.
  case: (ltngtP (size ΓlAB') (size ΓlCD'0).+1) => [Hlt | Hgt | //].
    move => H H'.
    move: Hlt.
    rewrite leq_eqVlt; move/orP => [/eqP Heq | Hlt'] => //=.
    move: (congr1 (take (size ΓlAB')) H).
    rewrite !take_cat Heq subnn /= !take_size !cats0 => h_eq => //=.
    have Heq_sz : size ΓlAB' = size ΓlCD'0 by move: Heq; case.
    rewrite Heq_sz ltnn subnn /= cats0 in h_eq.
    by case: neq2.
    have Hlt : size ΓlAB' < size ΓlCD'0 by move: Hlt'.
    have Hdrop: drop (size ΓlAB') (ΓlCD'0 ++ [:: C, D & ΓrCD'0])%SEQ = [:: A, B & ΓrAB'].
      by rewrite -H drop_cat ltnn subnn.
    rewrite drop_cat Hlt in Hdrop.
    case Hid: (drop (size ΓlAB') ΓlCD'0) => [| x rem] in Hdrop.
    move: Hlt; rewrite -subn_gt0 -size_drop Hid /=. 
    lia.
    case: Hdrop => Hseq; subst.
    have Hdrop': drop (size ΓlAB') (ΓlCD'0 ++ [:: C, D & ΓrCD'])%SEQ = [:: A ⅋ B & ΓrAB'].
      by rewrite H' drop_cat ltnn subnn.
    rewrite drop_cat Hlt Hid /= in Hdrop'.
    case: Hdrop' => Cycl _.
    move => HH.
    symmetry in Cycl.
    by apply (F_up_l Cycl).
    move => H1 H2.
    have hE': size ΓlCD' + 2 + size ΓrCD' = size ΓlCD'0 + 2 + size ΓrCD'0.
      by move: (congr1 size E'); rewrite !size_cat /=; lia.
    have hH1: size ΓlAB' + 2 + size ΓrAB' = size ΓlCD'0 + 2 + size ΓrCD'0.
      by move: (congr1 size H1); rewrite !size_cat /=; lia.
    have hH2: size ΓlCD'0 + 2 + size ΓrCD' = size ΓlAB' + 1 + size ΓrAB'
      by move: (congr1 size H2); rewrite !size_cat /=; lia.
    have HAB: seq.nth A ΓrCD' (size ΓlAB' - (size ΓlCD'0).+2) = A ⅋ B.
      move: (congr1 (fun s => seq.nth A s (size ΓlAB')) H2).
      rewrite !nth_cat ltnn subnn /=.
      have : (size ΓlAB' < (size ΓlCD'0).+2) = false by move: Hgt; lia.
      move => HH Hif.
      have Hlt : (size ΓlAB' < size ΓlCD'0) = false by move: Hgt; lia.
      have Ha : size ΓlAB' - size ΓlCD'0 = (size ΓlAB' - (size ΓlCD'0).+2).+2 by move: Hgt; lia.
      by rewrite Hlt Ha /= in Hif.
    have h_cycl: B = A ⅋ B.
      move: (congr1 (fun s => seq.nth A s (size ΓlCD' + 2 + (size ΓlAB' - (size ΓlCD'0).+2))) eq1).
      rewrite !nth_cat.
      have -> : (size ΓlCD' + 2 + (size ΓlAB' - (size ΓlCD'0).+2) < size ΓlCD') = false by move: Hgt; lia.
      have -> : (size ΓlCD' + 2 + (size ΓlAB' - (size ΓlCD'0).+2) < size ΓlAB') = false by move: Hgt; lia.
      have -> : (size ΓlCD' + 2 + (size ΓlAB' - (size ΓlCD'0).+2) - size ΓlAB' = 1) by move: Hgt; lia.
      move=> Hsimpl.
      have Hi : size ΓlCD' + 2 + (size ΓlAB' - (size ΓlCD'0).+2) - size ΓlCD' = 
                  (size ΓlAB' - (size ΓlCD'0).+2).+2 by lia.
      by rewrite Hi /= HAB in Hsimpl.
    symmetry in h_cycl.
    by apply (F_up_r h_cycl).
    move => H1 H2 H3.
    have E_ΓlAB' : ΓlAB' = ΓlCD'0 ++ [:: C].
      have Htake : take (size ΓlAB') (ΓlAB' ++ [:: A, B & ΓrAB']) = 
                   take (size ΓlAB') (ΓlCD'0 ++ [:: C, D & ΓrCD'0]) by rewrite H2.
      rewrite take_size_cat // H1 take_cat leqNgt /= !subSn // !subnn !ltnS //= in Htake.
      rewrite Htake //= -addn1.
    by rewrite leq_addr /=.
    have H2_drop : drop (size ΓlCD'0) ((ΓlCD'0 ++ [:: C]) ++ [:: A, B & ΓrAB']) = 
                     drop (size ΓlCD'0) (ΓlCD'0 ++ [:: C, D & ΓrCD'0]).
      by rewrite //= -!catA /= -H2 E_ΓlAB' /= -!catA /=. 
      rewrite -catA /= !drop_cat ltnn subnn /= in H2_drop.
      case: H2_drop => E1 H2_eq.
      have H3_drop : drop (size ΓlCD'0) (ΓlCD'0 ++ [:: C, D & ΓrCD']) = 
                 drop (size ΓlCD'0) ((ΓlCD'0 ++ [:: C]) ++ A ⅋ B :: ΓrAB').
      by rewrite -!catA H3 /= E_ΓlAB' -!catA /=.
    rewrite -catA /= !drop_cat ltnn subnn /= in H3_drop.
    case: H3_drop => E2 H3_eq.
    have HCycl : A = A ⅋ B by rewrite -E1 in E2.
    symmetry in HCycl.
    by apply (F_up_l HCycl).
subst.
have H: ΓlAB' = ΓlAB0.
 move: eqAB eqAB0 => -> E1.
  by move: E1 => /app_inv_tail E1.
subst.
rewrite -eqAB0 in eqAB_in_CD0.
move: eqAB_in_CD0 => /app_inv_head H /=.
case: H => Hcycl _.
symmetry in Hcycl.
exfalso.
by apply (F_up_l Hcycl).
- move => [H1 H2]; subst.
  have eq0s := eq0; symmetry in eq0s.
  case : (parr_middle_case _ _ _ _ _ _ _ _ _ _
           eqAB0 erefl erefl erefl eqCD_in_AB0 eqAB_in_CD0 erefl eq0s neq0) => //=.
  move => [H' H]; subst.
  rewrite -eq0s in eq1s.
  have E' := eq1s.
  have : ΓlAB = ΓlAB'.  
  move: eqAB eqAB0 => -> E.
  move: eq0 eqAB_in_CD.
  case: (ltngtP (size ΓlAB') (size ΓlCD').+1) => [Hlt | Hgt | //] => //=.
    move => H H'.
    move: Hlt.
    rewrite leq_eqVlt; move/orP => [/eqP Heq | Hlt'] => //=.
    move: (congr1 (take (size ΓlAB')) H').
    rewrite !take_cat Heq subnn /= !take_size !cats0 => h_eq => //=.
    have Heq_sz : size ΓlAB' = size ΓlCD' by move: Heq; case.
    rewrite Heq_sz ltnn /= subnn /= cats0 in h_eq.
    by case: neq0.
    have Hlt : size ΓlAB' < size ΓlCD' by move: Hlt'; rewrite ltnS.
    exfalso.
    symmetry in H'.
    exact: (collision_exfalso _ _ _ _ _ _ _ _ Hlt eq1 H').
  move=> H1 H2.
  exfalso.
  have Hsize : size ΓlAB' = (size ΓlAB).+1.
    have H1_sz := f_equal size eq1.
    have H2_sz := f_equal size eqCD_in_AB.
    rewrite !size_cat /= in H1_sz H2_sz.
    by lia.
  have HE_struct : ΓlAB' = ΓlAB ++ [:: A ⅋ B].
    have H_take := f_equal (take (size ΓlAB')) E.
    rewrite (catA ΓlAB [:: A ⅋ B] ΓrAB') in H_take.
    rewrite Hsize /= in H_take.
    rewrite !take_size_cat /= in H_take.
    by symmetry.
    done.
    by rewrite size_cat /=; lia.
 have Hk : size ΓlCD' < size ΓlAB by move: Hgt; rewrite Hsize.
 symmetry in eqCD_in_AB.
 list_simpl in *.
 rewrite HE_struct -catA /= in eqAB_in_CD0.
 exact: (collision_exfalso ΓlCD' ΓlAB (D :: ΓrCD'0) (A ⅋ B :: A ⅋ B :: ΓrAB') ΓrCD' (A :: B :: ΓrAB') C D Hk eqAB_in_CD0 eqCD_in_AB).
move=> H1 H2 H3.
have Hsize : size ΓlAB' = (size ΓlAB).+1.
  have H1_sz := f_equal size eq1.
  have H2_sz := f_equal size eqCD_in_AB.
  rewrite !size_cat /= in H1_sz H2_sz.
  by lia.
  have HE_struct : ΓlAB' = ΓlAB ++ [:: A ⅋ B].
    have H_take := f_equal (take (size ΓlAB')) E.
    rewrite (catA ΓlAB [:: A ⅋ B] ΓrAB') in H_take.
    rewrite Hsize /= in H_take.
    rewrite !take_size_cat /= in H_take.
    by symmetry.
    done.
    by rewrite size_cat /=; lia.
    exfalso.
    exact: (collision_exfalso2 _ _ _ _ _ _ A B C D H1 eq1 H3).
move => H.
have H1 : ΓrAB' = ΓrAB0.
subst.
move : eqAB eqAB0 => -> E1.
move : E1 => /app_inv_head E1.
by have := congr1 behead E1.
subst.
have H1 : ΓlCD' = ΓlCD'0.
move : eqAB0 eqAB_in_CD0 => <- E2.
exfalso.
  have H_len := f_equal size E2.
  rewrite !size_cat /= in H_len.
  by lia.
subst.
have H2 : ΓrCD' = ΓrCD'0.
move : E' => /app_inv_head E1.
have := congr1 behead E1 => /=.
congruence.
subst.
rewrite (eq_irrelevance eqCD_in_AB eqCD_in_AB0) (eq_irrelevance eq0 eq1).
  by rewrite (eq_irrelevance eqAB eqAB0).
  move => [H1 H2].
  subst.
  have CD:  ΓrCD'0 = ΓrCD'.
  move: eq1s eq0s => <- E.
  move : E => /app_inv_head E.
  congruence.
  subst.
  have AB: ΓlAB0 = ΓlAB.
  move: eqAB eqAB0 => -> E.
  move : E => /app_inv_tail E.
  by have := congr1 behead E.
  subst.
  rewrite (eq_irrelevance eqCD_in_AB eqCD_in_AB0) (eq_irrelevance eq0 eq1).
  by rewrite (eq_irrelevance eqAB eqAB0).
Qed.

Fixpoint fsize (f : formula) : nat :=
  match f with
  | var _ _ => 1
  | bin _ f1 f2 => (fsize f1 + fsize f2).+1
  end.

Definition lt_all (A : formula) (As : seq.seq formula) :=
  forall X, X \in As ->  fsize X < fsize A.
Notation "As ≪ A" := (lt_all A As) (at level 70).

Definition msubst (Γ : seq.seq formula) (F : formula) (θ Σ : seq.seq formula) :=
  exists Δl Δr,
    Γ = Δl ++ [:: F] ++ Δr /\
      Σ = Δl ++ θ ++ Δr.

Lemma parr_equiv_decomp (A C : formula) (Ā C̄ Γl Γm Γr : seq.seq formula) :
    Ā ≪ A ->
    C̄ ≪ C ->
    forall Σ,
      msubst (Γl ++ A :: Γm ++ C̄ ++ Γr) A Ā Σ ->
      msubst (Γl ++ Ā ++ Γm ++ C :: Γr) C C̄ Σ ->
      (exists Δr, Σ = Γl ++ Ā ++ Δr) /\
      (exists Δl, Σ = Δl ++ C̄ ++ Γr).
Proof.
  move=> hltA hltC Σ [Δl [Δr [hΓ hΣ]]] [Δl' [Δr' [hΓ' hΣ']]].
  split.
  subst.
  rewrite /= in hΓ hΓ'.
  case: (elt_eq_elt_trichotT _ _ _ _ _ _ hΓ) => [[[l2' [h1 h2]] | [h1 [_ h3]]] | [l4' [h1 h2]]] => //=.
  list_simpl in *; subst.
  rewrite /= catA catA in hΓ'.
  case: (elt_eq_elt_trichotT _ _ _ _ _ _ hΓ') => [[[l2'' [h1 h2']] | [h1 [_ h3]]] | [l4' [h1 h2']]] => //=.
  list_simpl in *; subst.
  clear  hΓ'.
  rewrite hΣ' /= -!catA /= -!app_assoc /=.
  by exists (Γm ++ (C :: (l2'' ++ C̄ ++ Δr'))).
  list_simpl in *; subst.
  rewrite hΣ' /= -!catA /= -!app_assoc /=.
  by exists ( Γm ++ C̄ ++ Δr').
  list_simpl in *; subst.          
  admit.
  list_simpl in *; subst.
  by exists ((Γm ++ C̄ ++ Γr)).
  list_simpl in *; subst.
  clear hΓ.
  rewrite -!catA /= in hΓ'.
  rewrite /=.
  rewrite hΣ' /=.
  admit.
  list_simpl in *; subst.
  rewrite hΣ'.
  exists Δl'.
  rewrite catA catA in hΓ'. 
  case: (elt_eq_elt_trichotT _ _ _ _ _ _ hΓ') => [[[l2'' [h1 h2']] | [h1 [_ h3]]] | [l4' [h1 h2']]] => //=.
  list_simpl in *; subst.
  clear  hΓ'.
  exfalso.
  list_simpl in *.
  admit.
  list_simpl in *; subst.
  done.
  list_simpl in *; subst.
Admitted.

Lemma test_invol_rule1 Σ A B C D (π1 : ⊢_pr Σ) (π2 : ⊢_pr Σ) (π3 : ⊢_pr Σ) :
  rule_equiv A B C D π1 π2 -> rule_equiv A B C D π3 π2 -> π1 = π3.
Proof.
move => H1 H2.
dependent destruction H1; dependent destruction H2; subst.
have eq1s := eq1; symmetry in eq1s.
have Hms1 : msubst (ΓlAB ++ [:: A, B & ΓrAB]) (C ⅋ D) [:: C; D]
              (ΓlAB' ++ [:: A, B & ΓrAB']).
  by exists ΓlCD', ΓrCD'.
case: (middleP C D A B  _ _ eqAB).
case: (middleP C D A B  _ _ eqAB0).
by symmetry.
move => Γm eqAB1 eqCD1.
list_simpl in *; subst.
by symmetry.
move => Γm eqAB1 eqCD1.
by symmetry.
move => Γm eqAB1 eqCD1.
list_simpl in *; subst.
have HltA : [:: A; B] ≪ A ⅋ B.
rewrite /lt_all /=.
move => X.
rewrite !inE /=.
move=> /orP[/eqP-> | /eqP->]; rewrite ltnS; [exact: leq_addr | exact: leq_addl].
have HltC : [:: C; D] ≪ C ⅋ D.
rewrite /lt_all /=.
move => X.
rewrite !inE /=.
move=> /orP[/eqP-> | /eqP->]; rewrite ltnS; [exact: leq_addr | exact: leq_addl].
case (@parr_equiv_decomp (C ⅋ D)(A ⅋ B) [:: C; D] [:: A; B]
        ΓlCD Γm ΓrAB HltC HltA (ΓlAB' ++ [:: A, B & ΓrAB'])) => //=.
by rewrite -catA in Hms1.
by exists ΓlAB', ΓrAB'.
move => [Δr Hm] [Δl Hm1].
rewrite Hm in Hm1.
Admitted.
