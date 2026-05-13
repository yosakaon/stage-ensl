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

(*Definition parr_equiv_cl Σ (π1 π2 : ⊢'' Σ) : Type :=
  forall (R : forall Σ, crelation (⊢'' Σ)),  
    (forall Σ, Equivalence (R Σ)) ->
    (forall Σ π π', parr_equiv π π' -> R Σ π π') ->
    (forall Σ0 Δ A B Γ1 Γ2 eqΓ eqΔ π π',
        R Σ0 π π' ->
        R Δ (@pr_shuffle_nondep Σ0 Δ A B Γ1 Γ2 eqΓ eqΔ π)
             (@pr_shuffle_nondep Σ0 Δ A B Γ1 Γ2 eqΓ eqΔ π')) ->
    R Σ π1 π2.*)

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
(*
         (neq2 : (ΓlAB = ΓlCD ++ C ⅋ D :: Γm /\ ΓlCD' = ΓlCD /\ ΓrAB' = ΓrAB)
                 \/
                   (ΓlCD = ΓlAB ++ A ⅋ B :: Γm /\ ΓlAB' = ΓlAB /\ ΓrCD' = ΓrCD))
*)
         (π : ⊢_pr Σ'),
    @rule_equiv A B C D Σ
      (@prr_nondep Δ_AB Σ A B ΓlAB ΓrAB eqΔ_AB eqAB
         (@prr_nondep Σ' Δ_AB C D ΓlCD' ΓrCD' eq1 eqCD_in_AB π))
      (@prr_nondep Δ_CD Σ C D ΓlCD ΓrCD eqΔ_CD eqCD
         (@prr_nondep Σ' Δ_CD A B ΓlAB' ΓrAB' eq2 eqAB_in_CD π)).

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
(*
subst.
decomp_list_eq eqCD.
- left.
  subst. list_simpl in *.
  assert (rCD = rCD') as H'.
  { rewrite 2 app_comm_cons, app_assoc in eqΔ_CD'.
    decomp_list_eq eqΔ_CD'; subst; list_simpl in *.
    - exfalso.
      remember (l ++ C :: D :: l0 ++ F C D :: rCD') as l1.
      remember (l ++ F C D :: l0 ++ C :: D :: rCD') as l2.
      assert (l1 <> l2) as H.
      { subst. intros H%app_inv_head. injection H as [= H].
        symmetry in H. apply (F_up_l _ _ H). }
      clear Heql1 Heql2.
      decomp_list_eq eq2; subst; list_simpl in *.
      + clear H.
        apply app_inv_head in eqΔ_AB'.
        injection eqΔ_AB' as [= H].
        apply (F_up_l _ _ H).
      + injection eq1 as [= ->].
        apply app_inv_head in eqΔ_AB'. injection eqΔ_AB' as [= ->].
        contradiction H. reflexivity.
      + clear H.
        apply app_inv_head in eqΔ_AB'.
        injection eqΔ_AB' as [= H]. symmetry in H.
        apply (F_up_l _ _ H).
    - reflexivity.
    - exfalso.
      clear eqΔ_CD'0.
      rewrite app_comm_cons, app_assoc in eqΔ_AB'.
      remember (lAB ++ F A B :: l) as l1. clear Heql1.
      rewrite 2 app_comm_cons, app_assoc in eq2.
      remember (lCD' ++ C :: D :: l0) as l2. clear Heql2.
      decomp_list_eq eq2; subst; list_simpl in *.
      + apply (f_equal (@rev _)) in eqΔ_AB'. list_simpl in eqΔ_AB'.
        apply app_inv_head in eqΔ_AB'.
        injection eqΔ_AB' as [= H]. symmetry in H.
        apply (F_up_r _ _ H).
      + apply (f_equal (@rev _)) in eqΔ_AB'. list_simpl in eqΔ_AB'.
        apply app_inv_head in eqΔ_AB'.
        injection eqΔ_AB' as [= H]. symmetry in H.
        apply (F_up_r _ _ H).
      + destruct l3; list_simpl in *.
        * injection eq1 as [= <- <-].
          apply (f_equal (@rev _)) in eqΔ_AB'. list_simpl in eqΔ_AB'.
          apply app_inv_head in eqΔ_AB'.
          injection eqΔ_AB' as [= H]. symmetry in H.
          apply (F_up_r2 _ _ _ H).
        * injection eq1 as [= <- <-].
          apply (f_equal (@rev _)) in eqΔ_AB'. list_simpl in eqΔ_AB'.
          apply app_inv_head in eqΔ_AB'.
          injection eqΔ_AB' as [= H]. symmetry in H.
          apply (F_up_r _ _ H). }
  subst.
  rewrite 2 app_comm_cons in eqΔ_CD'. rewrite app_assoc in eqΔ_CD'.
  apply app_inv_tail in eqΔ_CD'.
  subst. list_simpl in *.
  remember (l ++ C :: D :: rCD') as l0. clear Heql0.
  decomp_list_eq eqΔ_AB'; subst; list_simpl in *.
  + apply app_inv_head in eq2.
    injection eq2 as [= HN _]. symmetry in HN.
    exfalso. apply (F_up_l _ _ HN).
  + easy.
  + apply app_inv_head in eq2.
    injection eq2 as [= HN _].
    exfalso. apply (F_up_l _ _ HN).

- right. left. subst. repeat split.

- right. right.
  subst. list_simpl in *.
  assert (rAB = rAB') as H'.
  { rewrite 2 app_comm_cons, app_assoc in eqΔ_AB'.
    decomp_list_eq eqΔ_AB'; subst; list_simpl in *.
    - exfalso.
      remember (l ++ A :: B :: l0 ++ F A B :: rAB') as l1.
      remember (l ++ F A B :: l0 ++ A :: B :: rAB') as l2.
      assert (l1 <> l2) as H.
      { subst. intros H%app_inv_head. injection H as [= H].
        symmetry in H. apply (F_up_l _ _ H). }
      clear Heql1 Heql2.
      decomp_list_eq eq2; subst; list_simpl in *.
      + clear H.
        apply app_inv_head in eqΔ_CD'.
        injection eqΔ_CD' as [= H]. symmetry in H.
        apply (F_up_l _ _ H).
      + injection eq1 as [= ->].
        apply app_inv_head in eqΔ_CD'. injection eqΔ_CD' as [= ->].
        contradiction H. reflexivity.
      + clear H.
        apply app_inv_head in eqΔ_CD'.
        injection eqΔ_CD' as [= H].
        apply (F_up_l _ _ H).
    - reflexivity.
    - exfalso.
      clear eqΔ_AB'0.
      rewrite app_comm_cons, app_assoc in eqΔ_CD'.
      remember (lCD ++ F C D :: l) as l1. clear Heql1.
      rewrite 2 app_comm_cons, app_assoc in eq2.
      remember (lAB' ++ A :: B :: l0) as l2. clear Heql2.
      decomp_list_eq eq2; subst; list_simpl in *.
      + destruct l3; list_simpl in *.
        * injection eq1 as [= -> ->].
          apply (f_equal (@rev _)) in eqΔ_CD'. list_simpl in eqΔ_CD'.
          apply app_inv_head in eqΔ_CD'.
          injection eqΔ_CD' as [= H]. symmetry in H.
          apply (F_up_r2 _ _ _ H).
        * injection eq1 as [= -> ->].
          apply (f_equal (@rev _)) in eqΔ_CD'. list_simpl in eqΔ_CD'.
          apply app_inv_head in eqΔ_CD'.
          injection eqΔ_CD' as [= H]. symmetry in H.
          apply (F_up_r _ _ H).
      + apply (f_equal (@rev _)) in eqΔ_CD'. list_simpl in eqΔ_CD'.
        apply app_inv_head in eqΔ_CD'.
        injection eqΔ_CD' as [= H]. symmetry in H.
        apply (F_up_r _ _ H).
      + apply (f_equal (@rev _)) in eqΔ_CD'. list_simpl in eqΔ_CD'.
        apply app_inv_head in eqΔ_CD'.
        injection eqΔ_CD' as [= H]. symmetry in H.
        apply (F_up_r _ _ H). }
  subst.
  rewrite 2 app_comm_cons in eqΔ_AB'. rewrite app_assoc in eqΔ_AB'.
  apply app_inv_tail in eqΔ_AB'.
  subst. list_simpl in *.
  remember (l ++ A :: B :: rAB') as l0. clear Heql0.
  decomp_list_eq eqΔ_CD'; subst; list_simpl in *.
  + apply app_inv_head in eq2.
    injection eq2 as [= HN _].
    exfalso. apply (F_up_l _ _ HN).
  + easy.
  + apply app_inv_head in eq2.
    injection eq2 as [= HN _]. symmetry in HN.
    exfalso. apply (F_up_l _ _ HN).
*)
Admitted.

Inductive rule_equiv1 (A B C D : formula) : forall (Σ : seq formula), crelation (⊢_pr Σ) :=
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
              (@prr_nondep Σ' Δ_CD A B ΓlAB' ΓrAB' eq2 eqAB_in_CD π))).

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

Lemma rule_equiv_sym1 A B C D Σ (π1 π2 : ⊢_pr Σ) :
  rule_equiv1 A B C D π1 π2 -> rule_equiv1 C D A B π2 π1.
Proof.
move=> H; dependent destruction H; subst.
apply rule_parr_equiv1 with (Γm := Γm) => //=.
case: neq2 => [H | H].
  right; exact: H.
  left; exact: H.
Qed.

Lemma commutation_rule A B C D (π : ⊢_pr [:: A; B; C; D]) :
  rule_equiv A B C D
  (prr_nondep A B [::] [:: C ⅋ D] erefl erefl (prr_nondep C D [:: A; B] [::] erefl erefl π))
  (prr_nondep C D [:: A ⅋ B] [::] erefl erefl (prr_nondep A B [::] [:: C; D] erefl erefl π)).
Proof.
apply: rule_parr_equiv.
intros [=]. (* ss_reflect style? *)
Qed.

Lemma commutation_rule1 A B C D (π : ⊢_pr [:: A; B; C; D]) :
  rule_equiv1 A B C D
  (prr_nondep A B [::] [:: C ⅋ D] erefl erefl (prr_nondep C D [:: A; B] [::] erefl erefl π))
  (prr_nondep C D [:: A ⅋ B] [::] erefl erefl (prr_nondep A B [::] [:: C; D] erefl erefl π)).
Proof.
apply rule_parr_equiv1 with (Ctx := fun x => x) (Γm := [::]).
by right; split => //=. 
Qed.

Lemma test_invol_rule Σ A B C D (π1 : ⊢_pr Σ) (π2 : ⊢_pr Σ) (π3 : ⊢_pr Σ) :
  rule_equiv A B C D π1 π2 -> rule_equiv A B C D π3 π2 -> π1 = π3.
Proof.
move => H1 H2.
dependent destruction H1; dependent destruction H2; subst.
have eq1s := eq1. symmetry in eq1s.
case : (parr_middle_case _ _ _ _ _ _ _ _ _ _
         eqAB erefl erefl erefl eqCD_in_AB eqAB_in_CD erefl eq1s neq2).
- move => [H1 H2]. subst.
  have eq0s := eq0. symmetry in eq0s.
  case : (parr_middle_case _ _ _ _ _ _ _ _ _ _
           eqAB0 erefl erefl erefl eqCD_in_AB0 eqAB_in_CD0 erefl eq0s neq0).
    move => [H' H].
(*
  case : neq2 => [ [H ] [H1 H2] | H] => //=..
  case: neq0 => [[H'] [H1' H2'] | H'] => //=.
*)
    have H'' : (ΓrAB = ΓrAB0) by admit.
    have H''' : (ΓlCD' = ΓlCD'0) by admit.
    subst.
    rewrite (eq_irrelevance eqCD_in_AB eqCD_in_AB0) (eq_irrelevance eq0 eq1).
    by rewrite (eq_irrelevance eqAB eqAB0).
    clear eq1s eq0s.
    exfalso. admit.
- move => [H1 H2]. subst.
  have eq0s := eq0. symmetry in eq0s.
  case : (parr_middle_case _ _ _ _ _ _ _ _ _ _
           eqAB0 erefl erefl erefl eqCD_in_AB0 eqAB_in_CD0 erefl eq0s neq0).
    move => [H' H]. subst.
    exfalso. admit.
move => [H' H]. subst.
have Eq_lAB : ΓlAB0 = ΓlAB by admit.
subst ΓlAB0.
have Eq_rCD' : ΓrCD'0 = ΓrCD' by admit.
subst ΓrCD'.
rewrite (eq_irrelevance eqCD_in_AB eqCD_in_AB0) (eq_irrelevance eq0 eq1).
by rewrite (eq_irrelevance eqAB eqAB0).
Admitted.

Lemma rule_equiv1_cong : forall Σ Σ' A B C D Γl Γr
  (eq_S : Σ = Γl ++ A ⅋ B :: Γr)
  (eq_S' : Σ' = Γl ++ [:: A, B & Γr])
  (π1 π2 : ⊢_pr Σ'),
  rule_equiv1 A B C D π1 π2 -> 
  rule_equiv1 A B C D (prr_nondep A B Γl Γr eq_S' eq_S π1) (prr_nondep A B Γl Γr eq_S' eq_S π2).
Proof.
intros.
subst.
dependent destruction X => //=.
subst.
apply rule_parr_equiv1 with (Ctx := fun x => prr_nondep A B Γl Γr erefl erefl (Ctx x)) (Γm := Γm) => //=.
Qed.

(* pas possible ?*)
Lemma test_invol_rule1 Σ A B C D (π1 : ⊢_pr Σ) (π2 : ⊢_pr Σ) (π3 : ⊢_pr Σ) :
  rule_equiv1 A B C D π1 π2 -> rule_equiv1 A B C D π3 π2 -> π1 = π3.
Proof.
move => H1 H2.
dependent destruction H1; dependent destruction H2; subst.
case : neq2 => [ [H ] [H1 H2] | H] => //=.
case: neq0 => [[H'] [H1' H2'] | H'] => //=.
have HlAB : ΓlAB = ΓlAB0.
rewrite H' H.
congr(_++_).
Abort.
