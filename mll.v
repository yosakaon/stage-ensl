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

(** * Preliminaries *)

Notation "l ∈ m ⧢ n" := (shuffleT m n l) (at level 65).

(** * Formulas *)

Definition atom := nat : Type.

Inductive formula := var (_ : bool) (_ : atom) | bin (_ : bool) (_ _ : formula).
Infix "⊗" := (bin true) (at level 34).
Infix "⅋" := (bin false) (at level 35).

Coercion pvar := var true.

Reserved Notation "A ┴".
Fixpoint dual A :=
match A with
| var b X => var (negb b) X
| bin b B C => bin (negb b) (B┴) (C┴)
end
where "A ┴" := (dual A) (only parsing).
Notation "A 'ᗮ'" := (dual A) (left associativity, format "A ᗮ").

Lemma bidual A : A┴┴ = A.
Proof.
rewrite /A┴┴.
induction A => //; last 2 first.
  by rewrite negb_involutive.
- by rewrite IHA1 IHA2 negb_involutive.
Qed.

Arguments bidual {_}, _.

Fixpoint fsize A :=
match A with
| var _ _ => 1
| B ⊗ C | B ⅋ C => S (fsize B + fsize C)
end.

Lemma fsize_dual A : fsize A┴ = fsize A.
Proof.
rewrite /A┴.
induction A => //=.
by rewrite IHA2 IHA1 negb_if.
Qed.
(** * Proofs *)

Reserved Notation "⊢ l" (at level 65).
Inductive mll : list formula -> Type :=
| ax b X : ⊢ [var b X; var (negb b) X]
| tr l1 m1 l2 m2 n1 n2 A B :
  n1 ∈ l1 ⧢ m1 -> n2 ∈ l2 ⧢ m2 -> ⊢ l1 ++ A :: l2 -> ⊢ m1 ++ B :: m2 -> ⊢ n1 ++ A ⊗ B :: n2
| pr l1 A B l2 : ⊢ l1 ++ A :: B :: l2 -> ⊢ l1 ++ A ⅋ B :: l2
where "⊢ l" := (mll l).
Arguments ax {_ _}, [_] _, _ _.
Arguments pr [_ _ _ _] _, _ [_ _ _] _, _ _ _ [_] _.
Arguments tr [_ _ _ _ _ _ _ _ _ _] _ _, [_ _ _ _ _ _ _ _] _ _ _ _, _ _ _ _ [_ _ _ _] _ _ _ _.

Scheme Equality for formula.
Definition formula_dec_bl := internal_formula_dec_bl.
Definition formula_dec_lb := internal_formula_dec_lb.

Lemma formula_eqP : Equality.axiom formula_beq.
Proof.
move=> x y.
apply: (iffP idP).
exact: formula_dec_bl.
exact: formula_dec_lb.
Qed.

HB.instance Definition _ := hasDecEq.Build formula formula_eqP.

Reserved Notation "⊢' l" (at level 65).

Fixpoint psize l (pi : ⊢ l) :=
match pi with
| ax _ _  => 1
| pr _ _ _ _ pi1 => S (psize pi1)
| tr _ _ _ _ _ _ _ _ _ _ pi1 pi2=> S (psize pi1 + psize pi2)
end.

Instance ex : Proper (@PermutationT _ ==> iffT) mll.
Proof.
move => l1 l2 Hperm.
split => Hd.
  move: l2 Hperm.
  elim: Hd.
  - move=> b X l2 h1.
    case: (PermutationT_length_2_inv h1) => ->.
     exact: ax.
     by rewrite -{2}(negbK b); exact: ax.
  - (*tr*)
    move=> l0 m1 l3 m2 n1 n2 A B s s0 H1 IH1 H2 IH2 l' Hp. 
    have Hpinv : PermutationT l' (A ⊗ B :: (n1 ++ n2)).
      eapply PermutationT_trans; [exact: PermutationT_sym Hp |].
      exact: PermutationT_sym (PermutationT_middle _ _ (A ⊗ B)).
    have [[p q] epq] := @PermutationT_vs_cons_inv _ (A ⊗ B) _ _ Hpinv.
    subst l'.
    have Hnn := shuffleT_app_app s s0.
    have Hpq := PermutationT_sym (PermutationT_cons_app_inv _ _ (PermutationT_sym Hpinv)).
    have [[l' m'] [Hl' Hm'] Hpq_sh] := @PermutationT_shuffleT formula _ _ _ _ Hnn (PermutationT_sym Hpq).
    have [[[[l0' l3'] m1'] m2'] [Hl0 Hm1] [sp sq]] := @shuffleT_app_inv formula _ _ p q Hpq_sh.
    apply (@tr _ _ _ _ _ _ _ _ sp sq).
    by apply: IH1; apply: (@PermutationT_app_middle formula [:: A] l0 l3 l0' l3'); rewrite Hl0 in Hl'.
    by apply: IH2; apply: (@PermutationT_app_middle formula [:: B] m1 m2 m1' m2'); rewrite Hm1 in Hm'.
- (* pr *)
  move=> l0 A B l2 Hpr IH l3 Hp.
  have Hpinv : PermutationT l3 (A ⅋ B :: (l0 ++ l2)).
    eapply PermutationT_trans; [exact: PermutationT_sym Hp |].
    exact: (PermutationT_sym (PermutationT_middle _ _ (A ⅋ B))).
  have [[p q] epq]:= (@PermutationT_vs_cons_inv _ (A ⅋ B) _ _ Hpinv).
  subst l3.
  apply: pr; apply: IH.
  have Hctx := PermutationT_cons_app_inv _ _ ((PermutationT_sym Hpinv)).
  by apply: @PermutationT_app_middle formula (A :: B :: nil) l0 l2 p q Hctx => //=.
- move: l1 Hperm.
  elim: Hd.
  - move => b X l1 Hp.
    apply PermutationT_sym in Hp.
    case: (PermutationT_length_2_inv Hp) => ->.
     exact: ax.
     by rewrite -{2}(negbK b); exact: ax.
  - move => l0 m0 l1 m1 n1 n2 A B s s1 H1 IH1 H2 IH2 l' Hp. (* tr *)
      have Hpinv' : PermutationT l' (A ⊗ B :: (n1 ++ n2)).
        eapply PermutationT_trans; [exact: Hp |].
        exact: PermutationT_sym (PermutationT_middle _ _ (A ⊗ B)).
      have [[p q] epq] := @PermutationT_vs_cons_inv _ (A ⊗ B) _ _ Hpinv'.
      subst l'.
      have Hnn := shuffleT_app_app s s1.
      have Hpq := PermutationT_sym (PermutationT_cons_app_inv _ _ (PermutationT_sym Hpinv')).
      have [[l' m'] [Hl' Hm'] Hpq_sh] := @PermutationT_shuffleT formula _ _ _ _ Hnn (PermutationT_sym Hpq).
      have [[[[l0' l3'] m1'] m2'] [Hl0 Hm1] [sp sq]] := @shuffleT_app_inv formula _ _ p q Hpq_sh.
      apply (@tr _ _ _ _ _ _ _ _ sp sq).
      by apply: IH1; apply PermutationT_sym; apply (@PermutationT_app_middle formula [:: A] l0 l1 l0' l3'); rewrite Hl0 in Hl'.
      by apply: IH2; apply PermutationT_sym; apply (@PermutationT_app_middle formula [:: B] m0 m1 m1' m2'); rewrite Hm1 in Hm'.
    - move => l1 A B l0 H1 IH1 l3 Hp.
      have Hpinv : PermutationT l3 (A ⅋ B :: (l1 ++ l0)).
        eapply PermutationT_trans; [exact: Hp |].
        exact: PermutationT_sym (PermutationT_middle _ _ (A ⅋ B)).
      have [[p q] epq]:= (@PermutationT_vs_cons_inv _ (A ⅋ B) _ _ Hpinv).
  subst l3.
  apply: pr; apply: IH1.
  have Hctx := PermutationT_cons_app_inv _ _ ((PermutationT_sym Hpinv)).
  by apply : PermutationT_sym ((@PermutationT_app_middle formula (A :: B :: nil) l1 l0 p q Hctx)). 
Qed.

Lemma ex_size l' l (p : PermutationT l l') (pi : ⊢ l) : { pi' : ⊢ l' | psize pi' = psize pi }.
Proof.
induction pi in l', p |- *.
  - destruct (PermutationT_length_2_inv p) as [-> | ->] => //=. (* ax *)
    - by exists (ax b X) => //.
    - by rewrite (negb_involutive_reverse (b)) negb_involutive; exists (ax (~~ b) X).                              
  - (* tr *)
    have Hpinv : PermutationT l' (A ⊗ B :: (n1 ++ n2)).
      eapply PermutationT_trans; [exact: PermutationT_sym p |].
      exact: PermutationT_sym (PermutationT_middle _ _ (A ⊗ B)).
    have Hdec := (@PermutationT_vs_cons_inv _ (A ⊗ B) _ _ Hpinv).
    destruct Hdec as [[p' q]].
    subst l'.
    have Hpq := PermutationT_sym (PermutationT_cons_app_inv _ _ (PermutationT_sym Hpinv)).
    have Hnn := shuffleT_app_app s s0.
    have [[l' m'] [Hl' Hm'] Hpq_sh] := @PermutationT_shuffleT formula _ _ _ _ Hnn (PermutationT_sym Hpq).
    have [[[[l0' l3'] m1'] m2'] [Hl0 Hm1] [sp sq]] := @shuffleT_app_inv formula _ _ p' q Hpq_sh.
    have HpermA : PermutationT (l1 ++ A :: l2) (l0' ++ A :: l3'). 
      by apply: (@PermutationT_app_middle formula [:: A] l1 l2 l0' l3'); rewrite Hl0 in Hl'.
      have HpermB : PermutationT (m1 ++ B :: m2) (m1' ++ B :: m2'). 
        by apply: (@PermutationT_app_middle formula [:: B] m1 m2 m1' m2'); rewrite Hm1 in Hm'.
      have [HApq HsizeA] := IHpi1 _ HpermA.
      have [HBpq HsizeB] := IHpi2 _ HpermB.
      exists (tr sp sq HApq HBpq) => //=.
      by f_equal; rewrite HsizeA HsizeB.
  - (* pr *)
    have Hpinv : PermutationT l' (A ⅋ B :: (l1 ++ l2)).
        eapply PermutationT_trans; [exact: PermutationT_sym p |].
        exact: PermutationT_sym (PermutationT_middle _ _ (A ⅋ B)).
     have [[p' q] epq] := @PermutationT_vs_cons_inv _ (A ⅋ B)_ _ Hpinv.
     subst l'.
     have Hctx := PermutationT_cons_app_inv _ _ ((PermutationT_sym Hpinv)).
     have Hab :=(@PermutationT_app_middle formula (A :: B :: nil) l1 l2 p' q Hctx).
     have [piAB HpiAB] := IHpi _ Hab.
     exists (pr piAB) => //=.
     by f_equal => //.
Qed.

Lemma ax_gen A : ⊢ [A; A┴].
Proof.
induction A => //= ; last 2 first.
  by apply ax.
  destruct b.
  rewrite /=.
  apply: (@pr [::_] _ _ _ ).
  apply: (@tr [::] [::] [::dual A1] [::dual A2] [::])=> //= ; last 2 first.
- by constructor.
- by repeat constructor.
  rewrite /=.
- apply: (@pr [::]) => //=.  
  apply: (@tr [A1] [A2] [::] [::] [::A1 ; A2]) => //=; last 2 first.
    - by repeat constructor.
    - by constructor.
Qed.

Lemma ax_gen_left  A : ⊢ [A┴; A].
Proof.
induction A => //=; last 2 first.
- rewrite (negb_involutive_reverse(b)) negb_involutive.
  by apply ax.
- destruct b; rewrite /=.
  apply: (@pr [::]) => //=.
  eapply tr
    with (l1 := [:: dual A1])
         (m1 := [:: dual A2])
         (l2 := [::])
         (m2 := [::])
         (n1 := [:: dual A1; dual A2])
         (n2 := [::])
         (A := A1)
         (B := A2) => //=; last 2 first.
- repeat constructor.
- repeat constructor.
      apply: (@pr [::_]) => //=.
      eapply tr
        with (l1 := [::])
         (m1 := [::])
         (l2 := [:: A1])
         (m2 := [:: A2])
         (n1 := [::])
         (n2 := [:: A1; A2])
         (A := dual A1)
         (B := dual A2) => //=.
    - constructor.
    - repeat constructor.  
Qed.
