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

Inductive mll_shuffle_tuple : seq formula -> Type :=
| ax_shuffle_tuple b X : ⊢'' [var b X; var (negb b) X]
| tr_shuffle_tuple {n1 m1 n2 m2}
    (l1  : n1.-tuple formula) (ml1 : m1.-tuple formula)
    (l2  : n2.-tuple formula) (ml2 : m2.-tuple formula)
    (t1  : (n1+m1).-tuple formula)
    (t2  : (n2+m2).-tuple formula)
    A B :
  shuffling_tuple l1 ml1 t1 ->
  shuffling_tuple l2 ml2 t2 ->
  ⊢'' l1 ++ A :: l2 ->
  ⊢'' ml1 ++ B :: ml2 ->
  ⊢'' t1 ++ A ⊗ B :: t2
| pr_shuffle_tuple l1 A B l2 : ⊢'' l1 ++ A :: B :: l2 -> ⊢'' l1 ++ A ⅋ B :: l2
where "⊢'' l" := (mll_shuffle_tuple l).

Arguments ax_shuffle {_ _}, [_] _, _ _.
Arguments pr_shuffle [_ _ _ _] _, _ [_ _ _] _, _ _ _ [_] _.
Arguments tr_shuffle [_ _ _ _ _ _ _ _ _ _] _ _, [_ _ _ _ _ _ _ _] _ _ _ _, _ _ _ _ [_ _ _ _] _ _ _ _.

Fixpoint psize_shuffle l (pi : ⊢' l) :=
match pi with
| ax_shuffle _ _  => 1
| pr_shuffle _ _ _ _ pi1 => S (psize_shuffle pi1)
| tr_shuffle _ _ _ _ _ _ _ _ _ _ _ _ _ _ pi1 pi2 => S (psize_shuffle pi1 + psize_shuffle pi2)
end.

Fixpoint psize_shuffle_tuple l (pi : ⊢'' l) :=
match pi with
| ax_shuffle_tuple _ _  => 1
| pr_shuffle_tuple _ _ _ _ pi1 => S (psize_shuffle_tuple pi1)
| tr_shuffle_tuple _ _ _ _ _ _ _ _ _ _ _ _ _ _ pi1 pi2 => S (psize_shuffle_tuple pi1 + 
                                                               psize_shuffle_tuple pi2)
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

Lemma ax_gen_shuffle_tuple A : ⊢'' [A; A┴].
Proof.
induction A => //= ; last 2 first.
  by apply ax_shuffle_tuple.
  destruct b => //=.
  apply: (@pr_shuffle_tuple [::_] _ _ _ ) => //=.
  apply: (@tr_shuffle_tuple 0 0 1 1 [::] [::] [::dual A1] [::dual A2] [::] [::dual A1; dual A2] _ _).
      exists (@MkMerge 0 0 [::] erefl erefl) => //=.
        by apply/val_inj => //.
      exists (@MkMerge 1 1 [::true; false] erefl erefl); by apply/val_inj => //=.
      all: try rewrite cat0s => //.         
  apply: (@pr_shuffle_tuple [::]) => //=.  
  apply: (@tr_shuffle_tuple 1 1 0 0 [A1] [A2] [::] [::] [::A1 ; A2]) => //=; last 2 first.
    exists (@MkMerge 1 1 [::true; false] erefl erefl) => //=; by apply/val_inj => //=.
    exists (@MkMerge 0 0 [::] erefl erefl) => //=; by apply/val_inj => //=.
Qed.

(*
Instance ex_shuffle : Proper (perm_eq ==> iffT) mll_shuffle.
Proof.
move=> l1 l2 Hperm.
split => Hd.
move: l2 Hperm.
elim: Hd.
- (* ax_shuffle *)
  move=> b X l2 h1.
  rewrite perm_sym in h1.
  case: (perm_eq_length_2_inv _ _ _ h1) => ->.
    exact: ax_shuffle.
    by rewrite -{2}(negbK b); exact: ax_shuffle.
- (* tr_shuffle *)
  move=> nl1 nm1 nl2 nm2 l0 m1 l3 m2 n1 n2 A B s s0 H1 IH1 H2 IH2 l' Hp.
  have Hpinv : perm_eq l' (A ⊗ B :: (n1 ++ n2))
    by rewrite perm_sym -cat1s perm_catCA /=.
  have [p [q [Heq Hpq]]] := perm_eq_vs_cons_inv (A ⊗ B) _ _ Hpinv.
  subst l'.
  have [bs [[hs1 sl01] sm1]] := s.
  have [bs0 [[hs2 sl3] sm2]] := s0.
  have Hnn := shuffling_app_app s s0.
  have Hpq' : perm_eq (n1 ++ n2) (p ++ q) by rewrite perm_sym.
  have sl012 : size (l0 ++ l3) = nl1 + nl2 by rewrite size_cat sl01 sl3.
  have sm12 : size (m1 ++ m2) = nm1 + nm2 by rewrite size_cat sm1 sm2.
  have [l12' [l12'' [[Hl1 Hl2] Hsh]]] := @shuffling_perm_eq _ _ _ _ _ _ _ Hnn Hpq'.
  have [l0' [l3' [m1' [m2' [[[Hl0 Hm1] sp] sq]]]]] := 
    @shuffling_app_inv  _ _ _ _ _ _ _  Hsh.
  apply (@tr_shuffle _ _ _ _ _ _ _ _ _ _ _ _ sp sq).
  by apply: IH1; apply: perm_eq_app_middle; rewrite Hl0 in Hl1.
  by apply: IH2; apply: perm_eq_app_middle; rewrite Hm1 in Hl2.
- (* pr_shuffle *)
  move=> l0 A B l2 Hpr IH l3 Hp.
  have Hpinv : perm_eq l3 (A ⅋ B :: (l0 ++ l2))
    by rewrite -cat1s perm_sym perm_catCA.
  have [p [q [Heq Hpq]]] := perm_eq_vs_cons_inv (A ⅋ B) _ _ Hpinv.
  subst l3; apply: pr_shuffle; apply: IH.
  rewrite perm_sym; by do 2! apply: perm_eq_app_middle.
- (* sym *)
  move: l1 Hperm; elim: Hd.
- move=> b X l1 h1.
  case: (perm_eq_length_2_inv _ _ _ h1) => ->.
    exact: ax_shuffle.
    rewrite -{2}(negbK b); exact: ax_shuffle.
- move=> nl1 nm1 nl2 nm2 l0 m1 l3 m2 n1 n2 A B s s0 H1 IH1 H2 IH2 l' Hp.
  have Hpinv : perm_eq l' (A ⊗ B :: (n1 ++ n2))
    by rewrite -cat1s perm_sym perm_catCA perm_sym.
  have [p [q [Heq Hpq]]] := perm_eq_vs_cons_inv (A ⊗ B) _ _ Hpinv.
  subst l'.
  have [bs [[hs1 sl01] sm1]] := s.
  have [bs0 [[hs2 sl3] sm2]] := s0.
  have Hnn := shuffling_app_app s s0.
  have Hpq' : perm_eq (n1 ++ n2) (p ++ q) by rewrite perm_sym.
    have sl012 : size (l0 ++ l3) = nl1 + nl2 by rewrite size_cat sl01 sl3.
  have sm12 : size (m1 ++ m2) = nm1 + nm2 by rewrite size_cat sm1 sm2.
  have [l12' [l12'' [[Hl1 Hl2] Hsh]]] := @shuffling_perm_eq _ _ _ _ _ _ _ Hnn Hpq'.
  have [l0' [l3' [m1' [m2' [[[Hl0 Hm1] sp] sq]]]]] := 
    @shuffling_app_inv  _ _ _ _ _ _ _  Hsh.
  apply (@tr_shuffle _ _ _ _ _ _ _ _ _ _ _ _ sp sq).
    by apply: IH1; apply: perm_eq_app_middle; rewrite perm_sym -Hl0.
    by apply: IH2; apply: perm_eq_app_middle; rewrite perm_sym -Hm1.
- move=> l0 A B l2' Hpr IH l3 Hp.
  have Hpinv : perm_eq l3 (A ⅋ B :: (l0 ++ l2'))
    by rewrite -cat1s perm_sym perm_catCA perm_sym.
  have [p [q [Heq Hpq]]] := perm_eq_vs_cons_inv (A ⅋ B) _ _ Hpinv.
  subst l3; apply: pr_shuffle; apply: IH.
  by rewrite perm_sym; do 2! apply: perm_eq_app_middle; rewrite perm_sym.
Qed.
*)

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

Instance ex_shuffle : Proper (perm_eq ==> iffT) mll_shuffle.
Proof.
move=> l l' p; split => pi.
by destruct (ex_size_shuffle _ p pi).
rewrite perm_sym in p.
by destruct (ex_size_shuffle _ p pi).
Qed.

(*
Instance ex_shuffle_tuple : Proper (perm_eq ==> iffT) mll_shuffle_tuple.
Proof.
move=> l1 l2 Hperm.
split => Hd.
move: l2 Hperm.
elim: Hd.
- (* ax_shuffle *)
  move=> b X l2 h1.
  rewrite perm_sym in h1.
  case: (perm_eq_length_2_inv _ _ _ h1) => ->.
    exact: ax_shuffle_tuple.
    by rewrite -{2}(negbK b); exact: ax_shuffle_tuple.
- (* tr_shuffle *)
  move=> nl1 nm1 nl2 nm2 l0 m1 l3 m2 n1 n2 A B s s0 H1 IH1 H2 IH2 l' Hp.
  have Hpinv : perm_eq l' (A ⊗ B :: (n1 ++ n2))
    by rewrite perm_sym -cat1s perm_catCA /=.
  have [p [q [Heq Hpq]]] := perm_eq_vs_cons_inv (A ⊗ B) _ _ Hpinv.
  subst l'.
  have [[hs1 sl01] sm1] := s.
  have [[hs2 sl3] sm2] := s0.
  have Hnn := shuffling_tuple_app_app s s0.
  have Hnn' := shuffling_tuple_to_seq Hnn.
  have Hpq'' : perm_eq (tcast (addnACA nl1 nm1 nl2 nm2) (cat_tuple n1 n2)) (p ++ q).
  by rewrite val_tcast perm_sym.
  have [l12' [l12'' [[Hl1 Hl2] Hsh]]] := @shuffling_perm_eq _ _ _ _ _ _ _ Hnn' Hpq''.
  have [l0' [l3' [m1' [m2' [[[Hl0 Hm1] sp] sq]]]]] := 
    @shuffling_app_inv  _ _ _ _ _ _ _  Hsh.
  have szp : size p = size l0' + size m1'.
    move: sp => [bs [[hsp _] _]].
    by rewrite hsp; merge_size.
  have szq : size q = size l3' + size m2'.
    move: sq => [bs' [[hsq _] _]].
    by rewrite hsq; merge_size.
  have ssp := @shuffling_to_tuple _ _ _ l0' m1' p erefl erefl szp sp.
  have ssq := @shuffling_to_tuple _ _ _ l3' m2' q erefl erefl szq sq.
  move => _ _ .
  apply (@tr_shuffle_tuple _ _ _ _ _ _ _ _ _ _ _ _ ssp ssq).
  by apply: IH1; apply: perm_eq_app_middle; rewrite Hl0 in Hl1.
  by apply: IH2; apply: perm_eq_app_middle; rewrite Hm1 in Hl2.
- (* pr_shuffle *)
  move=> l0 A B l2 Hpr IH l3 Hp.
  have Hpinv : perm_eq l3 (A ⅋ B :: (l0 ++ l2))
    by rewrite -cat1s perm_sym perm_catCA.
  have [p [q [Heq Hpq]]] := perm_eq_vs_cons_inv (A ⅋ B) _ _ Hpinv.
  subst l3; apply: pr_shuffle_tuple; apply: IH.
  rewrite perm_sym; by do 2! apply: perm_eq_app_middle.
- (* sym *)
  move: l1 Hperm; elim: Hd.
- move=> b X l1 h1.
  case: (perm_eq_length_2_inv _ _ _ h1) => ->.
    exact: ax_shuffle_tuple.
    rewrite -{2}(negbK b); exact: ax_shuffle_tuple.
- move=> nl1 nm1 nl2 nm2 l0 m1 l3 m2 n1 n2 A B s s0 H1 IH1 H2 IH2 l' Hp.
  have Hpinv : perm_eq l' (A ⊗ B :: (n1 ++ n2))
    by rewrite -cat1s perm_sym perm_catCA perm_sym.
  have [p [q [Heq Hpq]]] := perm_eq_vs_cons_inv (A ⊗ B) _ _ Hpinv.
  subst l'.
  have [[hs1 sl01] sm1] := s.
  have [[hs2 sl3] sm2] := s0.
  have Hnn' := shuffling_tuple_to_seq (shuffling_tuple_app_app s s0).
  have Hpq'' : perm_eq (tcast (addnACA nl1 nm1 nl2 nm2) (cat_tuple n1 n2)) (p ++ q).
  by rewrite val_tcast perm_sym.
  have [l12' [l12'' [[Hl1 Hl2] Hsh]]] := @shuffling_perm_eq _ _ _ _ _ _ _ Hnn' Hpq''.
  have [l0' [l3' [m1' [m2' [[[Hl0 Hm1] sp] sq]]]]] := 
    @shuffling_app_inv  _ _ _ _ _ _ _  Hsh.
  have szp : size p = size l0' + size m1'.
    move: sp => [bs [[hsp _] _]].
    by rewrite hsp; merge_size.
  have szq : size q = size l3' + size m2'.
    move: sq => [bs' [[hsq _] _]].
    by rewrite hsq; merge_size.
  have ssp := @shuffling_to_tuple _ _ _ l0' m1' p erefl erefl szp sp.
  have ssq := @shuffling_to_tuple _ _ _ l3' m2' q erefl erefl szq sq.
  move => _ _ .
  apply (@tr_shuffle_tuple _ _ _ _ _ _ _ _ _ _ _ _ ssp ssq).
    by apply: IH1; apply: perm_eq_app_middle; rewrite perm_sym -Hl0.
    by apply: IH2; apply: perm_eq_app_middle; rewrite perm_sym -Hm1.
- move=> l0 A B l2' Hpr IH l3 Hp.
  have Hpinv : perm_eq l3 (A ⅋ B :: (l0 ++ l2'))
    by rewrite -cat1s perm_sym perm_catCA perm_sym.
  have [p [q [Heq Hpq]]] := perm_eq_vs_cons_inv (A ⅋ B) _ _ Hpinv.
  subst l3; apply: pr_shuffle_tuple; apply: IH.
  by rewrite perm_sym; do 2! apply: perm_eq_app_middle; rewrite perm_sym.
Qed.
*)

Lemma ex_size_shuffle_tuple l' l (p : perm_eq l l') (pi : ⊢'' l) : 
{ pi' : ⊢'' l' | psize_shuffle_tuple pi' = psize_shuffle_tuple pi }.
Proof.
induction pi in l', p |- *.
  rewrite perm_sym in p.
  destruct (perm_eq_length_2_inv _ _ _ p) as [-> | ->] => //=.
      by exists (ax_shuffle_tuple b X).
    by rewrite (negb_involutive_reverse (b)) negb_involutive; exists (ax_shuffle_tuple (~~ b) X).
    have Hpinv : perm_eq l' (A ⊗ B :: (t1 ++ t2)) by rewrite perm_sym -cat1s perm_catCA /=.
    have [p' [q [Heq Hpq]]] := perm_eq_vs_cons_inv (A ⊗ B) _ _ Hpinv.
    subst l'.
    have Hnn' := (shuffling_tuple_app_app s s0).
    have Hlen : size (p' ++ q) == n1 + n2 + (m1 + m2).
      have := perm_size Hpq.
      by rewrite size_cat; merge_size.
    pose l3' : (n1 + n2 + (m1 + m2)).-tuple formula := Tuple Hlen.
    have Hpq' : perm_eq (tcast (addnACA n1 m1 n2 m2) (cat_tuple t1 t2)) l3' by rewrite !val_tcast /l3' /= perm_sym.
    have [l12' [l12'' [[Hl1 Hl2] Hsh]]] := @shuffling_tuple_perm_eq _ _ _ _ _ _ _ Hnn' Hpq'.
    have Hpq_size : size p' + size q = n1 + n2 + (m1 + m2) by rewrite -size_cat; apply/eqP.
    set P : (size p').-tuple formula := Tuple (eqxx (size p')).
    set Q : (size q).-tuple formula := Tuple (eqxx (size q)).
    have Hcat_val : tval l3' = tval P ++ tval Q by rewrite /l3' /P /Q /=.
    have [n1p [n2p [m1p [m2p [Hnp [Hmp [Hap [Hbp [L11p [L12p [L21p [L22p
        [[[HLsp1 HLsp2] sh1p] sh2p]]]]]]]]]]]]] := shuffling_tuple_app_inv Hpq_size Hcat_val Hsh.
    have HpermA : perm_eq (l1 ++ A :: l2) (L11p ++ A :: L12p) by rewrite perm_eq_app_middle //; rewrite HLsp1 in Hl1.
    have HpermB : perm_eq (ml1 ++ B :: ml2) (L21p ++ B :: L22p) by rewrite perm_eq_app_middle => //=;    rewrite HLsp2 in Hl2.
    have [HApq HsizeA] := IHpi1 _ HpermA.
    have [HBpq HsizeB] := IHpi2 _ HpermB.
    have Hseq : tcast Hap P ++ A ⊗ B :: tcast Hbp Q = p' ++ A ⊗ B :: q by rewrite !val_tcast /P /Q /=.
    rewrite -Hseq /=.
    exists (tr_shuffle_tuple A B sh1p sh2p HApq HBpq).
    f_equal.
    by rewrite /= HsizeA HsizeB.
  - have Hpinv : perm_eq l' (A ⅋ B :: (l1 ++ l2)) by rewrite -cat1s perm_sym perm_catCA.
    have [p' [q [Heq Hpq]]] := perm_eq_vs_cons_inv (A ⅋ B) _ _ Hpinv.
    subst l'.
    have Hab : perm_eq (l1 ++ [:: A, B & l2]) (p' ++ [:: A, B & q]). 
    rewrite (perm_catCA l1 [::A;B] l2). 
    rewrite perm_sym (perm_catCA p' [::A;B] q).
    by rewrite !perm_cons.
    have [piAB HpiAB] := IHpi _ Hab.
    exists (pr_shuffle_tuple _ _ _ _ piAB) => /=.
    f_equal => //.
Qed.

Instance ex_shuffle_tuple : Proper (perm_eq ==> iffT) mll_shuffle_tuple.
Proof.
move=> l l' p; split => pi.
by destruct (ex_size_shuffle_tuple _ p pi).
rewrite perm_sym in p.
by destruct (ex_size_shuffle_tuple _ p pi).
Qed.

Reserved Notation "⊢''' l" (at level 65).

Inductive mll_splits : seq formula -> Type :=
| ax_splits b X : ⊢''' [var b X; var (negb b) X]
| tr_splits {n1 m1 n2 m2} (s1 : Merge n1 m1) (s2 : Merge n2 m2) 
    (l : (n1+m1).-tuple formula) (l' : (n2+m2).-tuple formula)
    A B :
  ⊢''' split1 s1 l ++ A :: split1 s2 l'  ->
  ⊢''' split2 s1 l ++ B :: split2 s2 l' ->
  ⊢''' l ++ A ⊗ B :: l'
| pr_splits l1 A B l2 : ⊢''' l1 ++ A :: B :: l2 -> ⊢''' l1 ++ A ⅋ B :: l2
where "⊢''' l" := (mll_splits l).

Fixpoint psize_split l (pi : ⊢''' l) :=
match pi with
| ax_splits _ _  => 1
| pr_splits _ _ _ _ pi1 => S (psize_split pi1)
| tr_splits _ _ _ _ _ _ _ _ _ _ pi1 pi2 => S (psize_split pi1 + psize_split pi2)
end.

Lemma ax_gen_split A : ⊢''' [A; A┴].
Proof.
induction A => //= ; last 2 first.
  by apply ax_splits.
  destruct b => //=.
  apply: (@pr_splits [::_] _ _ _ ) => //=.
  apply : (@tr_splits 0 0 1 1 (@MkMerge 0 0 [::] erefl erefl) (@MkMerge 1 1 [::true; false] erefl erefl)  [::] [dual A1 ; dual A2] A1 A2 _ _) => //=.   
  apply: (@pr_splits [::]) => //=.  
  apply : (@tr_splits 1 1 0 0 (@MkMerge 1 1 [::true; false] erefl erefl)
             (@MkMerge 0 0 [::] erefl erefl)
             [::A1; A2] [::] (dual A1) (dual A2) _ _ ) => //=.
Qed.

(*
Instance ex_split : Proper (perm_eq ==> iffT) mll_splits.
Proof.
move=> l1 l2 Hperm.
split => Hd.
move: l2 Hperm.
elim: Hd.
- (* ax_shuffle *)
  move=> b X l2 h1.
  rewrite perm_sym in h1.
  case: (perm_eq_length_2_inv _ _ _ h1) => ->.
    exact: ax_splits.
    by rewrite -{2}(negbK b); exact: ax_splits.
- (* tr_shuffle *)
  move=> nl1 nm1 nl2 nm2 s s0 l0 l2 A B H1 IH1 H2 IH2 l' IHperm. 
  have Hpinv : perm_eq l' (A ⊗ B :: (l0 ++ l2))
    by rewrite perm_sym -cat1s perm_catCA /=.
  have [p [q [Heq Hpq]]] := perm_eq_vs_cons_inv (A ⊗ B) _ _ Hpinv.
  subst l'.
  have Hsh_s : shuffling nl1 nm1 (split1 s l0) (split2 s l0) l0.
    apply ((shuffling_splits_iff _ _ _ )) => //=.
    by exists s => //=; merge_size.
  have Hsh_s0 : shuffling nl2 nm2 (split1 s0 l2) (split2 s0 l2) l2.
    apply ((shuffling_splits_iff _ _ _ )) => //=.
    by exists s0 => //=; merge_size.
  have Hnn := shuffling_app_app Hsh_s Hsh_s0.
  have Hpq' : perm_eq (l0 ++ l2) (p ++ q) by rewrite perm_sym.
  have [l12' [l12'' [[Hl1 Hl2] Hsh]]] := @shuffling_perm_eq _ _ _ _ _ _ _ Hnn Hpq'.
  have [l0' [l3' [m1' [m2' [[[Hl0 Hm1] sp] sq]]]]] := 
    @shuffling_app_inv  _ _ _ _ _ _ _  Hsh.
  move: sp => [bs [[hsp sl0'] sm1']].
  move: sq => [bs0 [[hsq sl3'] sm2']].
  have szp : size p = size l0' + size m1' by rewrite hsp; merge_size.
  have szq : size q = size l3' + size m2' by rewrite hsq; merge_size.
  apply (@tr_splits _ _ _ _ bs bs0   (Tuple (introT eqP szp)) (Tuple (introT eqP szq)) A B).
    apply: IH1 => //=.
    rewrite perm_eq_app_middle => //=.
    rewrite Hl0 in Hl1.
    rewrite /split1 hsp hsq /= !mask_merge_seq_l /=.
    by rewrite Hl1.
      all: try merge_size => //; try by lia  => //=.
      all: try rewrite addKn => //=.
    rewrite /= Hm1 in Hl2 => //=.
    rewrite hsp hsq.
    apply IH2 => //=.
    rewrite perm_eq_app_middle => //=.
    rewrite /split2 !mask_merge_seq_r /=.
    by rewrite Hl2.
      all: try merge_size => //; try lia => //=.
      all: try rewrite addKn => //.
- (* pr_shuffle *)
  move=> l0 A B l2 Hpr IH l3 Hp.
  have Hpinv : perm_eq l3 (A ⅋ B :: (l0 ++ l2))
    by rewrite -cat1s perm_sym perm_catCA.
  have [p [q [Heq Hpq]]] := perm_eq_vs_cons_inv (A ⅋ B) _ _ Hpinv.
  subst l3; apply: pr_splits; apply: IH.
  rewrite perm_sym; by do 2! apply: perm_eq_app_middle.
- (* sym *)
  move: l1 Hperm; elim: Hd.
- move=> b X l1 h1.
  case: (perm_eq_length_2_inv _ _ _ h1) => ->.
    exact: ax_splits.
    rewrite -{2}(negbK b); exact: ax_splits.
- move=> nl1 nm1 nl2 nm2 s s0 l0 l2' A B H1 IH1 H2 IH2 l' IHperm. 
  have Hpinv : perm_eq l' (A ⊗ B :: (l0 ++ l2')).
    by rewrite perm_sym -cat1s perm_catCA perm_sym /=.
  have [p [q [Heq Hpq]]] := perm_eq_vs_cons_inv (A ⊗ B) _ _ Hpinv.
  subst l'.
  have Hsh_s : shuffling nl1 nm1 (split1 s l0) (split2 s l0) l0.
    apply ((shuffling_splits_iff _ _ _ )) => //=.
    by exists s => //=; merge_size.
  have Hsh_s0 : shuffling nl2 nm2 (split1 s0 l2') (split2 s0 l2') l2'.
    apply ((shuffling_splits_iff _ _ _ )) => //=.
    by exists s0 => //=; merge_size => //=.
  have Hnn := shuffling_app_app Hsh_s Hsh_s0.
  have Hpq' : perm_eq (l0 ++ l2') (p ++ q) by rewrite perm_sym.
  have [l12' [l12'' [[Hl1 Hl2] Hsh]]] := @shuffling_perm_eq _ _ _ _ _ _ _ Hnn Hpq'.
  have [l0' [l3' [m1' [m2' [[[Hl0 Hm1] sp] sq]]]]] := 
    @shuffling_app_inv  _ _ _ _ _ _ _  Hsh.
  move: sp => [bs [[hsp sl0'] sm1']].
  move: sq => [bs0 [[hsq sl3'] sm2']].
  have szp : size p = size l0' + size m1' by rewrite hsp; merge_size.
  have szq : size q = size l3' + size m2' by rewrite hsq; merge_size.
  apply (@tr_splits _ _ _ _ bs bs0   (Tuple (introT eqP szp)) (Tuple (introT eqP szq)) A B).
    apply: IH1; apply: perm_eq_app_middle.
    rewrite perm_sym /=.
    rewrite Hl0 in Hl1.
    rewrite /split1 hsp hsq /= !mask_merge_seq_l /=.
    by rewrite Hl1.
      all: try merge_size => //=; try lia => //=.
    rewrite Hm1 in Hl2 => //=.
    rewrite hsp hsq.
    apply IH2 => //=.
    rewrite perm_eq_app_middle /= /split2 //= !mask_merge_seq_r /=.
    rewrite /split2 perm_sym in Hl2.
    by rewrite Hl2.
      all: try merge_size => //=; try lia => //=.
- move=> l0 A B l2' Hpr IH l3 Hp.
  have Hpinv : perm_eq l3 (A ⅋ B :: (l0 ++ l2'))
    by rewrite -cat1s perm_sym perm_catCA perm_sym.
  have [p [q [Heq Hpq]]] := perm_eq_vs_cons_inv (A ⅋ B) _ _ Hpinv.
  subst l3; apply: pr_splits; apply: IH.
  by rewrite perm_sym; do 2! apply: perm_eq_app_middle; rewrite perm_sym.
Qed.
*)

Lemma ex_size_split l' l (p : perm_eq l l') (pi : ⊢''' l) : { pi' : ⊢''' l' | psize_split pi' = psize_split pi }.
Proof.
induction pi in l', p |- *.
  rewrite perm_sym in p.
  destruct (perm_eq_length_2_inv _ _ _ p) as [-> | ->] => //=.
    - by exists (ax_splits b X).
    - by rewrite (negb_involutive_reverse (b)) negb_involutive; exists (ax_splits (~~ b) X).     
      have tr1 := (tr_splits _ _ _ _ _ _ pi1 pi2).
      have Hpinv : perm_eq l' (A ⊗ B :: (l ++ l'0)) by rewrite perm_sym -cat1s perm_catCA /=.
      have [p' [q [Heq Hpq]]] := perm_eq_vs_cons_inv (A ⊗ B) _ _ Hpinv.
      subst l'.
      have Hsh_s : shuffling n1 m1 (split1 s1 l) (split2 s1 l) l.
        apply ((shuffling_splits_iff _ _ _ )) => //=.
        by exists s1 => //=; merge_size_clear.
      have Hsh_s0 : shuffling n2 m2 (split1 s2 l'0) (split2 s2 l'0) l'0.
        apply ((shuffling_splits_iff _ _ _ )) => //=.
        by exists s2 => //=; merge_size_clear.
      have Hnn := shuffling_app_app Hsh_s Hsh_s0.
      have Hpq' : perm_eq (l ++ l'0) (p' ++ q) by rewrite perm_sym.
      have [l12' [l12'' [[Hl1 Hl2] Hsh]]] := shuffling_perm_eq Hnn Hpq'.
      have [l0' [l3' [m1' [m2' [[[Hl0 Hm1] sp] sq]]]]]:= shuffling_app_inv Hsh.
      have HpermA : perm_eq (split1 s1 l ++ A :: split1 s2 l'0) (l0' ++ A :: l3'). 
        by rewrite perm_eq_app_middle => //=; rewrite Hl0 in Hl1.
      have HpermB : perm_eq (split2 s1 l ++ B :: split2 s2 l'0) (m1' ++ B :: m2').
        by rewrite perm_eq_app_middle => //=; rewrite Hm1 in Hl2.
    have [HApq HsizeA] := IHpi1 _ HpermA.
    have [HBpq HsizeB] := IHpi2 _ HpermB.
    move: sp => [bs hsp [sl0' sm1']].
    move: sq => [bs0 hsq [sl3' sm2']].
    have hT1 : size (merge_seq bs l0' m1') == size l0' + size m1' by merge_size_clear.
    have hT2 : size (merge_seq bs0 l3' m2') == size l3' + size m2' by merge_size_clear.
    have h1 : split1 bs  (Tuple hT1) = l0' by rewrite /= thm2.
    have h2 : split1 bs0 (Tuple hT2) = l3' by rewrite thm2.
    have h3 : split2 bs  (Tuple hT1) = m1' by rewrite /= thm3.
    have h4 : split2 bs0 (Tuple hT2) = m2' by rewrite thm3.
    have HpermA' : perm_eq (split1 s1 l ++ A :: split1 s2 l'0)
                       (split1 bs (Tuple hT1) ++ A :: split1 bs0 (Tuple hT2))
      by rewrite h1 h2.
    have [HA' HsizeA'] := IHpi1 _ HpermA'.
    have HpermB' : perm_eq (split2 s1 l ++ B :: split2 s2 l'0)
                       (split2 bs (Tuple hT1) ++ B :: split2 bs0 (Tuple hT2))
      by rewrite h3 h4.
    have [HB' HsizeB'] := IHpi2 _ HpermB'.
    subst p' q.
    exists (@tr_splits _ _ _ _ bs bs0 (Tuple hT1) (Tuple hT2) A B HA' HB') => //=.
    f_equal.
    simpl in *.
    by rewrite HsizeA' HsizeB'.
  - have Hpinv : perm_eq l' (A ⅋ B :: (l1 ++ l2)).
        by rewrite -cat1s perm_sym perm_catCA.
      have [p' [q [Heq Hpq]]] := perm_eq_vs_cons_inv (A ⅋ B) _ _ Hpinv.
      have Hab : perm_eq (l1 ++ [:: A, B & l2]) (p' ++ [:: A, B & q]). 
        rewrite (perm_catCA l1 [::A;B] l2). 
        rewrite perm_sym (perm_catCA p' [::A;B] q).
        by rewrite !perm_cons.
      have [piAB HpiAB] := IHpi _ Hab.
      subst l'.
      exists (pr_splits _ _ _ _ piAB) => /=.
      f_equal => //.
Qed.

Instance ex_split_ : Proper (perm_eq ==> iffT) mll_splits.
Proof.
move=> l l' p; split => pi.
by destruct (ex_size_split _ p pi).
rewrite perm_sym in p.
by destruct (ex_size_split _ p pi).
Qed.

Reserved Notation "⊢''''' l" (at level 65).
Inductive mll_splits5 : seq formula -> Type :=
| ax_splits5 b X : ⊢''''' [var b X; var (negb b) X]
| tr_splits5  {n1 m1 n2 m2} (s1 : Merge n1 m1) (s2 : Merge n2 m2)
    (l : (n1+m1).-tuple formula) (l' : (n2+m2).-tuple formula)
     A B l1 l2 l1' l2' :
  @splits formula n1 m1 s1 l = (l1, l2) ->
  @splits formula n2 m2 s2 l' = (l1', l2') ->
  ⊢''''' l1 ++ A :: l1' ->
  ⊢''''' l2 ++ B :: l2' ->
  ⊢''''' l ++ A ⊗ B :: l'
| pr_splits5 l1 A B l2 :
  ⊢''''' l1 ++ A :: B :: l2 ->
  ⊢''''' l1 ++ A ⅋ B :: l2
where "⊢''''' l" := (mll_splits5 l).

Fixpoint psize_splits l (pi : ⊢''''' l) :=
match pi with
| ax_splits5 _ _  => 1
| pr_splits5 _ _ _ _ pi1 => S (psize_splits pi1)
| tr_splits5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pi1 pi2 => S (psize_splits pi1 + psize_splits pi2)
end.

Lemma ax_gen_splits A : ⊢''''' [A; A┴].
Proof.
induction A => //= ; last 2 first.
  by apply ax_splits5.
  destruct b => //=.
  apply: (@pr_splits5 [::_] _ _ _ ) => //=.
  apply : (@tr_splits5 0 0 1 1 (@MkMerge 0 0 [::] erefl erefl)  (@MkMerge 1 1 [::true; false] erefl erefl) [::] [::dual A1; dual A2 ] (A1) A2 _ _) => //=.   
  apply: (@pr_splits5 [::]) => //=.  
  apply : (@tr_splits5 1 1 0 0 (@MkMerge 1 1 [::true; false] erefl erefl)
              (@MkMerge 0 0 [::] erefl erefl)
             [::A1; A2] [::] (dual A1) (dual A2) _ _ ) => //=.
Qed.

Lemma ex_size_splits l' l (p : perm_eq l l') (pi : ⊢''''' l) :
  { pi' : ⊢''''' l' | psize_splits pi' = psize_splits pi }.
Proof.
induction pi in l', p |- *.
 - rewrite perm_sym in p.
   destruct (perm_eq_length_2_inv _ _ _ p) as [-> | ->] => //=.
     by exists (ax_splits5 b X).
     by rewrite (negb_involutive_reverse b) negb_involutive; exists (ax_splits5 (~~ b) X).
 - have Hpinv : perm_eq l' (A ⊗ B :: (l ++ l'0)) by rewrite perm_sym -cat1s perm_catCA //=.
   have [p' [q' [-> Hpq]]] := perm_eq_vs_cons_inv (A ⊗ B) _ _ Hpinv.
   rewrite perm_sym in Hpq.
   have Hsh_s : shuffling n1 m1 l1 l2 l.
     by apply (shuffling_splits_iff _ _ l).2; exists s1 => //=; merge_size_clear.
   have Hsh_s0 : shuffling n2 m2 l1' l2' l'0.
     by apply (shuffling_splits_iff _ _ l'0).2; exists s2 => //=; merge_size_clear.
     have Hnn' := shuffling_app_app Hsh_s Hsh_s0.
   have [L1 [L2 [[HL1 HL2] Hsh]]] := shuffling_perm_eq Hnn' Hpq.
   have [L11 [L12 [L21 [L22 [[[HLs1 HLs2] sp1] sp2]]]]] := shuffling_app_inv Hsh.
   have HpA : perm_eq (l1 ++ A :: l1') (L11 ++ A :: L12).
     apply perm_eq_app_middle => //; by rewrite HLs1 in HL1.
   have HpB : perm_eq (l2 ++ B :: l2') (L21 ++ B :: L22).
     apply perm_eq_app_middle; by rewrite HLs2 in HL2.
   have [pi1' Hsize1] := IHpi1 _ HpA.
   have [pi2' Hsize2] := IHpi2 _ HpB.
   have [bs1 Hbs1] := (shuffling_splits_iff _ _ p').1 sp1.
   have [bs2 Hbs2] := (shuffling_splits_iff _ _ q').1 sp2.
   move/eqP => sq ; move/eqP => sp.
   have Hbs1' : splits bs1 (Tuple (sp)) = (L11, L21) by rewrite -Hbs1 => //.
   have Hbs2' : splits bs2 (Tuple sq) = (L12, L22) by rewrite Hbs2 => //.   
   exists (tr_splits5 (Tuple (sp)) (Tuple (sq)) A B Hbs1' Hbs2' pi1' pi2').
     by rewrite /= Hsize1 Hsize2.
 - have Hpinv : perm_eq l' (A ⅋ B :: (l1 ++ l2)) by rewrite -cat1s perm_sym perm_catCA.
   have [p' [q [Heq Hpq]]] := perm_eq_vs_cons_inv (A ⅋ B) _ _ Hpinv.
   subst l'.
   have Hab : perm_eq (l1 ++ [:: A, B & l2]) (p' ++ [:: A, B & q]) by
      rewrite (perm_catCA l1 [::A;B] l2) perm_sym (perm_catCA p' [::A;B] q) !perm_cons.
   have [piAB HpiAB] := IHpi _ Hab.
   exists (pr_splits5  _ _ _ _ piAB) => /=.
   f_equal => //.
Qed.

Instance ex_splits_ : Proper (perm_eq ==> iffT) mll_splits5.
Proof.
move=> l l' p; split => pi.
by destruct (ex_size_splits _ p pi).
rewrite perm_sym in p.
by destruct (ex_size_splits _ p pi).
Qed.

Reserved Notation "⊢'''' l" (at level 65).
Inductive mll_split_tuple : seq formula -> Type :=
| ax_split_tuple b X : ⊢'''' [var b X; var (negb b) X]
| tr_split_tuple  {n1 m1 n2 m2} (s1 : Merge n1 m1) (s2 : Merge n2 m2)
    (l : (n1+m1).-tuple formula) (l' : (n2+m2).-tuple formula)
     A B l1 l2 l1' l2' :
  @split_tuple formula n1 m1 s1 l = (l1, l2) ->
  @split_tuple formula n2 m2 s2 l' = (l1', l2') ->
  ⊢'''' l1 ++ A :: l1' ->
  ⊢'''' l2 ++ B :: l2' ->
  ⊢'''' l ++ A ⊗ B :: l'
| pr_split_tuple l1 A B l2 :
  ⊢'''' l1 ++ A :: B :: l2 ->
  ⊢'''' l1 ++ A ⅋ B :: l2
where "⊢'''' l" := (mll_split_tuple l).

Fixpoint psize_split_tuple l (pi : ⊢'''' l) :=
match pi with
| ax_split_tuple _ _  => 1
| pr_split_tuple _ _ _ _ pi1 => S (psize_split_tuple pi1)
| tr_split_tuple _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pi1 pi2 => S (psize_split_tuple pi1 + psize_split_tuple pi2)
end.

Lemma ax_gen_split_tuple A : ⊢'''' [A; A┴].
Proof.
induction A => //= ; last 2 first.
  by apply ax_split_tuple.
  destruct b => //=.
  apply: (@pr_split_tuple [::_] _ _ _ ) => //=.
  apply : (@tr_split_tuple 0 0 1 1 (@MkMerge 0 0 [::] erefl erefl)  (@MkMerge 1 1 [::true; false] erefl erefl) [::] [::dual A1; dual A2 ] (A1) A2 _ _) => //=.   
  apply: (@pr_split_tuple [::]) => //=.  
  apply : (@tr_split_tuple 1 1 0 0 (@MkMerge 1 1 [::true; false] erefl erefl)
              (@MkMerge 0 0 [::] erefl erefl)
             [::A1; A2] [::] (dual A1) (dual A2) _ _ ) => //=.
Qed.

Lemma ex_size_split_tuple l' l (p : perm_eq l l') (pi : ⊢'''' l) :
  { pi' : ⊢'''' l' | psize_split_tuple pi' = psize_split_tuple pi }.
Proof.
induction pi in l', p |- *.
 - rewrite perm_sym in p.
   destruct (perm_eq_length_2_inv _ _ _ p) as [-> | ->] => //=.
     by exists (ax_split_tuple b X).
     by rewrite (negb_involutive_reverse b) negb_involutive; exists (ax_split_tuple (~~ b) X).
- have Hpinv : perm_eq l' (A ⊗ B :: (l ++ l'0))
  by rewrite perm_sym -cat1s perm_catCA.
  have [p' [q' [-> Hpq]]] := perm_eq_vs_cons_inv (A ⊗ B) _ _ Hpinv.
  rewrite perm_sym in Hpq.
  have Hsh_s : shuffling_tuple l1 l2 l.
    by apply (shuffling_tuple_splits_iff _ _ l).2; exists s1.
  have Hsh_s0 : shuffling_tuple l1' l2' l'0.
    by apply (shuffling_tuple_splits_iff _ _ l'0).2; exists s2.
  have Hnn' := shuffling_tuple_app_app Hsh_s Hsh_s0.
  have Hlen : size (p' ++ q') == n1 + n2 + (m1 + m2).
    have := perm_size Hpq.
    by rewrite size_cat; merge_size.
  pose l3' : (n1 + n2 + (m1 + m2)).-tuple formula := Tuple Hlen.
  have Hpq' : perm_eq (tcast (addnACA n1 m1 n2 m2) (cat_tuple l l'0)) l3'
    by rewrite !val_tcast /l3'.
  have [L1 [L2 [[HL1 HL2] Hsh]]] := shuffling_tuple_perm_eq Hnn' Hpq'.
  have Hpq_size : size p' + size q' = n1 + n2 + (m1 + m2).
    by rewrite -size_cat; apply/eqP.
  set P : (size p').-tuple formula := Tuple (eqxx (size p')).
  set Q : (size q').-tuple formula := Tuple (eqxx (size q')).
  have Hcat_val : tval l3' = tval P ++ tval Q by rewrite /l3' /P /Q /=.
  have [n1p [n2p [m1p [m2p [Hnp [Hmp [Hap [Hbp [L11p [L12p [L21p [L22p
  [[[HLsp1 HLsp2] sh1p] sh2p]]]]]]]]]]]]] := shuffling_tuple_app_inv Hpq_size Hcat_val Hsh.
  have HpA : perm_eq (l1 ++ A :: l1') (L11p ++ A :: L12p).
    apply perm_eq_app_middle. 
    by apply: (perm_trans HL1); rewrite HLsp1.
  have HpB : perm_eq (l2 ++ B :: l2') (L21p ++ B :: L22p).
    apply perm_eq_app_middle.
    by apply: (perm_trans HL2); rewrite HLsp2.
    have [pi1p Hsize1p] := IHpi1 _ HpA.
    have [pi2p Hsize2p] := IHpi2 _ HpB.
    have [s1p Hs1p] := sh1p.
    have [s2p Hs2p] := sh2p.
    have Hsplit1 : split_tuple s1p (tcast Hap P) = (L11p, L21p).
      by rewrite Hs1p /split_tuple thm3_tuple thm2_tuple.
    have Hsplit2 : split_tuple s2p (tcast Hbp Q) = (L12p, L22p).
      by rewrite Hs2p /split_tuple thm3_tuple thm2_tuple.
    have Hseq : tcast Hap P ++ A ⊗ B :: tcast Hbp Q = p' ++ A ⊗ B :: q'
      by rewrite !val_tcast /P /Q /=.
    rewrite -Hseq.
    exists (tr_split_tuple A B Hsplit1 Hsplit2 pi1p pi2p).
      by rewrite /= Hsize1p Hsize2p.
 - have Hpinv : perm_eq l' (A ⅋ B :: (l1 ++ l2)) by rewrite -cat1s perm_sym perm_catCA.
   have [p' [q [Heq Hpq]]] := perm_eq_vs_cons_inv (A ⅋ B) _ _ Hpinv.
   subst l'.
   have Hab : perm_eq (l1 ++ [:: A, B & l2]) (p' ++ [:: A, B & q]) by
      rewrite (perm_catCA l1 [::A;B] l2) perm_sym (perm_catCA p' [::A;B] q) !perm_cons.
   have [piAB HpiAB] := IHpi _ Hab.
   exists (pr_split_tuple  _ _ _ _ piAB) => /=.
   f_equal => //.
Qed.

Instance ex_splits_tuple : Proper (perm_eq ==> iffT) mll_split_tuple.
Proof.
move=> l l' p; split => pi.
by destruct (ex_size_split_tuple _ p pi).
rewrite perm_sym in p.
by destruct (ex_size_split_tuple _ p pi).
Qed.
