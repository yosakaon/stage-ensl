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

Definition shuffle {A : Type}
    (l1 : seq A) (l2 : seq A) (l3 : seq A) : Type :=
  { c : bitseq &
    size c = size l3 /\
    mask c l3 = l1 /\
    mask (map negb c) l3 = l2 }.

Lemma shuffle_nil {A : Type} : shuffle ([::] : seq A) [::] [::].
Proof.
by exists [::].
Qed.

Lemma shuffle_nil_r {A : Type} n (l1 l3 : n.-tuple A):  shuffle l3 l1 [::] -> l1 = l3.
Proof.
move => s.
destruct s as [c [s [Hl Hr]]].
rewrite mask0 in Hl Hr.
rewrite mask0 in Hr.
apply: val_inj => //=.
by rewrite -Hl -Hr.
Qed.

Lemma shuffle_nil_l {A : Type} n (l1 l2 : n.-tuple A):  shuffle l1 [::] l2 -> l2 = l1.
Proof.
move => [c [Hsize [Hl Hr]]].
apply val_inj => //=.
rewrite -Hl.
move: Hsize Hr.
clear Hl l1.
elim: c (val l2) => [|b c IH] [|x l] //= Hs Hm.
case: b Hm => //= Hm.
congr (x :: _).
by apply IH; inversion Hs.
Qed.

Lemma shuffle_l {A : Type} n m a
    (t1 : n.-tuple A) (t2 : m.-tuple A) (t3 : (m+n).-tuple A) :
  shuffle t1 t2 t3 ->
  shuffle [tuple of a :: t1] t2 [tuple of a :: t3].
Proof.
move => s1.
destruct s1 as [c [s [Hl Hr]]].
exists (true :: c).
split => //=.
by inversion s.
split.
  by rewrite /=; rewrite Hl. 
  by rewrite /=; rewrite Hr. 
Qed.

Lemma shuffle_r {A : Type} n m a
    (t1 : n.-tuple A) (t2 : m.-tuple A) (t3 : (n+m).-tuple A) :
  shuffle t1 t2 t3 ->
  shuffle t1 [tuple of a :: t2] [tuple of a :: t3].
Proof.
move => s1.
destruct s1 as [c [ s [Hl Hr]]].
exists (false :: c).
split => //=.
by inversion s.
split.
  by rewrite /=; rewrite Hl. 
  by rewrite /=; rewrite Hr. 
Qed.

Lemma shuffle_comm {A : Type} n m (t1 : n.-tuple A) (t2 : m.-tuple A) 
(t3 : (n+m).-tuple A) : iffT (shuffle t1 t2 t3) (shuffle t2 t1 t3).
Proof.
split => [[c [Hs [Hl Hr]]] | [c [Hs [Hl Hr]]]].
all: exists (map negb c); rewrite size_map; split => //; split => //.
all: by rewrite mapK //; exact negbK.
Qed.

Fixpoint expand (c1 c2 : bitseq) : bitseq :=
  match c1, c2 with
  | [::], _ => [::]
  | true :: c1', c2 => true :: expand c1' c2
  | false :: c1', b :: c2' => b :: expand c1' c2'
  | false :: c1', [::] => false :: expand c1' [::]
  end.

Lemma size_expand : forall (c1 c2 : bitseq),
  size c2 = count negb c1 ->
  size (expand c1 c2) = size c1.
Proof.
elim => [|b c1 IH] [|x c2] //= Hs.
  case: b Hs => //= Hs; by rewrite IH.
  by case: b Hs => //= Hs; [rewrite IH| rewrite IH; inversion Hs] => //=.
Qed.

Lemma mask_expand_l : forall (c1 c2 : bitseq) (B : Type) (s : seq B),
  size c1 = size s -> size c2 = count negb c1 ->
  mask (mask (expand c1 c2) c1) (mask (expand c1 c2) s) = mask c1 s.
Proof.
move => c1 c2 B s sc1 sc2.
elim: c1 c2 s sc1 sc2 => [|b c1 IH] c2 [|x s] //= sc1 sc2 => //=.
case: b sc1 sc2 => /= sc1 sc2.
  rewrite IH => //=.
  by inversion sc1.
  case: c2 sc2 => [|y c2] /= sc2.
    by rewrite IH => //=.
    case: y => /=.
      by rewrite IH //=; [inversion sc1 | inversion sc2] => //=.
      rewrite IH => //=.
        by inversion sc1 => //=.
        by inversion sc2 => //=.
Qed.

Lemma expand_mask_r : forall (c1 c2 : bitseq) (B : Type) (s : seq B),
  size c1 = size s -> size c2 = count negb c1 ->
  mask [seq ~~ i | i <- mask (expand c1 c2) c1] (mask (expand c1 c2) s) = 
  mask c2 (mask [seq ~~ i | i <- c1] s).
Proof.
elim => [|[] c1 IH] [|[] c2] B [|x s] //= sc1 sc2;
  rewrite IH //=; by inversion sc1; by inversion sc2.
Qed.

Lemma mask_expand_r : forall (c1 c2 : bitseq) (B : Type) (s : seq B),
  size c1 = size s -> size c2 = count negb c1 ->
  mask (map negb (expand c1 c2)) s = mask (map negb c2) (mask (map negb c1) s).
Proof.
move => c1 c2 B s sc1 sc2.
elim: c1 c2 s sc1 sc2 => [|b c1 IH] c2 [|x s] //= sc1 sc2 => //=.
by rewrite mask0.
case: b sc1 sc2 => /= sc1 sc2.
  rewrite IH => //=.
  by inversion sc1.
  case: c2 sc2 => [|y c2] /= sc2.
    by rewrite IH.
    rewrite IH => //=; last 2 first.
      by inversion sc1.
      by inversion sc2.
Qed.

Lemma count_expand : forall (c1 c2 : bitseq),
  size c2 = count negb c1 ->
  count id (expand c1 c2) = count id c1 + count id c2.
Proof.
elim => [|[] c1 IH] [|[] c2] //= sc.
 all: try rewrite IH => //= try addnA try addnCA.
  rewrite IH //=.
  by rewrite addnA add0n addnCA -addnA.
  by inversion sc.
  by rewrite IH => //=; inversion sc.
Qed.

Lemma shuffle_assoc_l {A : Type} n m p (l1 : n.-tuple A) (l2 : m.-tuple A) 
  (l3 : p.-tuple A) (l' : (m+p).-tuple A) (l : (n+m+p).-tuple A) :
  shuffle l1 l' l -> shuffle l2 l3 l' ->
  { l'' : (n+m).-tuple A & shuffle l1 l2 l'' * shuffle l'' l3 l }.
Proof.
move=> [c1 [Hs1 [Hl1 Hr1]]] [c2 [Hs2 [Hl2 Hr2]]].
have Hec : size c2 = count negb c1.
  rewrite -Hr1 in Hs2; rewrite size_mask in Hs2; last by rewrite size_map.
  by rewrite Hs2 count_map; apply eq_count => x /=.
have Hse : size (expand c1 c2) = size l by rewrite size_expand // -Hs1.
have Hmaskr : mask [seq ~~ i | i <- expand c1 c2] l = l3.
  by rewrite mask_expand_r // Hr1 Hr2.
have Hsize_l'' : size (mask (expand c1 c2) l) = n + m.
  rewrite size_mask // count_expand //.
  by rewrite -[n](size_tuple l1) -Hl1 size_mask // 
        -[m](size_tuple l2) -Hl2 size_mask //.
move: Hsize_l'' => /eqP Hsize_l'' /=.
exists (Tuple Hsize_l'') => //=.
split.
  exists (mask (expand c1 c2) c1); split ; [|split].
    by rewrite !size_mask // size_expand // Hs1.
    by rewrite mask_expand_l // -Hs1 // -Hec // Hl1.
    by rewrite expand_mask_r //= Hr1 Hl2.
exists (expand c1 c2); split; [|split].
    by rewrite Hse size_tuple.
    by [].
    exact: Hmaskr.
Qed.

Lemma shuffle_assoc_r {A : Type} n m p (l1 : n.-tuple A) (l2 : m.-tuple A) 
  (l3 : p.-tuple A) (l' : (n+m).-tuple A) (l : (n+m+p).-tuple A) :
  shuffle l1 l2 l' -> shuffle l' l3 l ->
  { l'' : (m+p).-tuple A & shuffle l2 l3 l'' * shuffle l1 l'' l }.
Proof.
move=> [c1 [Hs1 [Hl1 Hr1]]] [c2 [Hs2 [Hl2 Hr2]]].
have Hec : size (map negb c1) = count negb (map negb c2).
  rewrite size_map count_map //=.
  have ee : count (preim negb negb) c2 = count id c2 by apply eq_count => x /=; rewrite negbK.
  by rewrite ee -(size_mask Hs2) Hl2 Hs1.
have Hse : size (expand (map negb c2) (map negb c1)) = size l.
  by rewrite size_expand // size_map.
have Hsize_l'' : size (mask (expand (map negb c2) (map negb c1)) l) = m + p.
  rewrite size_mask // count_expand // !count_map /=.
  have e1 : count negb c2 = size l3.
    rewrite -Hr2 size_mask => //=; last by rewrite -Hs2 size_map.
    by rewrite count_map.
  have e2 : count negb c1 = size l2.
    rewrite -Hr1 size_mask //=; last by rewrite -Hs1 size_map.
    by rewrite count_map.
  by rewrite e1 e2 !size_tuple addnC.
exists (Tuple (introT eqP Hsize_l'')).
split.
  exists [seq ~~ i | i <- mask (expand (map negb c2) (map negb c1)) (map negb c2)].
  split; [|split] => //=.
    by rewrite size_map !size_mask // size_expand // size_map.
    rewrite expand_mask_r /= ?size_map => //=; last first => /=.
      rewrite count_map /=.
      have ee : count (preim negb negb) c2 = count id c2 by apply eq_count => x /=; rewrite negbK.
    by rewrite ee -(size_mask Hs2) Hl2 Hs1.
    rewrite -Hr1 /= mapK //= ?negbK /=; last by move => x; rewrite negbK => //.
    by rewrite -Hl2.
  rewrite mapK /=; last by move => x; rewrite negbK.
  by rewrite mask_expand_l // ?size_map //.
exists [seq ~~ i | i <- expand [seq ~~ i | i <- c2] [seq ~~ i | i <- c1]].
split; [|split] => //=.
  by rewrite size_map Hse size_tuple.
  rewrite -Hl1 mask_expand_r /= ?size_map //.
    rewrite mapK /= ?negbK => //=; last by move => x; rewrite negbK.
    rewrite mapK => //=; last by move => x; rewrite negbK => //=.
    by rewrite Hl2.
    by rewrite -Hec size_map.
by rewrite mapK => //=; last by move => x; rewrite negbK.
Qed.

Lemma shuffle_assoc {A : Type} n m p (l1 : n.-tuple A) (l2 : m.-tuple A) 
  (l3 : p.-tuple A) (l : (n+m+p).-tuple A) :
  iffT { l' : (n+m).-tuple A & shuffle l1 l2 l' * shuffle l' l3 l }
  { l'' : (m+p).-tuple A & shuffle l2 l3 l'' * shuffle l1 l'' l }.
Proof.
split.
  move => [l' [s1 s2]].
  by apply shuffle_assoc_r with l'.
  move => [l'' [s1 s2]].
  by apply shuffle_assoc_l with l''.
Qed.

Lemma perm_mask {A : eqType} (c : bitseq) (l : seq A) :
  size c = size l ->
  perm_eq (mask c l ++ mask (map negb c) l) l.
Proof.
elim: c l.
  by move=> [].
  move=> [|] c IH [|a l] //= [Hsc].
    by rewrite /= perm_cons; exact: IH.
    by rewrite /= perm_catC /= perm_cons perm_catC; exact: IH.
Qed.

Lemma shuffle_perm {A : eqType} n m (l1 : n.-tuple A) (l2 : m.-tuple A) 
(l3 : (n+m).-tuple A) : shuffle l1 l2 l3 -> perm_eq (l1 ++ l2) l3.
Proof.
by move=> [c [Hsc [Hmc Hnmc]]]; rewrite -Hmc -Hnmc; exact: perm_mask.
Qed.

Lemma shuffle_app_app {A : Type} (l1 l2 l3 l1' l2' l3' : seq A) :
  shuffle l1 l2 l3 -> shuffle l1' l2' l3' ->
  shuffle (l1 ++ l1') (l2 ++ l2') (l3 ++ l3').
Proof.
move=> [c [Hsc [Hmc Hnmc]]] [c' [Hsc' [Hmc' Hnmc']]].
exists (c ++ c'); split; [|split] => //=.
  by rewrite !size_cat Hsc Hsc'.
  by rewrite mask_cat // Hmc Hmc' // Hsc.
  rewrite map_cat mask_cat; last by rewrite size_map Hsc.
  by rewrite Hnmc Hnmc'.
Qed.

Lemma shuffle_to_shuffleT {A : Type} (l1 l2 l3 : seq A) :
  shuffle l1 l2 l3 ->  shuffleT l1 l2 l3.
Proof.
move=> [c [Hsc [Hmc Hnmc]]].
elim: l3 l1 l2 c Hsc Hmc Hnmc.
  move=> l1 l2 c Hsc Hmc Hnmc.
    by rewrite (size0nil Hsc) /= in Hmc Hnmc; rewrite -Hmc -Hnmc; exact: shuffleT_nil.
move=> a l3 IH l1 l2 [|[|] c] //= Hsc Hmc Hnmc.
case: l1 Hmc => //= b l1 [<- Hmc].
  by apply: shuffleT_l => //=; exact: IH l1 l2 c (succn_inj Hsc) Hmc Hnmc.
move: Hsc => /= [].
case: l2 Hnmc => //= b l2 [<- Hnmc].
move => ss.
by apply: shuffleT_r; exact: IH l1 l2 c ss Hmc Hnmc.
Qed.

Lemma shuffleT_to_shuffle {A : Type} (l1 l2 l3 : seq A) :
  shuffleT l1 l2 l3 -> shuffle l1 l2 l3.
Proof.
elim.
  exact: (existT _ [::] (conj erefl (conj erefl erefl))).
  move=> a l1' l2' l3' _ [c [Hsc [Hmc Hnmc]]].
  exact: (existT _ (true :: c) (conj (congr1 S Hsc) (conj (congr1 (cons a) Hmc) Hnmc))).
  move=> a l1' l2' l3' _ [c [Hsc [Hmc Hnmc]]].
  exact: (existT _ (false :: c) (conj (congr1 S Hsc) (conj Hmc (congr1 (cons a) Hnmc)))).
Qed.

Lemma shuffle_app_inv {A : Type} (l1 l2 p q : seq A) :
  shuffle l1 l2 (p ++ q) ->
  { l1' & { l1'' & { l2' & { l2'' &
    (l1 = l1' ++ l1'') * (l2 = l2' ++ l2'') *
    shuffle l1' l2' p * shuffle l1'' l2'' q }}}}.
Proof.
move => s.
elim : s.
  move => x [si [m1 m2]].
  set l1'  := mask (take (size p) x) p.
  exists (mask (take (size p) x) p),
       (mask (drop (size p) x) q),
       (mask [seq ~~ i | i <- take (size p) x] p),
       (mask [seq ~~ i | i <- drop (size p) x] q).
  have szp : size (take (size p) x) = size p by rewrite size_takel // si size_cat leq_addr.
  have szq : size (drop (size p) x) = size q by rewrite size_drop si size_cat addKn.
  do !split.
    rewrite -m1 -mask_cat. 
    by rewrite cat_take_drop.
    by rewrite size_takel // si size_cat leq_addr.
    rewrite -m2.
    rewrite -mask_cat; last by rewrite size_map size_takel // si size_cat leq_addr.
    by rewrite -map_cat cat_take_drop.
    by exists (take (size p) x); rewrite ?szp.
    by exists (drop (size p) x); rewrite ?szq.
Qed.

Lemma shuffle_cat_swap {A : Type} (a c s1 a' c' s2 : seq A) :
  shuffle a c s1 -> shuffle a' c' s2 ->
  shuffle (a' ++ a) (c' ++ c) (s2 ++ s1).
Proof.
move=> [bs1 [Hs1 [Hm11 Hm21]]] [bs2 [Hs2 [Hm12 Hm22]]].
exists (bs2 ++ bs1); split; [|split].
  by rewrite !size_cat Hs2 Hs1 addnC.
  by rewrite mask_cat ?Hm12 ?Hm11 // Hs2.
  by rewrite map_cat mask_cat ?Hm22 ?Hm21 // size_map Hs2.
Qed.
