From mathcomp Require Import all_boot.
From mathcomp.zify Require Import zify.
From OLlibs Require Import Logic_Datatypes_more.
Import LogicNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section helper.

Lemma count_negb (s : bitseq) : count negb s = size s - count id s.
Proof.
by rewrite -[size s](count_predC id) addKn.
Qed.

Fixpoint merge_seq {A} (c : bitseq) l1 l2 : seq A :=
  match c, l1, l2 with
  | [::], _, _=> [::]
  | true :: c', h :: t, _=> h :: merge_seq c' t  l2
  | false :: c', _, h :: t  => h :: merge_seq c' l1 t
  | _, _, _ => [::]
  end.

Lemma size_merge_seq {A} c (l1 l2 : seq A) :
  count id c = size l1 -> count negb c = size l2 ->
  size (merge_seq c l1 l2) = size c.
Proof.
elim: c l1 l2 => [|[] c IH] [|a1 l1] [|a2 l2] //= h1 h2.
all: rewrite IH //; lia.
Qed.

Lemma merge_seq_mask {A} (c : bitseq) (l : seq A) :
  size c = size l ->
  merge_seq c (mask c l) (mask (map negb c) l) = l.
Proof.
elim: c l => [|[] c IH] [|a l] //= [hs].
all : by rewrite IH.
Qed.

Lemma mask_merge_seq_l {A} (c : bitseq) (l1 l2 : seq A) :
  count id c = size l1 -> count negb c = size l2 ->
  mask c (merge_seq c l1 l2) = l1.
Proof.
elim: c l1 l2 => [|[] c IH] [|a1 l1] [|a2 l2] //= h1 h2.
all: rewrite IH => //=; lia.
Qed.

Lemma mask_merge_seq_r {A} (c : bitseq) (l1 l2 : seq A) :
  count id c = size l1 -> count negb c = size l2 ->
  mask (map negb c) (merge_seq c l1 l2) = l2.
Proof.
elim: c l1 l2 => [|[] c IH] [|a1 l1] [|a2 l2] //= h1 h2.
all: rewrite IH => //=; lia.
Qed.

Lemma merge_seq_neg {A} (c : bitseq) (l1 l2 : seq A) :
  merge_seq (map negb c) l2 l1 = merge_seq c l1 l2.
Proof.
  elim: c l1 l2 => [|[] c' IH] [|h1 t1] [|h2 t2] //=.
  all: by rewrite IH.
Qed.

End helper.

Record Merge (n m : nat) := MkMerge {
  mcode        :> bitseq;                     (* TODO remove some mcode: coercion *)
  mcode_size   : size mcode == n + m;
  mcode_count  : count id mcode == n;
}.

Definition shuffle n m (n' : Merge n m) : (n+m).-tuple bool :=
  Tuple (mcode_size n').

Section expand. 

Fixpoint expand (c1 c2 : bitseq) : bitseq :=
  match c1, c2 with
  | [::],          _        => [::]
  | true  :: c1',  c2       => true  :: expand c1' c2
  | false :: c1',  b :: c2' => b     :: expand c1' c2'
  | false :: c1',  [::]     => false :: expand c1' [::] (* [::] *)
  end.

Lemma size_expand (c1 c2 : bitseq) :
  size c2 = count negb c1 ->
  size (expand c1 c2) = size c1.
Proof.
move: c1 c2. (* TODO integrate in next line *)
elim => [|b c1 IH] [|x c2] //= Hs.
  case: b Hs => //= Hs; by rewrite IH.
  by case: b Hs => //= Hs; [rewrite IH| rewrite IH; inversion Hs] => //=.
Qed.

Lemma count_expand (c1 c2 : bitseq) :
  size c2 = count negb c1 ->
  count id (expand c1 c2) = count id c1 + count id c2.
Proof.
move: c1 c2. (* TODO integrate in next line *)
elim => [|[] c1 IH] [|[] c2] //= sc.
 all: try rewrite IH => //= try addnA try addnCA.
  rewrite IH //=.
  by rewrite addnA add0n addnCA -addnA.
  by inversion sc.
  by rewrite IH => //=; inversion sc.
Qed.

Lemma merge_seq_assoc {A} (c1 c2 : bitseq) (l1 l2 l3 : seq A) :
  size c2 = count negb c1 ->
  count id c1 = size l1 ->
  count id c2 = size l2 ->
  merge_seq c1 l1 (merge_seq c2 l2 l3) =
  merge_seq (expand c1 c2) (merge_seq (mask (expand c1 c2) c1) l1 l2) l3.
Proof.
elim: c1 c2 l1 l2 l3 => [|[] c1' IH] [|[] c2'] [|h1 t1] [|h2 t2] [|h3 t3] //=
    => Hec Hl1 Hl2 ; try discriminate. 
all: rewrite -IH //=; lia.
Qed.

Lemma count_expand_mask (c1 c2 : bitseq) :
  size c2 = count negb c1 ->
  count id (mask (expand c1 c2) c1) = count id c1.
Proof.
  elim: c1 c2 => [|[] c1' IH] [|[] c2'] //= Hec;
  rewrite IH // ?count_negb //=.
  all: rewrite count_negb in Hec; lia.
Qed.

End expand.

Section seqLevel.

Definition split1 {A} {n m} (s: Merge n m) (l : seq A) := (mask (mcode s) l).

Definition split2 {A} {n m} (s: Merge n m) (l : seq A) := 
  (mask (map negb (mcode s)) l).

Definition splits {A} {n m} (s : Merge n m) (l : seq A) := (split1 s l, split2 s l).

Definition shuffling {A} n m (l1 l2 l3 : seq A) :=
  { s : Merge n m | l3 = merge_seq s l1 l2 }.

Lemma thm {A} {n m} (s : Merge n m) (l : seq A) : 
  (size l) = n + m -> merge_seq s (split1 s l) (split2 s l) = l.
Proof.
move => si.
rewrite (@merge_seq_mask _ (mcode s) ) => //=.
by rewrite (eqP (mcode_size s)).
Qed.

Lemma thm2 {A} {n m} (s : Merge n m) (l1 l2 : seq A) :
  n = size l1 -> m = size l2 ->
  split1 s (merge_seq s l1 l2) = l1. 
Proof.
move => sl1 sl2.
apply mask_merge_seq_l => //=.
  by rewrite (eqP (mcode_count s)).
  by rewrite count_negb ?size_tuple (eqP (mcode_size s)) (eqP (mcode_count s)) addKn.
Qed.

Lemma thm3 {A} {n m} (s : Merge n m) (l1 l2 : seq A) :
  n = size l1 -> m = size l2 -> 
  split2 s (merge_seq s l1 l2) = l2.
Proof.
move => sl1 sl2.
apply mask_merge_seq_r => //=.
  by rewrite (eqP (mcode_count s)).
  by rewrite count_negb ?size_tuple (eqP (mcode_size s)) (eqP (mcode_count s)) addKn.
Qed.

Definition shuffle_neg {n m} (s : Merge n m) : Merge m n.
Proof.
apply (@MkMerge m n (map negb (mcode s))).
  by rewrite size_map; rewrite (eqP (mcode_size s)) addnC.
  by rewrite count_map ?count_negb ?(eqP (mcode_size s)) ?(eqP (mcode_count s)) addKn.
Defined.

Lemma shuffling_comm {A} {n m : nat} (l1 l2 l3 : seq A) :
  shuffling n m l1 l2 l3 <=> shuffling m n l2 l1 l3.
Proof.
split; move => [s hs].
all: by exists (shuffle_neg s); rewrite hs merge_seq_neg.
Qed.

Lemma shuffling_assoc_l {A} {n m p} (l1 l2 l3 l' l : seq A) :
  size l1 = n -> size l2 = m ->
  shuffling n (m+p) l1 l' l -> shuffling m p l2 l3 l' ->
  { l'' & shuffling n m l1 l2 l'' & shuffling (n+m) p l'' l3 l }.
Proof.
move=> sl1 sl2 [s1 hs1] [s2 hs2].
have Hec : size (mcode s2) = count negb (mcode s1).
  by rewrite count_negb (eqP (mcode_size s1)) (eqP (mcode_count s1))
             (eqP (mcode_size s2)) addKn.
have Hsize12 : size (mask (expand (mcode s1) (mcode s2)) (mcode s1)) == n + m.
  rewrite size_mask //=.
  by rewrite count_expand // (eqP (mcode_count s1)) (eqP (mcode_count s2)).
  by rewrite size_expand.
have Hcount12 : count id (mask (expand (mcode s1) (mcode s2)) (mcode s1)) == n.
  by rewrite count_expand_mask // (eqP (mcode_count s1)).
exists (merge_seq (mask (expand (mcode s1) (mcode s2)) (mcode s1))
                        l1 l2).
  by exists (MkMerge Hsize12 Hcount12).
  have Hsize123 : size (expand (mcode s1) (mcode s2)) == n + m + p.
    by rewrite size_expand // (eqP (mcode_size s1)) addnA.
  have Hcount123 : count id (expand (mcode s1) (mcode s2)) == n + m.
    by rewrite count_expand // (eqP (mcode_count s1)) (eqP (mcode_count s2)) //=.
  exists (MkMerge Hsize123 Hcount123).
  rewrite hs2 in hs1.
  rewrite hs1 /= merge_seq_assoc //=.
    by rewrite (eqP (mcode_count s1)) //.
    by rewrite (eqP (mcode_count s2)) //.
Qed.

Lemma shuffling_assoc_r {A} {n m p} (l1 l2 l3 l' l : seq A) :
  size l2 = m -> size l3 = p ->
  shuffling n m l1 l2 l' -> shuffling (n+m) p l' l3 l ->
  { l'' & shuffling m p l2 l3 l'' & shuffling n (m+p) l1 l'' l }.
Proof.
move=> sl2 sl3 [s1 hs1] [s2 hs2].
set nc2 := mcode (shuffle_neg s2).
set nc1 := mcode (shuffle_neg s1).
have Hnc2 : mcode s2 = [seq ~~ i | i <- nc2].
  by rewrite /nc2 /= -map_comp (eq_map negbK) map_id.
have Hnc1 : mcode s1 = [seq ~~ i | i <- nc1].
  by rewrite /nc1 /= -map_comp (eq_map negbK) map_id.
have Hec : size nc1 = count negb nc2.
  rewrite count_negb /nc1 /nc2 !size_map count_map count_negb.
  by rewrite (eqP (mcode_size s2)) (eqP (mcode_size s1))
             (eqP (mcode_count s2)) !addKn addnK.
exists (merge_seq [seq ~~ i | i <- mask (expand nc2 nc1) nc2] l2 l3).
  have Hsize23 : size [seq ~~ i | i <- mask (expand nc2 nc1) nc2] == m + p.
    rewrite size_map size_mask //.
    rewrite count_expand //=.
    rewrite /nc2 count_map count_negb /nc1 count_map count_negb.
    by rewrite (eqP (mcode_size s2)) (eqP (mcode_count s2)) addKn
                 (eqP (mcode_size s1)) (eqP (mcode_count s1)) addKn addnC.
    by rewrite size_expand // /nc2 size_map (eqP (mcode_size s2)).
  have Hcount23 : count id [seq ~~ i | i <- mask (expand nc2 nc1) nc2] == m.
    rewrite count_map count_negb size_mask //.
    rewrite count_expand // count_expand_mask //.
    rewrite /nc2 count_map count_negb /nc1 count_map count_negb.
    by rewrite (eqP (mcode_size s2)) (eqP (mcode_count s2)) addKn
                 (eqP (mcode_size s1)) (eqP (mcode_count s1)) addKn.
    by rewrite size_expand // /nc2 size_map (eqP (mcode_size s2)).
    by exists (MkMerge Hsize23 Hcount23).
  have Hsize1 : size [seq ~~ i | i <- expand nc2 nc1] == n + (m + p).
    by rewrite size_map size_expand // /nc2 size_map (eqP (mcode_size s2)) addnA.
  have Hcount1 : count id [seq ~~ i | i <- expand nc2 nc1] == n.
    rewrite count_map count_negb size_expand // count_expand //.
    rewrite /nc2 count_map count_negb /nc1 count_map count_negb size_map.
    rewrite (eqP (mcode_size s2)) (eqP (mcode_count s2)) addKn
            (eqP (mcode_size s1)) (eqP (mcode_count s1)) !addKn -addnA.
    by rewrite (addnC m) addnK.
  exists (MkMerge Hsize1 Hcount1).
  rewrite hs2 hs1 Hnc2 Hnc1.
  rewrite merge_seq_neg (merge_seq_neg nc1).
  rewrite merge_seq_assoc //.
    by rewrite !merge_seq_neg.
    by rewrite /nc2 count_map count_negb (eqP (mcode_size s2))
               (eqP (mcode_count s2)) addKn sl3. 
    by rewrite /nc1 count_map count_negb (eqP (mcode_size s1))
               (eqP (mcode_count s1)) addKn sl2. 
Qed.

Lemma shuffling_assoc {A} {n m p} (l1 l2 l3 l : seq A) :
  size l1 = n -> size l2 = m -> size l3 = p ->
      { l' & shuffling n m l1 l2 l' & shuffling (n+m) p l' l3 l }
  <=> { l'' & shuffling m p l2 l3 l'' & shuffling n (m+p) l1 l'' l }.
Proof.
move => sl1 sl2 sl3.
split.
  move => [l' s1 s2].
  by apply shuffling_assoc_r with l'.
  move => [l'' s1 s2].
  by apply shuffling_assoc_l with l''.
Qed.

Lemma merge_seq_comm {A} {n m} (s : Merge n m) (l1 l2 : seq A) :
  merge_seq s l1 l2 = merge_seq (shuffle_neg s) l2 l1.
Proof. by rewrite merge_seq_neg. Qed. (* TODO same as merge_seq_neg? *)

End seqLevel.

Section tupleLevel.

Definition split1_tuple {A} {n m} (s: Merge n m) (l : (n+m).-tuple A) : n.-tuple A.
Proof.
refine (Tuple (tval := mask s l)_ ) => //.
rewrite size_mask //=. 
by rewrite (eqP (mcode_count s)).
by rewrite size_tuple (eqP (mcode_size s)).
Defined.

Definition split2_tuple {A} {n m} (s : Merge n m) (l : (n+m).-tuple A) : m.-tuple A.
Proof.
refine (Tuple (tval := mask (map negb (mcode s)) l )_ ).
rewrite size_mask ?size_tuple //= ?size_map; last first.
  by rewrite (eqP (mcode_size s)).
rewrite count_map ?count_negb ?(eqP (mcode_size s)) ?(eqP (mcode_count s)).
by rewrite addKn.
Defined.

Definition split_tuple {A} {n m} (s : Merge n m) (l : (n+m).-tuple A) :
  n.-tuple A * m.-tuple A := 
  (split1_tuple s l, split2_tuple s l). (* TODO split left and right components *)

Definition merge_tuple {A} {n m} (s : Merge n m) (l1 : n.-tuple A) (l2 : m.-tuple A) :
  (n+m).-tuple A.
Proof.
refine (Tuple (tval := merge_seq (mcode s) l1 l2) _).
have ss := (mcode_size s).
rewrite size_merge_seq => //=.
by rewrite (eqP (mcode_count s)) ?size_tuple.
rewrite count_negb (eqP (mcode_count s)) size_tuple.
move/eqP : ss ->.
by rewrite addKn.
Defined.

Lemma thm_tuple {A} {n m} (s : Merge n m) (l : (n+m).-tuple A) :
  merge_tuple s (split1_tuple s l) (split2_tuple s l) = l.
Proof.
apply/val_inj => //=.
rewrite thm => //=.
by rewrite size_tuple. 
Qed.

Lemma thm2_tuple {A} {n m} (s : Merge n m) (l1 : n.-tuple A) (l2 : m.-tuple A) :
  split1_tuple s (merge_tuple s l1 l2) = l1. 
Proof.
apply/val_inj => //=.
apply thm2 => //.
all: try by rewrite ?size_tuple.
Qed.

Lemma thm3_tuple {A} {n m} (s : Merge n m) (l1 : n.-tuple A) (l2 : m.-tuple A) :
  split2_tuple s (merge_tuple s l1 l2) = l2.
Proof.
apply/val_inj => //=.
apply/thm3 => //.
all: try by rewrite size_tuple.
Qed.

Definition shuffling_tuple {A} {n m} (l1 : n.-tuple A) (l2 : m.-tuple A) (l3 : (n+m).-tuple A) :=
  { s : Merge n m  | l3 = merge_tuple s l1 l2 }.

Lemma merge_tuple_tval {A} {n m} (s : Merge n m) (l1 : n.-tuple A) (l2 : m.-tuple A) :
  tval (merge_tuple s l1 l2) = merge_seq s (tval l1) (tval l2).
Proof. by []. Qed.

Lemma merge_tuple_comm {A} {n m} (s : Merge n m) (l1 : n.-tuple A) (l2 : m.-tuple A) :
  tcast (addnC n m) (merge_tuple s l1 l2) = merge_tuple (shuffle_neg s) l2 l1.
Proof.
apply: val_inj => //=.
by rewrite !val_tcast -merge_seq_comm.
Qed.

Lemma shuffling_tuple_comm {A} {n m} (l1 : n.-tuple A) (l2 : m.-tuple A) l3 :
  shuffling_tuple l1 l2 l3 <=> shuffling_tuple l2 l1 (tcast (addnC n m) l3).
Proof.
split; move => [s hs].
all: by exists (shuffle_neg s); rewrite -merge_tuple_comm -hs -?tcast_trans ?tcast_id=> //.
Qed.

Lemma shuffling_assoc_l_tuple {A} {n m p} (l1 : n.-tuple A) (l2 : m.-tuple A)
  (l3 : p.-tuple A) (l' : (m+p).-tuple A) (l : (n+m+p).-tuple A) :
  shuffling_tuple l1 l' (tcast (esym (addnA n m p)) l) -> shuffling_tuple l2 l3 l' ->
  { l'' : (n+m).-tuple A & shuffling_tuple l1 l2 l'' & shuffling_tuple l'' l3 l }.
Proof.
move=> [s1 hs1] [s2 hs2].
have Hseq1 : shuffling n (m+p) (tval l1) (tval l') (tval l).
  exists s1.
  have := congr1 val hs1 => //=. 
  by rewrite val_tcast.
have Hseq2 : shuffling m p (tval l2) (tval l3) (tval l').
  exists s2.
  rewrite -merge_tuple_tval.
  by rewrite hs2.
have [lseq H1 H2] :=
  shuffling_assoc_l (size_tuple l1) (size_tuple l2) Hseq1 Hseq2.
have [s' hs'] := H1.
have [s'' hs''] := H2.
exists (merge_tuple s' l1 l2).
- by exists s'.
- exists s''.
  apply val_inj => /=.
  by rewrite hs'' hs'.
Qed.

Lemma shuffling_assoc_r_tuple {A} {n m p} (l1 : n.-tuple A) (l2 : m.-tuple A)
  (l3 : p.-tuple A) (l' : (n+m).-tuple A) (l : (n+m+p).-tuple A) :
  shuffling_tuple l1 l2 l' -> shuffling_tuple l' l3 l ->
  { l'' : (m+p).-tuple A & shuffling_tuple l2 l3 l'' & shuffling_tuple l1 l'' (tcast (esym (addnA n m p)) l) }.
Proof.
move=> [s1 hs1] [s2 hs2].
have Hseq1 : shuffling n m (tval l1) (tval l2) (tval l').
  exists s1.
  rewrite -merge_tuple_tval.
  by rewrite hs1.
have Hseq2 : shuffling (n+m) p (tval l') (tval l3) (tval l).
  exists s2.
  rewrite -merge_tuple_tval.
  by rewrite hs2.
have [lseq H1 H2] :=
  shuffling_assoc_r (size_tuple l2) (size_tuple l3) Hseq1 Hseq2.
have [s' hs'] := H1.
have [s'' hs''] := H2.
exists (merge_tuple s' l2 l3).
- by exists s'.
- exists s''.
  apply val_inj => /=.
  rewrite val_tcast.
  by rewrite hs'' hs'.
Qed.

Lemma shuffling_assoc_tuple {A} n m p (l1 : n.-tuple A) (l2 : m.-tuple A) 
  (l3 : p.-tuple A) (l : (n+m+p).-tuple A) :
      { l' : (n+m).-tuple A & shuffling_tuple l1 l2 l' & shuffling_tuple l' l3 l }
  <=> { l'' : (m+p).-tuple A & shuffling_tuple l2 l3 l'' & shuffling_tuple l1 l'' (tcast (esym (addnA n m p)) l )}.
Proof.
split.
  move => [l' s1 s2].
  by apply shuffling_assoc_r_tuple with l'.
  move => [l'' s1 s2].
  by apply shuffling_assoc_l_tuple with l''.
Qed.

End tupleLevel.
