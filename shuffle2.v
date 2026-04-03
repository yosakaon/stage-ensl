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
all: try rewrite IH //; lia. 
Qed.

Lemma merge_seq_mask {A} (c : bitseq) (l : seq A) :
  size c = size l ->
  merge_seq c (mask c l) (mask (map negb c) l) = l.
Proof.
elim: c l => [|[] c IH] [|a l] //= [hs].
all : try by rewrite IH.
Qed.

Lemma mask_merge_seq_l {A} (c : bitseq) (l1 l2 : seq A) :
  count id c = size l1 -> count negb c = size l2 ->
  mask c (merge_seq c l1 l2) = l1.
Proof.
elim: c l1 l2 => [|[] c IH] [|a1 l1] [|a2 l2] //= h1 h2.
all: try rewrite IH => //=; lia.
Qed.

Lemma mask_merge_seq_r {A} (c : bitseq) (l1 l2 : seq A) :
  count id c = size l1 -> count negb c = size l2 ->
  mask (map negb c) (merge_seq c l1 l2) = l2.
Proof.
elim: c l1 l2 => [|[] c IH] [|a1 l1] [|a2 l2] //= h1 h2.
all: try rewrite IH => //=; lia.
Qed.

Lemma merge_seq_neg {A} (c : bitseq) (l1 l2 : seq A) :
  merge_seq (map negb c) l2 l1 = merge_seq c l1 l2.
Proof.
elim: c l1 l2 => [|[] c' IH] [|h1 t1] [|h2 t2] //=.
all: by rewrite IH.
Qed.

End helper.

Record Merge (n m : nat) := MkMerge {
  mcode        :> bitseq;           
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
  | false :: c1',  [::]     => [::] 
  end.


Lemma size_expand (c1 c2 : bitseq) :
  size c2 = count negb c1 ->
  size (expand c1 c2) = size c1.
Proof.
elim: c1 c2 => [|[] c1 IH] [|[] c2] //= sc.
all: rewrite IH => //; lia.
Qed.

Lemma count_expand (c1 c2 : bitseq) : 
  size c2 = count negb c1 ->
  count id (expand c1 c2) = count id c1 + count id c2.
Proof.
elim: c1 c2 => [|[] c1 IH] [|[] c2] //= sc.
all: rewrite IH => //; lia.
Qed.

Lemma merge_seq_cat {A} (s s' : bitseq) (l1 l2 l1' l2' : seq A) :
  count id s = size l1 -> count negb s = size l2 ->
  merge_seq (s ++ s') (l1 ++ l1') (l2 ++ l2') = 
  merge_seq s l1 l2 ++ merge_seq s' l1' l2'.
Proof.
elim: s l1 l2 => [|[] s IH] [|a1 l1] [|a2 l2] //= h1 h2.
all: congr cons. 
all: rewrite -IH => //=; lia.
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

(*
Ltac merge_size :=
  repeat ( rewrite ?size_map ?size_mask ?size_tuple ?count_map ?count_negb 
            ?size_merge_seq ?size_expand ?count_expand ?count_expand_mask
            ?(eq_count (fun x => negbK x)) ?count_cat ?size_cat;
    repeat match goal with
    | s : Merge _ _ |- _ =>
        progress first [ rewrite (eqP (mcode_size s))
                       | rewrite (eqP (mcode_count s)) ]
    end
  );
  try lia.
*)
Ltac merge_size :=
  repeat ( rewrite ?size_map ?size_mask ?size_tuple ?count_map ?count_negb 
            ?size_merge_seq
            ?(fun s => eqP (mcode_size s)) ?(fun s => eqP (mcode_count s))
            ?size_expand ?count_expand ?count_expand_mask
            ?(eq_count (fun x => negbK x)) ?count_cat ?size_cat);
  try reflexivity;
  try lia.
Ltac merge_size_clear :=
  clear;
  repeat ( rewrite ?size_map ?size_mask ?size_tuple ?count_map ?count_negb 
            ?size_merge_seq
            ?(fun s => eqP (mcode_size s)) ?(fun s => eqP (mcode_count s))
            ?size_expand ?count_expand ?count_expand_mask
            ?(eq_count (fun x => negbK x)) ?count_cat ?size_cat);
  try reflexivity;
  lia.
Section seqLevel.

Definition split1 {A} {n m} (s: Merge n m) (l : seq A) := (mask s l).

Definition split2 {A} {n m} (s: Merge n m) (l : seq A) := 
  (mask (map negb (mcode s)) l).

Definition splits {A} {n m} (s : Merge n m) (l : seq A) := (split1 s l, split2 s l).

Definition shuffling {A} n m (l1 l2 l3 : seq A) :=
  { s : Merge n m & l3 = merge_seq s l1 l2 & ((size l1 = n) * (size l2 = m))%type }.

Lemma shuffling_splits_iff {A} {n m} (l1 l2 l3 : seq A) :
  shuffling n m l1 l2 l3 <=>
  {s : Merge n m | splits s l3 = (l1, l2) & size l3 = n + m }.
Proof.
split.
  move=> [s hs [sl1 sl2]].
  exists s.
  rewrite /splits /split1 /split2 hs.
  rewrite mask_merge_seq_l //=.
  rewrite mask_merge_seq_r //; merge_size.
  all: try merge_size.
  by rewrite hs; merge_size.
  move=> [s [hsplit hsize]].
  exists s.
  rewrite /splits /split1 /split2 in hsplit.
     rewrite -hsplit -hsize merge_seq_mask //.
     all: try merge_size.
  do !split.
     rewrite -hsplit /=. 
     rewrite size_mask => //.
     all: try merge_size.
  rewrite -hsize.
  merge_size.
Qed.

Lemma shuffling_splits {A} {n m} (s : Merge n m) (l3 : seq A) :
  size l3 = n + m ->
  shuffling n m (split1 s l3) (split2 s l3) l3.
Proof.
Proof.
move=> hs; apply shuffling_splits_iff.
by exists s.
Qed.

Lemma thm {A} {n m} (s : Merge n m) (l : seq A) : 
  size l = n + m -> merge_seq s (split1 s l) (split2 s l) = l.
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
apply: mask_merge_seq_l => //=; merge_size.
Qed.

Lemma thm3 {A} {n m} (s : Merge n m) (l1 l2 : seq A) :
  n = size l1 -> m = size l2 -> 
  split2 s (merge_seq s l1 l2) = l2.
Proof.
move => sl1 sl2.
by apply: mask_merge_seq_r => //=; merge_size.
Qed.

Definition shuffle_neg {n m } (s : Merge n m ) : Merge m n.
Proof.
by apply (@MkMerge m n (map negb (mcode s))); merge_size.
Defined.

Lemma shuffling_comm {A} {n m : nat} (l1 l2 l3 : seq A) :
  shuffling n m l1 l2 l3 <=> shuffling m n l2 l1 l3.
Proof.
split. 
move=> [s hs [sl1 sl2]].
exists (shuffle_neg s). 
all: rewrite ?hs ?merge_seq_neg; try split => //.
move=> [s hs [sl1 sl2]].
exists (shuffle_neg s); [ | split ].
all: by rewrite ?hs ?merge_seq_neg.
Qed.

Lemma shuffling_assoc_l {A} {n m p} (l1 l2 l3 l' l : seq A) :
  size l1 = n -> size l2 = m ->
  shuffling n (m+p) l1 l' l -> shuffling m p l2 l3 l' ->
  { l'' & shuffling n m l1 l2 l'' & shuffling (n+m) p l'' l3 l }.
Proof.
move=> sl1 sl2 [s1 hm1 [hs11 hs12]] [s2 hm2 [hs21 hs22]].
have Hec : size (mcode s2) = count negb (mcode s1).
  by merge_size.
have Hsize12 : size (mask (expand s1 s2) (mcode s1)) == n + m.
  merge_size => //=.
  rewrite ?count_expand ?size_expand ?merge_size => //=.
have Hcount12 : count id (mask (expand s1 s2) (mcode s1)) == n.
  by merge_size.
exists (merge_seq (mask (expand s1 s2) (mcode s1)) l1 l2).
  by exists (MkMerge Hsize12 Hcount12).
have Hsize123 : size (expand s1 s2) == n + m + p by merge_size.
have Hcount123 : count id (expand s1 s2) == n + m by merge_size.
exists (MkMerge Hsize123 Hcount123); [ | split ].
rewrite hm2 in hm1.
all: rewrite ?hm1 /= ?merge_seq_assoc //=; merge_size => //=.
Qed.

Lemma shuffling_assoc_r {A} {n m p} (l1 l2 l3 l' l : seq A) :
  size l2 = m -> size l3 = p ->
  shuffling n m l1 l2 l' -> shuffling (n+m) p l' l3 l ->
  { l'' & shuffling m p l2 l3 l'' & shuffling n (m+p) l1 l'' l }.
Proof.
move=> sl2 sl3 [s1 hm1 [hs11 hs12]] [s2 hm2 [hs21 hs22]].
set nc2 := mcode (shuffle_neg s2).
set nc1 := mcode (shuffle_neg s1).
have Hnc2 : mcode s2 = [seq ~~ i | i <- nc2].
  by rewrite /nc2 /= -map_comp (eq_map negbK) map_id.
have Hnc1 : mcode s1 = [seq ~~ i | i <- nc1].
  by rewrite /nc1 /= -map_comp (eq_map negbK) map_id.
have Hec : size nc1 = count negb nc2 by rewrite /nc1 /nc2; merge_size.
exists (merge_seq [seq ~~ i | i <- mask (expand nc2 nc1) nc2] l2 l3).
  have Hsize23 : size [seq ~~ i | i <- mask (expand nc2 nc1) nc2] == m + p. 
    by merge_size.
  have Hcount23 : count id [seq ~~ i | i <- mask (expand nc2 nc1) nc2] == m. 
  by rewrite /nc1 /nc2; merge_size => //=.
  by exists (MkMerge Hsize23 Hcount23).
have Hsize1 : size [seq ~~ i | i <- expand nc2 nc1] == n + (m + p) by merge_size.
have Hcount1 : count id [seq ~~ i | i <- expand nc2 nc1] == n.
  by rewrite /nc1 /nc2; merge_size.
exists (MkMerge Hsize1 Hcount1).
  rewrite hm2 hm1 Hnc2 Hnc1.
  rewrite merge_seq_neg (merge_seq_neg nc1).
  rewrite merge_seq_assoc //.
  4: split.
  all: move => //=.
  all: try merge_size.
  by rewrite !merge_seq_neg.
Qed.

Lemma shuffling_app_app {A} {n1 nm1 n2 nm2} 
    {l1 l2 l3 l1' l2' l3' : seq A} :
  shuffling n1 nm1 l1 l2 l3 ->
  shuffling n2 nm2 l1' l2' l3' ->
  shuffling (n1+n2) (nm1+nm2) (l1++l1') (l2++l2') (l3++l3').
Proof.
move=> [s hs [sl1 sl2]] [s' hs' [sl1' sl2']].
have hsize : size (mcode s ++ mcode s') == (n1+n2) + (nm1+nm2) by merge_size.
have hcount : count id (mcode s ++ mcode s') == n1+n2 by merge_size.
exists (MkMerge hsize hcount).
2: split => //.
all: try merge_size => //=.
by rewrite /= hs hs' merge_seq_cat; merge_size.
Qed.

Lemma shuffling_app_inv {A} {n m} {l1 l2 : seq A} (p q : seq A) :
  shuffling n m l1 l2 (p ++ q) ->
  { l1' & { l1'' & { l2' & { l2'' &
    (l1 = l1' ++ l1'') * (l2 = l2' ++ l2'') *
    shuffling (size l1') (size l2') l1' l2' p *
    shuffling (size l1'') (size l2'') l1'' l2'' q }}}}.
Proof.
move=> [s hs [sl1 sl2]].
set c := mcode s.
set c1 := take (size p) c.
set c2 := drop (size p) c.
set l1' := take (count id c1) l1.
set l1'' := drop (count id c1) l1.
set l2' := take (count negb c1) l2.
set l2'' := drop (count negb c1) l2.
have hc   : c = c1 ++ c2          by rewrite /c1 /c2 cat_take_drop.
have szc  : size c = size (p ++ q).
  by rewrite hs; merge_size.
have szc1 : size c1 = size p by rewrite /c1 size_takel // szc size_cat leq_addr.
have hle1 : count id c1 <= size l1.
have h : count id c1 + count id c2 = n
  by rewrite /c1 /c2 -count_cat cat_take_drop -(eqP (mcode_count s)).
lia.
have hle2 : count negb c1 <= size l2.
have h : count negb c1 + count negb c2 = m.
  by rewrite /c1 /c2 -count_cat cat_take_drop; merge_size.
lia.
have hl1  : l1 = l1' ++ l1'' by rewrite /l1' /l1'' cat_take_drop.
have hl2  : l2 = l2' ++ l2'' by rewrite /l2' /l2'' cat_take_drop.
have hcnt1 : count id c1 = size l1' by rewrite /l1' size_takel.
have hcnt2 : count negb c1 = size l2' by rewrite /l2' size_takel.
have hmerge : merge_seq c1 l1' l2' ++ merge_seq c2 l1'' l2'' = p ++ q.
  by rewrite -merge_seq_cat -?hc -?hl1 -?hl2 //; merge_size => //=; rewrite hs.
have hszp : size (merge_seq c1 l1' l2') = size p
  by rewrite size_merge_seq // -?hcnt1 -?hcnt2 ?count_negb; merge_size.
have hmerge1 : merge_seq c1 l1' l2' = p.
  have h := congr1 (take (size p)) hmerge.
  by rewrite take_size_cat // take_size_cat in h.
have hmerge2 : merge_seq c2 l1'' l2'' = q.
  have h := congr1 (drop (size p)) hmerge.
  by rewrite drop_size_cat // drop_size_cat in h.
have hsize1 : size c1 == size l1' + size l2'.
  rewrite szc1 -hcnt1 -hcnt2; try merge_size => //=.
  rewrite szc1; merge_size; rewrite subnKC => //=.
  by rewrite -szc1; apply count_size.
have hcount1 : count id c1 == size l1' by rewrite hcnt1.
have hsize2 : size c2 == size l1'' + size l2''.
  by rewrite /c2 size_drop /l1'' size_drop /l2'' size_drop // hcnt1 hcnt2; merge_size.
have hcount2 : count id c2 == size l1''.
  have h : count id c1 + count id c2 = n
    by rewrite /c1 /c2 -count_cat cat_take_drop -(eqP (mcode_count s)).
  rewrite /l1'' size_drop hcnt1 sl1; lia.
exists l1', l1'', l2', l2'' => //.
do !split => //.
  by exists (MkMerge hsize1 hcount1).
  by exists (MkMerge hsize2 hcount2).
Qed.

Lemma shuffling_cat_swap {A : Type} {n m n' m'} 
  {a c s1 a' c' s2 : seq A} :
  shuffling n m a c s1 -> shuffling n' m' a' c' s2 ->
  shuffling (n'+n) (m'+m) (a'++a) (c'++c) (s2++s1).
Proof.
move=> [s hs [sl1 sl2]] [s' hs' [sl1' sl2']].
have hsize : size (mcode s' ++ mcode s) == (n'+n) + (m'+m) by merge_size. 
have hcount : count id (mcode s' ++ mcode s) == n'+n by merge_size.
exists (MkMerge hsize hcount).
rewrite /= hs hs' merge_seq_cat; merge_size => //.
do !split => //=; merge_size.
Qed.

Lemma shuffling_perm_eq (A : eqType) {n m} {l1 l2 l3 : seq A} (l3' : seq A) :
  shuffling n m l1 l2 l3 ->
  perm_eq l3 l3' ->
  { l1' : seq A & { l2' : seq A &
    perm_eq l1 l1' * perm_eq l2 l2' *
    shuffling (size l1') (size l2') l1' l2' l3' }}.
Proof.
move=> [s hs [sl1 sl2]] hperm.
apply: (catCA_perm_ind
  (P := fun t => {l1' & {l2' &
    perm_eq l1 l1' * perm_eq l2 l2' *
    shuffling (size l1') (size l2') l1' l2' t}}) _ hperm).
move=> s1 s2 s3 [l1' [l2' [[Hp1 Hp2] Hs]]].
rewrite catA in Hs.
move: (shuffling_app_inv Hs) =>
  [a [a' [c [c' [[[Ha Hc] Hs12] Hs3]]]]].
move: (shuffling_app_inv Hs12) =>
  [a1 [a2 [c1 [c2 [[[Ha12 Hc12] Hs1'] Hs2']]]]].
subst.
exists (a2 ++ a1 ++ a'), (c2 ++ c1 ++ c').
do !split.
  by rewrite (perm_trans Hp1) // catA perm_cat2r perm_catC.
  by rewrite (perm_trans Hp2) // catA perm_cat2r perm_catC.
  rewrite !catA => //=; merge_size.
  apply: shuffling_app_app; last exact Hs3.
  all: try merge_size.
  exact: shuffling_cat_swap Hs1' Hs2'.
by exists l1, l2; do !split => //; rewrite sl1 sl2; by exists s.
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

End seqLevel.

Section tupleLevel.
Definition split1_tuple {A} {n m} (s: Merge n m) (l : (n+m).-tuple A) : n.-tuple A.
Proof.
by refine (Tuple (tval := mask s l)_ ) => //; merge_size.
Defined.

Definition split2_tuple {A} {n m} (s : Merge n m) (l : (n+m).-tuple A ) : m.-tuple A.
Proof.
by refine (Tuple (tval := mask (map negb (mcode s)) l )_ ); merge_size. 
Defined.

Definition split_tuple {A} {n m} (s : Merge n m) (l : (n+m).-tuple A) := 
  (split1_tuple s l, split2_tuple s l). (* TODO split left and right components *)

Definition merge_tuple {A} (n m : nat) (s : Merge n m) (l1 : n.-tuple A) (l2 : m.-tuple A) :
  (n+m).-tuple A.
Proof.
by refine (Tuple (tval := merge_seq (mcode s) l1 l2) _); merge_size.
Defined.

Lemma thm_tuple {A} {n m} (s : Merge n m) (l : (n+m).-tuple A) :
  merge_tuple s (split1_tuple s l) (split2_tuple s l) = l.
Proof.
apply/val_inj => //=.
by rewrite thm => //=; merge_size.
Qed.

Lemma thm2_tuple {A} {n m} (s : Merge n m) (l1 : n.-tuple A) (l2 : m.-tuple A) :
  split1_tuple s (merge_tuple s l1 l2) = l1. 
Proof.
apply/val_inj => //=.
by apply: thm2 => //; merge_size.
Qed.

Lemma thm3_tuple {A} {n m} (s : Merge n m) (l1 : n.-tuple A) (l2 : m.-tuple A) :
  split2_tuple s (merge_tuple s l1 l2) = l2.
apply/val_inj => //=.
by apply/thm3 => //; merge_size.
Qed.

Definition shuffling_tuple {A} {n m } (l1 : n.-tuple A) (l2 : m.-tuple A) (l3 : (n+m).-tuple A ) := 
  { s : Merge n m  | l3 = merge_tuple s l1 l2}.

Lemma merge_tuple_tval {A} {n m} (s : Merge n m) (l1 : n.-tuple A) (l2 : m.-tuple A) :
  tval (merge_tuple s l1 l2) = merge_seq s (tval l1) (tval l2).
Proof. by []. Qed.

Lemma merge_tuple_comm {A} {n m} (s : Merge n m) (l1 : n.-tuple A) (l2 : m.-tuple A) :
  tcast (addnC n m) (merge_tuple s l1 l2) = merge_tuple (shuffle_neg s) l2 l1.
Proof.
apply: val_inj => //=.
by rewrite !val_tcast merge_seq_neg.
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
  rewrite val_tcast => //=.
  split; merge_size.
have Hseq2 : shuffling m p (tval l2) (tval l3) (tval l').
  exists s2.
  rewrite -merge_tuple_tval.
  by rewrite hs2.
  by merge_size.
have [lseq H1 H2] :=
  shuffling_assoc_l (size_tuple l1) (size_tuple l2) Hseq1 Hseq2.
have [s' hs'] := H1.
have [s'' hs''] := H2.
exists (merge_tuple s' l1 l2).
  by exists s'.
exists s''.
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
  by rewrite -merge_tuple_tval hs1.
  split; merge_size. 
have Hseq2 : shuffling (n+m) p (tval l') (tval l3) (tval l).
  exists s2.
  by rewrite -merge_tuple_tval hs2.
  split; merge_size.
have [lseq H1 H2] :=
  shuffling_assoc_r (size_tuple l2) (size_tuple l3) Hseq1 Hseq2.
have [s' hs'] := H1.
have [[s'' e] hs''] := H2.
exists (merge_tuple s' l2 l3).
  by exists s'.
exists (MkMerge e hs'').
apply: val_inj => //=.
by rewrite val_tcast /= -hs' p0.
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

Lemma shuffling_tuple_app_app {A} {n1 nm1 n2 nm2}
    (l1 : n1.-tuple A) (l2 : nm1.-tuple A)
    (l3 : (n1+nm1).-tuple A) (l1' : n2.-tuple A)
    (l2' : nm2.-tuple A) (l3' : (n2 + nm2).-tuple A) :
  shuffling_tuple l1 l2 l3 ->
  shuffling_tuple l1' l2' l3' ->
  shuffling_tuple (l1 ++l1') (l2++l2') 
        (tcast (addnACA n1 nm1 n2 nm2) (cat_tuple l3 l3')).
Proof.
move=> [s hs [s' hs']].
have hsize : size (mcode s ++ mcode s') == (n1+n2) + (nm1+nm2) by merge_size.
have hcount : count id (mcode s ++ mcode s') == n1+n2 by merge_size.
exists (MkMerge hsize hcount).
apply/val_inj => //=.
rewrite val_tcast merge_seq_cat => //; merge_size.
by rewrite hs hs'.
Qed.

Lemma shuffling_tuple_to_seq {A} {n m} (l1 : n.-tuple A) (l2 : m.-tuple A) (l3 : (n+m).-tuple A) :
  shuffling_tuple l1 l2 l3 -> shuffling n m l1 l2 l3.
Proof.
move=> [[s ss sc] hs].
exists (MkMerge ss sc) => //=.
  by rewrite hs /=.
split; merge_size.
Qed.

Lemma shuffling_to_tuple {A} {n m} (l1 l2 l3 : seq A)
    (sl1 : size l1 = n) (sl2 : size l2 = m) (sl3 : size l3 = n + m) :
  shuffling n m l1 l2 l3 ->
  shuffling_tuple (Tuple (introT eqP sl1)) 
                  (Tuple (introT eqP sl2)) 
                  (Tuple (introT eqP sl3)).
Proof.
move=> [s hs [_ _]].
exists s.
by apply/val_inj => //=. 
Qed.

Lemma shuffling_tuple_perm_eq {A : eqType} {n m}
  (l1 : n.-tuple A) (l2 : m.-tuple A) (l3 l3' : (n+m).-tuple A) :
  shuffling_tuple l1 l2 l3 -> perm_eq l3 l3' ->
  { l1' : n.-tuple A & { l2' : m.-tuple A &
    perm_eq l1 l1' * perm_eq l2 l2' *
    shuffling_tuple l1' l2' l3' }}.
Proof.
move=> hsh hperm.
have hsh_seq := shuffling_tuple_to_seq hsh.
have [X [Y [[HpX HpY] Hsh']]] :=
  shuffling_perm_eq hsh_seq hperm.
have szX : size X = n by rewrite -(perm_size HpX) size_tuple.
have szY : size Y = m by rewrite -(perm_size HpY) size_tuple.
have szXY : size X + size Y = n + m by rewrite szX szY.
exists (Tuple (introT eqP szX)).
exists (Tuple (introT eqP szY)).
split; [split|].
- exact HpX.
- exact HpY.
- rewrite szX szY in Hsh'.
  - have h := shuffling_to_tuple szX szY (size_tuple l3') Hsh'.
    have heq : Tuple (introT eqP (size_tuple l3')) = l3'.
    by apply/val_inj => //=.
  by rewrite heq in h.
Qed.

Lemma shuffling_tuple_app_inv {A : eqType} {n m a b : nat}
  (l1  : n.-tuple A) (l2  : m.-tuple A)
  (l3  : (n + m).-tuple A)
  (p   : a.-tuple A) (q   : b.-tuple A)
  (Hab : a + b = n + m)
  (Hpq : tval l3 = tval p ++ tval q) :
  shuffling_tuple l1 l2 l3 ->
  { n1  : nat & { n2  : nat &
  { m1  : nat & { m2  : nat &
  { Hn  : n1 + n2 = n  &
  { Hm  : m1 + m2 = m  &
  { Ha  : a = n1 + m1  &
  { Hb  : b = n2 + m2  &
  { l1' : n1.-tuple A & { l1'' : n2.-tuple A &
  { l2' : m1.-tuple A & { l2'' : m2.-tuple A &
      (tval l1 = tval l1' ++ tval l1'') *
      (tval l2 = tval l2' ++ tval l2'') *
      shuffling_tuple l1' l2' (tcast Ha p) *
      shuffling_tuple l1'' l2'' (tcast Hb q)
  }}}}}}}}}}}}.
Proof.
move=> hsh.
have hsh_seq := shuffling_tuple_to_seq hsh.
have hshpq : shuffling n m l1 l2 (p ++ q).
  by rewrite Hpq in hsh_seq.
have [l1' [l1'' [l2' [l2'' [Hl1 Hshsq]]]]] :=
  shuffling_app_inv hshpq.
have [eq1 [s s1]] := Hl1.
have Hn : size l1' + size l1'' = n by move: eq1.1; rewrite -size_cat => <-; merge_size_clear.
have Hm : size l2' + size l2'' = m by move : eq1.2; rewrite -size_cat => <-; merge_size_clear.
have Ha : a = size l1' + size l2'.
  have hc : count id (mcode s) = size l1' by merge_size_clear.
  have hnc : count negb (mcode s) = size l2' by merge_size_clear.
  have etc := size_merge_seq hc hnc.
  by rewrite -[a](size_tuple p) s1 etc; merge_size_clear.
have Hb : b = size l1'' + size l2'' by lia.
pose L1'  : (size l1').-tuple A := Tuple (eqxx (size l1')).
pose L1'' : (size l1'').-tuple A := Tuple (eqxx (size l1'')).
pose L2'  : (size l2').-tuple A := Tuple (eqxx (size l2')).
pose L2'' : (size l2'').-tuple A := Tuple (eqxx (size l2'')).
exists (size l1') ; exists (size l1'') ; exists (size l2'); exists (size l2'').
exists Hn; exists Hm.
exists Ha; exists Hb.
exists L1'; exists L1''; exists L2'; exists L2''.
repeat split => //=.
have sp : size (tval p) = (size l1') + (size l2') by rewrite size_tuple Ha.
have [Hl1eq Hsl1p] := Hl1.
have H := shuffling_to_tuple (erefl (size l1')) (erefl (size l2')) (sp) Hsl1p.
have eq11 : (Tuple (introT eqP erefl) : (size l1').-tuple A) = L1'.
  apply/val_inj => //=.
have eq22 : (Tuple (introT eqP erefl) : (size l2').-tuple A) = L2' by apply/val_inj => //=.
have eq3 : (Tuple (introT eqP sp) : (size l1' + size l2').-tuple A) = tcast Ha p. 
  apply/val_inj=> //=; by rewrite val_tcast.
rewrite -eq11 -eq22 -eq3.
exact H.
have sq : size (tval q) = (size l1'') + (size l2'') by rewrite size_tuple.
have H := shuffling_to_tuple (erefl (size l1'')) (erefl (size l2'')) (sq) Hshsq.
have eq11 : (Tuple (introT eqP erefl) : (size l1'').-tuple A) = L1'' by apply/val_inj => //=.
have eq2 : (Tuple (introT eqP erefl) : (size l2'').-tuple A) = L2'' by apply/val_inj => //=.
have eq3 : (Tuple (introT eqP sq) : (size l1'' + size l2'').-tuple A) = tcast Hb q. 
  apply/val_inj=> //=; by rewrite val_tcast.
rewrite -eq11 -eq2 -eq3.
exact H.
Qed.

End tupleLevel.
