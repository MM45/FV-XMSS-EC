(* --- Require/Import --- *)
(* -- Built-In (Standard Library) -- *)
require import AllCore List Distr DList IntDiv RealExp StdOrder SmtMap BitEncoding FinType.
require (*--*) Word Subtype.
(*---*) import RField IntOrder RealOrder BS2Int.


(* -- Local -- *)
require import WOTS_TW.
require (*--*) TweakableHashFunctions DigitalSignatures.
(*---*) import DigestBlock DBLL ChainingAddress EmsgWOTS.



(* --- Generic auxiliary properties --- *)
lemma take_rev_int2bs (i j n : int):
  0 <= j <= i =>
  take j (rev (int2bs i n)) = rev (int2bs j (n %/ 2 ^ (i - j))).
proof.
move=> rng_j.
rewrite (int2bs_cat (i - j) i n) 1:/# rev_cat take_cat size_rev size_int2bs.
rewrite (: ! j < max 0 (i - (i - j))) 1:/# /= (: max 0 (i - (i - j)) = j) 1:/# /=.
by rewrite take0 cats0 /#.
qed.

lemma rcons_take_rev_int2bs (i j n : int) (b : bool):
     0 <= j <= i 
  => rcons (take j (rev (int2bs i n))) b 
     = 
     if b
     then rev (int2bs (j + 1) (2 * (n %/ 2 ^ (i - j)) + 1))
     else rev (int2bs (j + 1) (2 * (n %/ 2 ^ (i - j)))).
proof.
move=> rng_j.
rewrite take_rev_int2bs // -rev_cons {1}(: j = j + 1 - 1) //.
case b => _.
+ rewrite {1}(: n %/ 2 ^ (i - j) = (2 * (n %/ 2 ^ (i - j)) + 1) %/ 2).
  - rewrite divzDl 1:dvdz_mulr //.
    by move: (divz_eq0 1 2 _) => //; move/iffLR => /(_ _) // -> /=; rewrite mulKz.
  rewrite (: true = ! 2 %| (2 * (n %/ 2 ^ (i - j)) + 1)).
  - by rewrite dvdzE mulzC modzMDl.
  by rewrite -int2bs_cons 1:/#.
rewrite {1}(: n %/ 2 ^ (i - j) = 2 * (n %/ 2 ^ (i - j)) %/ 2) 1:mulKz //.
rewrite (: false = ! 2 %| (2 * (n %/ 2 ^ (i - j)))) 1: dvdz_mulr //.
by rewrite -int2bs_cons 1:/#.
qed.



(* --- Types --- *)
(* -- General -- *)
(* - Binary trees - *)
type 'a bintree = [  
    Leaf of 'a
  | Node of 'a bintree & 'a bintree 
].


(* -- Fixed-Length XMSS-TW (in encompassing structure) specific -- *)
(* Integers between 0 (including) and l (including), used for the signing index *)
clone import Subtype as Index with
  type T <= int,
  pred P <= fun (i : int), 0 <= i < l.

type index = Index.sT.

(* Lists of length h of which the entries are digest of length 1 (block of 8 * n bits) *)
clone import Subtype as DBHL with
  type T <= dgstblock list,
  pred P <= fun (ls : dgstblock list) => size ls = h.
   
(* Authentication paths in Fixed-Length XMSS-TW binary hash tree *)
type apFLXMSSTW = DBHL.sT.

(* Public keys *)
type pkFLXMSSTW = dgstblock * pseed * adrs.

(* Secret keys *)
type skFLXMSSTW = index * sseed * pseed * adrs.

(* Messages *)
type msgFLXMSSTW = msgWOTS.   

(* Signatures *)
type sigFLXMSSTW = index * sigWOTS * apFLXMSSTW.



(* --- Distributions --- *)
(* Proper, full, and uniform distribution over messages considered for FL-XMSS-TW *)
op [lossless full uniform] dmsgFLXMSSTW : msgFLXMSSTW distr.



(* --- Operators --- *)
(* -- Tweakable hash functions -- *)
(* 
  Tweakable hash function used for the compression of public (WOTS-TW) keys to leaves
  of the binary hash tree of XMSS 
*)
op pkco : pseed -> adrs -> dgst -> dgstblock = thfc (8 * n * len).
  
(* Import and instantiate tweakable hash function definitions for pkco *)
clone TweakableHashFunctions as PKCO with
  type pp_t <- pseed,
  type tw_t <- adrs,
  type in_t <- dgst,
  type out_t <- dgstblock,

  op f <- pkco,
  
  op dpp <- dpseed
  
  proof *. 
  realize dpp_ll by exact: dpseed_ll.

clone PKCO.Collection as PKCOC with
  type diff <- int,
  
    op get_diff <- size,
    
    op fc <- thfc
  
  proof *.
  realize in_collection by exists (8 * n * len).

clone PKCOC.SMDTTCRC as PKCOC_TCR with
  op t_smdttcr <- l
  
  proof *.
  realize ge0_tsmdttcr by smt(ge2_l).  

(* 
  Tweakable hash function used for the hashing operations of the binary hash tree of XMSS.
*)
op trh : pseed -> adrs -> dgst -> dgstblock = thfc (8 * n * 2).

clone TweakableHashFunctions as TRH with
  type pp_t <- pseed,
  type tw_t <- adrs,
  type in_t <- dgst,
  type out_t <- dgstblock,

  op f <- trh,
  
  op dpp <- dpseed
  
  proof *. 
  realize dpp_ll by exact: dpseed_ll.

clone import TRH.Collection as TRHC with
  type diff <- int,
  
    op get_diff <- size,
    
    op fc <- thfc
  
  proof *.
  realize in_collection by exists (8 * n * 2).

clone TRHC.SMDTTCRC as TRHC_TCR with
  op t_smdttcr <- l - 1
  
  proof *.
  realize ge0_tsmdttcr by smt(ge2_l).  


(* -- Binary (hash) tree -- *)
(* Computes height, i.e., the number of levels to the furthest leaf, of a binary tree *)
op height (bt : 'a bintree) =
  with bt = Leaf _ => 0
  with bt = Node l r => 1 + max (height l) (height r).

(* Height of a binary tree is always greater than or equal to 0 *)
lemma ge0_height (bt : 'a bintree):
  0 <= height bt.
proof. by elim: bt => /#. qed.

(* Characterize trees of height 0 *)
lemma height_eq0 ['a] (bt : 'a bintree):
  height bt = 0 => exists x, bt = Leaf x.
proof. by case: bt => /= [x|t1 t2]; [exists x | smt(ge0_height)]. qed.

(* Characterize trees of non-zero height *)
lemma height_gt0 ['a] (bt : 'a bintree):
  0 < height bt => exists t1 t2, bt = Node t1 t2.
proof. by case: bt => [x| t1 t2] => // _; exists t1 t2. qed.

(* 
  Determines whether a binary tree is fully balanced, i.e., 
  whether all leaves are on the same level 
*)
op fully_balanced (bt : 'a bintree) =
  with bt = Leaf _ => true
  with bt = Node l r => height l = height r /\ fully_balanced l /\ fully_balanced r.

(* Characterize balanced trees of non-zero height *)
lemma height_balanced_gt0 ['a] (bt : 'a bintree):
  0 < height bt => fully_balanced bt => exists t1 t2,
       (bt = Node t1 t2)
    /\ (height t1 = height bt - 1)
    /\ (height t2 = height bt - 1)
    /\ fully_balanced t1
    /\ fully_balanced t2.
proof.
by case: bt => //= t1 t2 _ -[eqh [b1 b2]]; exists t1 t2 => //#.
qed.

(* 
  Gets the subtree of which the root is a node located at the end of a path
  represented by a boolean list. Starting from the left of the boolean list,
  each entry indicates whether the left or right subtree of the current binary tree
  is to be considered next. Specifically, a 0 entry indicates that the left-hand side
  subtree is to be considered next, while a 1 entry indicates that the right-hand side
  subtree is to be considered next. When all of the entries have been considered,
  the resulting subtree is returned.
*)
op sub_bt (bt : 'a bintree) (bs : bool list) : 'a bintree option =
  with bt = Leaf _  , bs = []      => Some bt
  with bt = Leaf _  , bs = _ :: _  => None
  with bt = Node _ _, bs = []      => Some bt
  with bt = Node l r, bs = b :: bs' => sub_bt (if b then r else l) bs'.

(* The subtree at the end of an empty path is the currently considered binary tree *)
lemma subbt_empty (bt : 'a bintree) :
  sub_bt bt [] = Some bt.
proof. by case bt. qed.

(* 
  Extracts the (hash) value from a leaf; returns None if the given binary tree is not a leaf 
*)
op val_lf (bt : 'a bintree) : 'a option =
  with bt = Leaf x => Some x
  with bt = Node _ _ => None.

(* 
  Extracts the (hash) value from a leaf located at the end of a path 
  represented by a boolean list 
*)
op extr_vallf (bt : 'a bintree) (bs : bool list) : 'a option =
  obind val_lf (sub_bt bt bs).

lemma extr_vallf_Leaf ['a] (x : 'a) :
  extr_vallf (Leaf x) [] = Some x.
proof. by []. qed.

lemma extr_vallf_Node ['a] (t1 t2 : 'a bintree) b bs:
  extr_vallf (Node t1 t2) (b :: bs) =
    if b then extr_vallf t2 bs else extr_vallf t1 bs.
proof. by case: b. qed.

(* Conversion operator between lists and binary trees *)
op list2tree_pred ['a] (s : 'a list) (t : 'a bintree) =
   let e = height t in
      size s = 2 ^ e
   /\ fully_balanced t
   /\ (forall idx, 0 <= idx < size s => extr_vallf t (rev (int2bs e idx)) = onth s idx).

lemma list2tree_spec ['a] (s : 'a list) (e : int) :
  0 <= e => size s = 2 ^ e => exists t, list2tree_pred s t.
proof.
move=> ge0_e; elim: e ge0_e s => /= [|e ge0_e ih] s.
- rewrite expr0 => /size_eq1[x ->>] /=; exists (Leaf x).
  do! split => //=; first by rewrite expr0.
  move=> idx; rewrite ltz1 -eqr_le => <<- /=.
  by rewrite int2bs0 nseq0 rev_nil /= extr_vallf_Leaf.
move=> sz_s; have /eq_sym := cat_take_drop (2 ^ e) s.
(pose s1 := take _ _; pose s2 := drop _ _) => sE.
have gt: 2 ^ e < 2 ^ (e + 1).
- by rewrite exprS // ltr_pmull // expr_gt0.
have sz_s1: size s1 = 2 ^ e.
- by rewrite /s1 size_take 1:expr_ge0 // sz_s gt.
have sz_s2: size s2 = 2 ^ e.
- rewrite /s2 size_drop 1:expr_ge0 // sz_s.
  rewrite exprS // (_ : 2 * 2^e - 2^e = 2 ^ e) 1:/#.
  by rewrite lez_maxr 1:expr_ge0.
case: (ih s1 sz_s1); last case: (ih s2 sz_s2).
move=> @/list2tree_pred /= t2 [# h2 b2 n2] t1 [# h1 b1 n1].
- move: h1 h2; rewrite !(sz_s1, sz_s2) => h1 h2.
  have inj := IntOrder.ieexprIn 2 _ _ => //.
  have et1 := inj e (height t1) ge0_e _ h1; 1: exact/ge0_height.
  have et2 := inj e (height t2) ge0_e _ h2; 1: exact/ge0_height.
move=> {inj}; exists (Node t1 t2); do! split => //=; 1,2:smt().
move=> idx; rewrite sz_s exprS // => -[ge0_idx lt_idx].
rewrite -et1 -et2 ler_maxr // [1+_]addrC int2bsS // rev_rcons.
pose c := (idx %/ (2 ^ e)).
move: lt_idx; rewrite -ltz_divLR 1:expr_gt0 // -/c => ltc.
have ge0_c: 0 <= c by rewrite divz_ge0 // expr_gt0.
have {ltc ge0_c} cE: (c = 0) \/ (c = 1) by smt().
rewrite extr_vallf_Node onth_nth_map sE map_cat.
rewrite nth_cat size_map; case: cE => ^ + -> /= - @/c => {c}.
- rewrite -divz_eq0 1:expr_gt0 // => -[_ lt_idx].
  by rewrite et1 n1 sz_s1 lt_idx //= -onth_nth_map.
move=> idxE; rewrite {-1}[idx](divz_eq _ (2 ^ e)) idxE /=.
rewrite sz_s1 ltrNge ler_addl modn_ge0 //= addrAC /=.
rewrite -int2bs_mod et2 n2 -1:onth_nth_map //.
by rewrite modn_ge0 //= sz_s2 -et2 ltz_pmod // expr_gt0.
qed.

op list2tree ['a] (s : 'a list) : 'a bintree =
  if   (exists e, 0 <= e /\ size s = 2 ^ e)
  then choiceb (list2tree_pred s) witness
  else witness.

lemma list2tree_spec_ok ['a] (s : 'a list) (e : int) :
     0 <= e
  => size s = 2 ^ e 
  => list2tree_pred s (list2tree s).
proof.
move=> ge0_e szs; rewrite /list2tree.
pose b := exists e, 0 <= e /\ size s = 2 ^ e.
have ^bT -> /=: b by exists e.
apply: (choicebP (list2tree_pred s) witness _).
by apply: (list2tree_spec s e).
qed.

lemma list2tree_ok ['a] (s : 'a list) (e : int) :
     0 <= e
  => size s = 2 ^ e 
  =>    height (list2tree s) = e
     /\ fully_balanced (list2tree s)
     /\ (forall idx, 0 <= idx < size s => extr_vallf (list2tree s) (rev (int2bs e idx)) = onth s idx).
proof.
move=> ge0_e szs; have := list2tree_spec_ok _ _ ge0_e szs.
move: (list2tree _) => t @/list2tree_pred /= [# h1 h2 h3].
have htE: height t = e.
- have inj := IntOrder.ieexprIn 2 _ _ => //.
  by move: h1; rewrite szs eq_sym &(inj) // &(ge0_height).
by do! split=> //; rewrite -htE.
qed.

(*
  Constructing a tree from a list (of which the size is a power of 2) through list2tree 
  results in a tree of which the leaf at breadth position i has (hash) value x, 
  where x is the (hash) value in the list at index i.
*)
lemma list2tree_lvb (s : 'a list) (idx : int) (e : int) :
     0 <= e
  => size s = 2 ^ e 
  => 0 <= idx < size s
  => extr_vallf (list2tree s) (rev (int2bs e idx)) = onth s idx.
proof. smt(list2tree_ok). qed.

(* 
  Constructing a tree from a list (of which the size is a power of 2, say 2 ^ e)
  through list2tree results in a tree with height e.
*)
lemma list2tree_height (s : 'a list) (e : int) :
     0 <= e
  => size s = 2 ^ e
  => height (list2tree s) = e.
proof. smt(list2tree_ok). qed.

(*
  Constructing a tree from a list (of which the size is a power of 2) through list2tree 
  results in a fully balanced tree
*)
lemma list2tree_fullybalanced (s : 'a list) (e : int) :
     0 <= e
  => size s = 2 ^ e
  => fully_balanced (list2tree s).
proof. smt(list2tree_ok). qed.

(* 
  Constructing a tree from a list that holds a single entry gives 
  a Leaf that holds the value of that entry
*)
lemma list2tree1 (x : 'a) :
  list2tree [x] = Leaf x.
proof.
move: (list2tree_lvb [x] 0 0 _) => //.
by rewrite expr0 /= int2bs0s /#.
qed.

lemma list2tree_uniq2 ['a] (e : int) (s : 'a list) (t1 t2 : 'a bintree) :
     0 <= e
  => size s = 2 ^ e
  => list2tree_pred s t1
  => list2tree_pred s t2
  => t1 = t2.
proof.
move=> ge0_e szs @/list2tree_pred /= [# h1 f1 n1] [# h2 f2 n2].
have inj := IntOrder.ieexprIn 2 _ _ => //.
have hg1E: height t1 = e.
- by apply/eq_sym/inj => //; [apply: ge0_height | rewrite -szs].
have hg2E: height t2 = e.
- by apply/eq_sym/inj => //; [apply: ge0_height | rewrite -szs].
move=> {h1 h2}; elim: e ge0_e s szs t1 f1 n1 hg1E t2 f2 n2 hg2E.
- move=> s; rewrite expr0 => /size_eq1[x] ->> t1 _ n1 h1 t2 _ n2 h2.
  case/height_eq0: h1=> x1 ->>; case/height_eq0: h2=> x2 ->>.
  (have := n1 0 _) => //=; (have := n2 0 _) => //=.
  by rewrite int2bs0 nseq0 rev_nil !extr_vallf_Leaf.
move=> e ge0_e ih s szs t1 b1 n1 h1 t2 b2 n2 h2.
have := height_balanced_gt0 t1 _ b1; first by smt().
case=> [tl1 tr1] [# ->> hl1 hr1 bl1 br1].
have := height_balanced_gt0 t2 _ b2; first by smt().
case=> [tl2 tr2] [# ->> hl2 hr2 bl2 br2].
pose s1 := take (2 ^ e) s; pose s2 := drop (2 ^ e) s.
have sz_s1: size s1 = 2 ^ e.
- rewrite /s1 size_take 1:expr_ge0 // szs.
  by rewrite exprS // ltr_pmull // expr_gt0.
have sz_s2: size s2 = 2 ^ e.
- rewrite /s1 size_drop 1:expr_ge0 // szs exprS //.
  rewrite (_ : 2 * 2 ^ e - 2 ^ e = 2 ^ e) 1:/#.
  by rewrite lez_maxr // expr_ge0.
rewrite h1 /= in hl1; rewrite h1 /= in hr1.
rewrite h2 /= in hl2; rewrite h2 /= in hr2.
congr; [apply (ih s1) | apply (ih s2)] => {ih} //.
- move=> idx [ge0_idx lt_idx]; have := n1 idx _.
  - by rewrite szs exprS // -sz_s1; smt(size_ge0).
  rewrite h1 int2bsS // rev_rcons extr_vallf_Node.
  rewrite pdiv_small 1:-sz_s1 //= hl1.
  rewrite -[s](cat_take_drop (2 ^ e)) -/s1 -/s2.
  by rewrite !onth_nth_map map_cat nth_cat size_map lt_idx.
- move=> idx [ge0_idx lt_idx]; have := n2 idx _.
  - by rewrite szs exprS // -sz_s1; smt(size_ge0).
  rewrite h2 int2bsS // rev_rcons extr_vallf_Node.
  rewrite pdiv_small 1:-sz_s1 //= hl2.
  rewrite -[s](cat_take_drop (2 ^ e)) -/s1 -/s2.
  by rewrite !onth_nth_map map_cat nth_cat size_map lt_idx.
- move=> idx [ge0_idx lt_idx]; have := n1 (size s1 + idx) _.
  - by rewrite szs exprS // -sz_s1; smt(size_ge0).
  rewrite h1 int2bsS // rev_rcons extr_vallf_Node.
  rewrite sz_s1 (divzMDl 1 _ (2 ^ e)).
  - by rewrite gtr_eqF // expr_gt0.
  rewrite pdiv_small 1:-sz_s2 //= hr1.
  rewrite -{1}int2bs_mod modzDl pmod_small 1:-sz_s2 //.
  rewrite -[s](cat_take_drop (2 ^ e)) -/s1 -/s2.
  rewrite !onth_nth_map map_cat nth_cat size_map.
  by rewrite ltrNge sz_s1 ler_addl ge0_idx /= addrAC.
- move=> idx [ge0_idx lt_idx]; have := n2 (size s1 + idx) _.
  - by rewrite szs exprS // -sz_s2; smt(size_ge0).
  rewrite h2 int2bsS // rev_rcons extr_vallf_Node.
  rewrite sz_s1 (divzMDl 1 _ (2 ^ e)).
  - by rewrite gtr_eqF // expr_gt0.
  rewrite pdiv_small 1:-sz_s2 //= hr2.
  rewrite -{1}int2bs_mod modzDl pmod_small 1:-sz_s2 //.
  rewrite -[s](cat_take_drop (2 ^ e)) -/s1 -/s2.
  rewrite !onth_nth_map map_cat nth_cat size_map.
  by rewrite ltrNge sz_s1 ler_addl ge0_idx /= addrAC.
qed.

lemma list2tree_uniq ['a] (e : int) (s : 'a list) (t : 'a bintree) :
     0 <= e
  => size s = 2 ^ e
  => list2tree_pred s t
  => list2tree s = t.
proof.
move=> ge0_e szs h; apply: (list2tree_uniq2 e s) => //.
by apply: (list2tree_spec_ok _ e).
qed.

lemma list2tree_pred0 ['a] (x : 'a) :
  list2tree_pred [x] (Leaf x).
proof.
do! split => //=; first by rewrite expr0.
move=> idx; rewrite ltz1 -eqr_le => <<-.
by rewrite int2bs0 nseq0 rev_nil /= extr_vallf_Leaf.
qed.

lemma list2tree0 ['a] (x : 'a) : list2tree [x] = Leaf x.
proof.
apply: (list2tree_uniq 0) => //=.
- by rewrite expr0. 
- by apply: list2tree_pred0.
qed.

lemma list2tree_predS ['a] (s1 s2 : 'a list) (t1 t2 : 'a bintree) :
     list2tree_pred s1 t1
  => list2tree_pred s2 t2
  => height t1 = height t2
  => list2tree_pred (s1 ++ s2) (Node t1 t2).
proof.
move=> + + eq_h - @/list2tree_pred /=; rewrite -eq_h.
move: (height t1) (ge0_height t1) => e ge0_e {eq_h}.
move=> [# h1 b1 n1] [# h2 b2 n2].
rewrite lez_maxr //; do! split => //.
- by rewrite size_cat [1 + _]addrC exprS //#.
move=> idx; rewrite size_cat => -[ge0_idx lt_idx].
rewrite [1+_]addrC int2bsS // rev_rcons.
have := divz_eq idx (2 ^ e); pose c := _ %/ _.
have lt2_c: c < 2 by rewrite /c ltz_divLR 1:expr_gt0 //#.
have ge0_c: 0 <= c by rewrite divz_ge0 // expr_gt0.
have {ge0_c lt2_c} eq_c: (c = 0) \/ (c = 1) by smt().
move=> -> {lt_idx}; rewrite extr_vallf_Node.
rewrite onth_nth_map map_cat nth_cat -!onth_nth_map size_map.
case: eq_c => -> /=; rewrite !(h1, h2).
- rewrite ltz_pmod 1:expr_gt0 //= &(n1) h1.
  by rewrite modn_ge0 //= ltz_pmod // expr_gt0.
- rewrite -int2bs_mod modzDl modz_mod ltzNge lez_addl.
  rewrite modn_ge0 //= addrAC /= &(n2).
  by rewrite modn_ge0 //= h2 ltz_pmod // expr_gt0.
qed.

lemma list2treeS ['a] (e : int) (s1 s2 : 'a list) :
     0 <= e
  => size s1 = 2 ^ e
  => size s2 = 2 ^ e
  => list2tree (s1 ++ s2) = Node (list2tree s1) (list2tree s2).
proof.
move=> ge0_e sz1 sz2; apply: (list2tree_uniq (e + 1)).
- smt(). 
- by rewrite size_cat exprS //#.
apply: list2tree_predS => //; 1,2: by apply: (list2tree_spec_ok _ e).
by rewrite !(list2tree_height _ e).
qed.

(* 
  Computes the (hash) value corresponding to the root of the binary tree w.r.t.
  a certain public seed, address, height index, and breadth index. 
*)
op val_bt_trh (bt : dgstblock bintree) (ps : pseed) (ad : adrs) (hidx : int) (bidx : int) : dgstblock =
  with bt = Leaf x => x
  with bt = Node l r => 
    trh ps (set_thtbidx ad hidx bidx) 
      (val (val_bt_trh l ps ad (hidx - 1) (2 * bidx)) ++ val (val_bt_trh r ps ad (hidx - 1) (2 * bidx + 1))).

lemma subbt_list2tree_cons (ls : dgstblock list) (b : bool) (bs : bool list) (e : int) :
     0 <= e
  => size ls = 2 ^ e
  => size bs < e
  => sub_bt (list2tree ls) (b :: bs)
     =
     if b
     then
       sub_bt (list2tree (drop (size ls %/ 2) ls)) bs
     else
       sub_bt (list2tree (take (size ls %/ 2) ls)) bs.
proof.
move=> ge0_e; elim: e ge0_e b bs => [|e ge0_e ih] b bs.
- by rewrite ltzNge size_ge0.
move=> ^szls -> szbs; rewrite exprS // mulKz //.
rewrite -{1}(cat_take_drop (2 ^ e)).
pose s2 := drop _ _; pose s1 := take _ _.
have sz_s1: size s1 = 2 ^ e.
- rewrite /s1 size_take 1:expr_ge0 // szls.
  by rewrite exprS // ltr_pmull // expr_gt0.
have sz_s2: size s2 = 2 ^ e.
- rewrite /s1 size_drop 1:expr_ge0 // szls exprS //.
  rewrite (_ : 2 * 2 ^ e - 2 ^ e = 2 ^ e) 1:/#.
  by rewrite lez_maxr // expr_ge0.
by rewrite (list2treeS e) //= fun_if2.
qed.

(* 
  For an index in a list that has a power of 2 size, the subtree (of the tree
  obtained by applying list2tree to the list) at the end of the 
  path represented by the big-endian binary representation of this index gives a leaf
  with the value of the entry at this index in the list.
*)
lemma subbt_list2tree_idx (ls : dgstblock list) (idx e : int) :
     0 <= e
  => size ls = 2 ^ e
  => 0 <= idx < size ls
  => sub_bt (list2tree ls) (rev (int2bs e idx))
     =
     Some (Leaf (nth witness ls idx)).
proof.
move=> ge0_e.
elim: e ge0_e ls idx => [/= ls idx | e ge0_e ih ls idx].
+ rewrite expr0 size_eq1 => -[x -> /=] rng_idx.
  rewrite list2tree1 int2bs0s /rev /#.
rewrite exprD_nneg // expr1 => szls rng_idx.
rewrite int2bsS // rev_rcons.
rewrite (subbt_list2tree_cons ls (idx %/ 2 ^ e %% 2 <> 0) (rev (int2bs e idx)) (e + 1)) 1:/#.
+ by rewrite exprD_nneg 3:expr1.
+ by rewrite size_rev size_int2bs /#.
case (idx %/ 2 ^ e %% 2 = 0) => cs /=.
+ have ltszls2_idx : idx < size ls %/ 2.
  - rewrite szls mulzK //.
    move: rng_idx => []; rewrite -(divz_ge0 idx (2 ^ e)) 1:expr_gt0 //.
    rewrite szls mulzC -ltz_divLR 1:expr_gt0 // => ge0_idx2e lt2_idx2e.
    have: idx %/ 2 ^ e \in range 0 1 by rewrite mem_range /#.
    by rewrite range_div_range 1:expr_gt0 2:mem_range.
  rewrite (ih (take (size ls %/ 2) ls) idx) 1,2:size_take 1,3:divz_ge0 // 1,2:/#.
  by rewrite nth_take 1,2:/#.
rewrite (: int2bs e idx = int2bs e (idx - 2 ^ e)).
+ rewrite /int2bs /mkseq &(eq_in_map) => i /mem_iota [ge0_i /= lte_i].
  rewrite divzDr 1:dvdzN 1:dvdz_exp2l 1:/#.
  rewrite dvdz_modzDr 1:dvdNdiv 2:dvdz_exp2l 2:/# //.
  - by suff /#: 0 < 2 ^ i; rewrite expr_gt0.
  by rewrite dvdzN expz_div 1:/# 1:// -{1}expr1 dvdz_exp2l 1:/#.  
rewrite (ih (drop (size ls %/ 2) ls) (idx - 2 ^ e)) 1,2:size_drop 1..4:/#.
by rewrite nth_drop /#.
qed.

(* 
  For a fully balanced binary (hash) tree and a valid tree hashing address, height index,
  and breadth index, the value of the subtree at the end of a path represented 
  by the first bits of the big-endian binary representation of the breadth index is 
  the trh hash of the (concatenation of) the hash values of the left and right 
  binary subtree of that subtree.
*)
lemma valbttrh_subbt (bt : dgstblock bintree) (ps : pseed) (ad : adrs) (hidx bidx : int) :
     is_trhtype ad
  => fully_balanced bt
  => 1 <= hidx <= height bt
  => val_bt_trh (oget (sub_bt bt (rev (int2bs (height bt - hidx) bidx)))) ps ad hidx bidx
     =
     trh ps (set_thtbidx ad hidx bidx)
       (val (val_bt_trh (oget (sub_bt bt (rev (int2bs (height bt - hidx + 1) (2 * bidx))))) ps ad (hidx - 1) (2 * bidx))
        ++
        val (val_bt_trh (oget (sub_bt bt (rev (int2bs (height bt - hidx + 1) (2 * bidx + 1))))) ps ad (hidx - 1) (2 * bidx + 1))).
proof.
move=> adtrh.
elim: bt hidx bidx  => [/= /# | l r /= ihl ihr hidx bidx [#] eqhl_hr fb_l fb_r rng_hidx].
case (hidx = 1 + max (height l) (height r)) => [-> /= | neq_hidx].
+ rewrite int2bs0s {1}/rev /= (: 1 = 0 + 1) 1:// ?int2bsS 1,2://.
  rewrite 2?int2bs0s /rev /= expr0 2!divz1 modzMr /=. 
  rewrite (: sub_bt l [] = Some l) 2:oget_some.
  - by case: l rng_hidx fb_l eqhl_hr ihl.
  rewrite mulzC modzMDl /= (: sub_bt r [] = Some r) 2:oget_some //.
  by case: r rng_hidx fb_r eqhl_hr ihr.
rewrite {1}addzC {1}[1 + _]addzC addzA 3?int2bsS 1,2,3:/# 3!rev_rcons {1 2}addzC.
case (bidx %/ 2 ^ (max (height l) (height r) - hidx) %% 2 = 0) => [eq0_div | neq0_div] /=.
+ rewrite -addzA exprD_nneg 1:// 1:/# expr1.
  rewrite divzMpl // eq0_div /= divzMr // 1:expr_ge0 // divzDl // 1:dvdz_mulr //.
  move: (divz_eq0 1 2 _) => //; move/iffLR => -> //=.
  by rewrite mulKz // eq0_div //= /#.
rewrite -addzA exprD_nneg 1:// 1:/# expr1.
rewrite divzMpl // neq0_div /= divzMr // 1:expr_ge0 // divzDl // 1:dvdz_mulr //.
move: (divz_eq0 1 2 _) => //; move/iffLR => -> //=.
by rewrite mulKz // neq0_div //= /#.
qed.

(* 
  Constructs an authentication path (without embedding it in the corresponding subtype)
  from a binary (hash) tree and a path represented by a boolean list w.r.t. a certain 
  public seed, address, height index, and breadth index
*)
op cons_ap_trh_gen (bt : dgstblock bintree) (bs : bool list) (ps : pseed) (ad : adrs) (hidx : int) (bidx : int) : dgstblock list =
  with bt = Leaf _, bs = [] => []
  with bt = Leaf _, bs = _ :: _ => witness
  with bt = Node _ _, bs = [] => witness
  with bt = Node l r, bs = b :: bs' =>
    (val_bt_trh (if b then l else r) ps ad (hidx - 1) (if b then 2 * bidx else 2 * bidx + 1)) 
    :: cons_ap_trh_gen (if b then r else l) bs' ps ad (hidx - 1) (if b then 2 * bidx + 1 else 2 * bidx). 

(*
  Computes the (hash) value corresponding to an authentication path, a leaf, and a 
  path represented by a boolean list w.r.t a certain public seed, address, height index, 
  and breadth index
*)  
op val_ap_trh_gen (ap : dgstblock list) (bs : bool list) (leaf : dgstblock) (ps : pseed) (ad : adrs) (hidx : int) (bidx : int) : dgstblock =
  with ap = [], bs = [] => leaf
  with ap = [], bs = _ :: _ => witness 
  with ap = _ :: _, bs = [] => witness
  with ap = x :: ap', bs = b :: bs' =>
      trh ps (set_thtbidx ad hidx bidx) 
       (if b 
        then val x ++ val (val_ap_trh_gen ap' bs' leaf ps ad (hidx - 1) (2 * bidx + 1))
        else val (val_ap_trh_gen ap' bs' leaf ps ad (hidx - 1) (2 * bidx)) ++ val x).

(*
  Extracts a collision, height index, and breadth index from a binary tree and 
  an authentication path w.r.t. a certain public seed, address, (initial) height index, and 
  (initial) breadth index
*)        
op extract_coll_bt_ap (bt : dgstblock bintree) (ap : dgstblock list) (bs : bool list) (leaf : dgstblock) (ps : pseed) (ad : adrs) (hidx : int) (bidx : int) : (dgst * dgst * int * int) option =
  with bt = Leaf _, ap = [], bs = [] => None
  with bt = Leaf _, ap = [], bs = b :: bs' => None
  with bt = Leaf _, ap = x :: ap', bs = [] => None
  with bt = Leaf _, ap = x :: ap', bs = b :: bs' => None
  with bt = Node _ _, ap = [], bs = [] => None
  with bt = Node _ _, ap = [], bs = b :: bs' => None
  with bt = Node _ _, ap = x :: ap', bs = [] => None
  with bt = Node l r, ap = x :: ap', bs = b :: bs' =>
    if b
    then
      if (val_bt_trh l ps ad (hidx - 1) (2 * bidx), val_bt_trh r ps ad (hidx - 1) (2 * bidx + 1)) <> (x, val_ap_trh_gen ap' bs' leaf ps ad (hidx - 1) (2 * bidx + 1))
         /\ val_bt_trh bt ps ad hidx bidx = val_ap_trh_gen ap bs leaf ps ad hidx bidx
      then Some (val (val_bt_trh l ps ad (hidx - 1) (2 * bidx)) ++ val (val_bt_trh r ps ad (hidx - 1) (2 * bidx + 1)), val x ++ val (val_ap_trh_gen ap' bs' leaf ps ad (hidx - 1) (2 * bidx + 1)), hidx, bidx)
      else extract_coll_bt_ap r ap' bs' leaf ps ad (hidx - 1) (2 * bidx + 1)
    else
      if (val_bt_trh l ps ad (hidx - 1) (2 * bidx), val_bt_trh r ps ad (hidx - 1) (2 * bidx + 1)) <> (val_ap_trh_gen ap' bs' leaf ps ad (hidx - 1) (2 * bidx), x)
         /\ val_bt_trh bt ps ad hidx bidx = val_ap_trh_gen ap bs leaf ps ad hidx bidx
      then Some (val (val_bt_trh l ps ad (hidx - 1) (2 * bidx)) ++ val (val_bt_trh r ps ad (hidx - 1) (2 * bidx + 1)), val (val_ap_trh_gen ap' bs' leaf ps ad (hidx - 1) (2 * bidx)) ++ val x, hidx, bidx)
      else extract_coll_bt_ap l ap' bs' leaf ps ad (hidx - 1) (2 * bidx).
     
(* 
  Specifies the conditions under which extract_coll_bt_ap actually extracts
  a collision and corresponding indices, and what some of the values are/in which range 
  some of the values lie
*)
lemma extract_coll_bt_ap_P (bt : dgstblock bintree) (ap : dgstblock list) (bs : bool list) (leaf leaf' : dgstblock) (ps : pseed) (ad : adrs) (bidx : int) :
     is_trhtype ad
  => leaf <> leaf'
  => fully_balanced bt
  => size ap = size bs
  => height bt = size ap
  => valid_thidx (height bt)
  => valid_tbidx (height bt) bidx
  => val_bt_trh bt ps ad (height bt) bidx = val_ap_trh_gen ap bs leaf ps ad (size ap) bidx
  => extr_vallf bt bs = Some leaf'
  => (exists (x x' : dgst) (i j : int),
        extract_coll_bt_ap bt ap bs leaf ps ad (height bt) bidx = Some (x, x', i, j) /\
        size x = 8 * n * 2 /\
        size x' = 8 * n * 2 /\
        x = val (val_bt_trh (oget (sub_bt bt (rcons (take (height bt - i) bs) false))) ps ad (i - 1) (2 * j)) 
            ++ val (val_bt_trh (oget (sub_bt bt (rcons (take (height bt - i) bs) true))) ps ad (i - 1) (2 * j + 1)) /\
        valid_thidx i /\
        valid_thidx (i - 1) /\
        valid_tbidx i j /\
        valid_tbidx (i - 1) (2 * j) /\
        valid_tbidx (i - 1) (2 * j + 1) /\
        1 <= i <= height bt /\
        j = bs2int (rev (take (height bt - i) bs) ++ (int2bs (h - height bt) bidx)) /\
        x <> x' /\ 
        trh ps (set_thtbidx ad i j) x
        =
        trh ps (set_thtbidx ad i j) x').
proof.
move=> adtrh neql_lp.
elim: ap bs bt bidx => [bs bt bidx fb_bt | x ap ih].
+ rewrite eq_sym size_eq0 => ->.
  by case: bt fb_bt. 
case; first by smt(size_ge0).
move=> b bs; case => [/# | l r bidx].
move: b => [] fb_nlr eqszap1_bs1 eqhnlr_szap1 valth_nlr valtb_nlr eq_valbtnlr_valapx eq_extrnlr_lfp /=.
+ pose val_l := val_bt_trh l _ _ _ _.
  pose val_r := val_bt_trh r _ _ _ _.
  pose val_ap := val_ap_trh_gen _ _ _ _ _ _ _.
  case (val_l = x /\ val_r = val_ap) => [cs | /negb_and cs /=].
  - rewrite (: height l = height r) 1:/# lez_maxl //=.
    move: (ih bs r (2 * bidx + 1)) => /= /(_ _ _ _ _ _ _ _); 1..4,6,7: by smt(ge0_height).
    * by move: valtb_nlr; rewrite /valid_tbidx /nr_nodes; smt(@IntOrder).
    move=> [xx xx' i j] [#] ? ? ? ? ? ? ? ? ? ? ? jval *.
    exists xx xx' i j; do ? (split => //); first 2 by smt().
    pose ifs := if _ then _ else _; rewrite (: ifs = take (1 + height r - i) (true :: bs)) 1:/#.
    rewrite jval 2?rev_take 1,2:/# rev_cons -cats1 drop_cat.
    have: size (true :: bs) - (1 + height r - i) <= size (rev bs) by smt(size_rev).
    case; first rewrite /rev => -> /=.
    * congr; rewrite -catA; congr => [/# |].
      by rewrite int2bs_cons 1:/# /=; smt(@IntDiv).
    rewrite ltz_def => eqszhr @/rev /=; rewrite eqszhr /=.
    rewrite (: size bs - (height r - i) = size (catrev bs [])) 1:/#.
    by rewrite drop_size /= int2bs_cons 1:/# /=; smt(@IntDiv).
  move: (eq_valbtnlr_valapx) => /= eq_trh @{1}/val_l @{1}/val_r @{1}/val_ap.
  rewrite eq_trh (: max (height l) (height r) = size ap) 1:/# /=.
  exists (val (val_l) ++ val (val_r)) (val x ++ val (val_ap)) (1 + max (height l) (height r)) bidx => /=.
  split => [/# |].
  rewrite 2!size_cat (: 8 * n * 2 = 8 * n + 8 * n) 1:/# /val_l /val_r /val_ap.
  split; first rewrite {1}lez_maxl 1:/# lez_maxr 1:/#; congr; first 2 by rewrite valP.
  split; first by rewrite (: max (height l) (height r) = size ap) 1:/# /= 2!valP.
  rewrite (: 1 + size ap - (1 + max (height l) (height r)) = 0) 1:/# /=.
  split; first by rewrite /= 2!subbt_empty 2!oget_some.
  rewrite 4!andbA; split; first by move: valtb_nlr; rewrite /valid_tbidx /nr_nodes; smt(ge0_height @IntOrder).
  split; first by smt(ge0_height).
  rewrite /rev /= int2bsK 1,2:/# /=.
  split => [| /#].
  by rewrite {1}lez_maxl 1:/# lez_maxr 1:/# eqseq_cat 1:2!valP //; smt(DigestBlock.val_inj).
pose val_l := val_bt_trh l _ _ _ _.
pose val_r := val_bt_trh r _ _ _ _.
pose val_ap := val_ap_trh_gen _ _ _ _ _ _ _.
case (val_l = val_ap /\ val_r = x) => [cs | /negb_and cs /=].
- rewrite lez_maxl 1:/# //=.
  move: (ih bs l (2 * bidx)) => /= /(_ _ _ _ _ _ _ _); 1..4,6,7: by smt(ge0_height).
  * by move: valtb_nlr; rewrite /valid_tbidx /nr_nodes; smt(@IntOrder).
  move=> [xx xx' i j] [#] ? ? ? ? ? ? ? ? ? ? ? jval *.
  exists xx xx' i j; do ? (split => //); first 2 by smt().
  pose ifs := if _ then _ else _; rewrite (: ifs = take (1 + height l - i) (false :: bs)) 1:/#.
  rewrite jval 2?rev_take 1,2:/# rev_cons -cats1 drop_cat.
  have: size (false :: bs) - (1 + height l - i) <= size (rev bs) by smt(size_rev).
  case; first rewrite /rev => -> /=.
  * congr; rewrite -catA; congr => [/# |].
    by rewrite int2bs_cons 1:/# /=; smt(@IntDiv).
  rewrite ltz_def => eqszhr @/rev /=; rewrite eqszhr /=.
  rewrite (: size bs - (height l - i) = size (catrev bs [])) 1:/#.
  by rewrite drop_size /= int2bs_cons 1:/# /=; smt(@IntDiv).
move: (eq_valbtnlr_valapx) => /= eq_trh @{1}/val_l @{1}/val_r @{1}/val_ap.
rewrite eq_trh (: max (height l) (height r) = size ap) 1:/# /=.
exists (val val_l ++ val val_r) (val val_ap ++ val x) (1 + max (height l) (height r)) bidx => /=.
split => [/# |].
rewrite 2!size_cat (: 8 * n * 2 = 8 * n + 8 * n) 1:/# /val_l /val_r /val_ap.
split; first rewrite {1}lez_maxl 1:/# lez_maxr 1:/#; congr; first 2 by rewrite valP.
split; first by rewrite (: max (height l) (height r) = size ap) 1:/# 2!valP.
rewrite (: 1 + size ap - (1 + max (height l) (height r)) = 0) 1:/# /=.
split; first by rewrite /= 2!subbt_empty 2!oget_some.
rewrite 4!andbA; split; first by move: valtb_nlr; rewrite /valid_tbidx /nr_nodes; smt(ge0_height @IntOrder).
split; first by smt(ge0_height).
rewrite /rev /= int2bsK 1,2:/# /=.
split => [| /#].
by rewrite {1}lez_maxl 1:/# {1}lez_maxr 1:/# (: max (height l) (height r) = size ap) 1:/# eqseq_cat 1:2!valP //; smt(DigestBlock.val_inj).
qed.

(* 
  Special case of the collision extraction lemma for binary trees and authentication path
  of height/length h and paths represented by the big-endian binary representation of
  indices between 0 (including) and 2 ^ h (including).  
*)
lemma extract_coll_bt_ap_Ph0 (bt : dgstblock bintree) (ap : apFLXMSSTW) (idx : index) (leaf leaf' : dgstblock) (ps : pseed) (ad : adrs) :
     is_trhtype ad
  => leaf <> leaf'
  => fully_balanced bt
  => height bt = h
  => val_bt_trh bt ps ad h 0 = val_ap_trh_gen (val ap) (rev (int2bs h (val idx))) leaf ps ad h 0
  => extr_vallf bt (rev (int2bs h (val idx))) = Some leaf'
  => (exists (x x' : dgst) (i j : int),
        extract_coll_bt_ap bt (val ap) (rev (int2bs h (val idx))) leaf ps ad h 0 = Some (x, x', i, j) /\
        size x = 8 * n * 2 /\
        size x' = 8 * n * 2 /\
        x = val (val_bt_trh (oget (sub_bt bt (rev (int2bs (h - i + 1) (2 * j))))) ps ad (i - 1) (2 * j)) 
            ++ val (val_bt_trh (oget (sub_bt bt (rev (int2bs (h - i + 1) (2 * j + 1))))) ps ad (i - 1) (2 * j + 1)) /\
        valid_thidx i /\
        valid_thidx (i - 1) /\
        valid_tbidx i j /\
        valid_tbidx (i - 1) (2 * j) /\
        valid_tbidx (i - 1) (2 * j + 1) /\
        1 <= i <= h /\
        j = val idx %/ 2 ^ i /\
        x <> x' /\ 
        trh ps (set_thtbidx ad i j) x
        =
        trh ps (set_thtbidx ad i j) x').
proof.
move=> adtrh neqlfp_lf fb_bt eqh_hbt eqbtap extrlf.
move: (extract_coll_bt_ap_P bt (val ap) (rev (int2bs h (val idx))) leaf leaf' ps ad 0).
move=> /(_ _ _ _ _ _ _ _ _ _) //; rewrite ?valP ?eqh_hbt //.
+ by rewrite size_rev size_int2bs; smt(ge1_h).
+ by smt(ge1_h ge0_height).
+ by rewrite /valid_tbidx /= /nr_nodes /= expr0 //.
move => [x x' i j] [#] ? ? ? + ? ? ? ? ? ? ?.
rewrite rcons_take_rev_int2bs //= 1:/# rcons_take_rev_int2bs //= 1:/#.
rewrite int2bs0s cats0 //= (: h - (h - i) = i) 1:/# => xval.
rewrite take_rev_int2bs // 1:/# revK int2bsK 1:/# => [| *]; last by exists x x' i j => /#.
rewrite andaE; split; first by rewrite divz_ge0 1:expr_gt0 //; smt(Index.valP).
by rewrite ltz_divLR 1:expr_gt0 // -exprD_nneg; smt(ge1_h Index.valP).
qed.

(* 
  Constructs authentication path (embedding it in the corresponding subtype)
  for the special case of binary trees of height h and indices between 0 (including) and
  2 ^ h (including) w.r.t. a certain public seed, address, height index h, and breadth index
  0. Note that, in case the given binary tree is not of height h,
  this operator does not explicitly fail; instead, witness is returned.
*)
op cons_ap_trh (bt : dgstblock bintree) (idx : index) (ps : pseed) (ad : adrs) : apFLXMSSTW =
  DBHL.insubd (cons_ap_trh_gen bt (rev (int2bs h (val idx))) ps ad h 0).

(* 
  Computes value corresponding to an authentication path, leaf, and a path represented 
  by the big-endian binary representation of an index between 0 (including) 
  and 2 ^ h (including) w.r.t. a certain public seed, address, height index h, 
  and breadth index 0. 
*)
op val_ap_trh (ap : apFLXMSSTW) (idx : index) (leaf : dgstblock) (ps : pseed) (ad : adrs) : dgstblock = 
  val_ap_trh_gen (val ap) (rev (int2bs h (val idx))) leaf ps ad h 0.



(* --- Fixed-Length XMSS-TW in encompassing structure --- *)
(* -- Specification of Fixed-Length XMSS-TW in encompassing structure -- *)
module FL_XMSS_TW_ES = {
  (* Compute list of leaves from a secret seed, public seed, and address *) 
  proc leaves_from_sspsad(ss : sseed, ps : pseed, ad : adrs) : dgstblock list = {
    var skWOTS : skWOTS;
    var pkWOTS : pkWOTS;
    var leaf : dgstblock;
    var leafl : dgstblock list;
    
    leafl <- [];
    while (size leafl < l) {
      (* Generate a WOTS-TW secret key *)
      skWOTS <@ WOTS_TW_ES.gen_skWOTS(ss, ps, set_kpidx (set_typeidx ad chtype) (size leafl));
      
      (* Compute the WOTS-TW public key from the generated WOTS-TW secret key *)
      pkWOTS <@ WOTS_TW_ES.pkWOTS_from_skWOTS(skWOTS, ps, set_kpidx (set_typeidx ad chtype) (size leafl));
      
      (* Compute leaf from the computed WOTS-TW public key *)
      leaf <- pkco ps (set_kpidx (set_typeidx ad pkcotype) (size leafl)) (flatten (map DigestBlock.val (val pkWOTS)));

      leafl <- rcons leafl leaf;
    }
    
    return leafl;
  }

  (* Generate a key pair from a secret seed, public seed, and address *)
  proc keygen(ss : sseed, ps : pseed, ad : adrs) : pkFLXMSSTW * skFLXMSSTW = {
    var root : dgstblock;
    var skWOTS : skWOTS;
    var skWOTSl : skWOTS list;
    var leafl : dgstblock list;
    var pk : pkFLXMSSTW;
    var sk : skFLXMSSTW;
    
    (* Compute list of leaves *)
    leafl <@ leaves_from_sspsad(ss, ps, ad);
    
    (* 
      Compute root (hash value) from the computed list of leaves, given public seed, and
      given address (after setting the type to tree hashing)
    *)
    root <- val_bt_trh (list2tree leafl) ps (set_typeidx ad trhtype) h 0; 
    
    pk <- (root, ps, ad);
    sk <- (insubd 0, ss, ps, ad);
    
    return (pk, sk);
  }
  
  (* Sign the given message with the given secret key *)
  proc sign(sk : skFLXMSSTW, m : msgFLXMSSTW) : sigFLXMSSTW * skFLXMSSTW = {
    var idx : index;
    var ss : sseed;
    var ps : pseed;
    var ad : adrs;
    var skWOTS : skWOTS;
    var sigWOTS : sigWOTS;
    var skWOTSl : skWOTS list;
    var leafl : dgstblock list;
    var ap : apFLXMSSTW;
    var sig : sigFLXMSSTW;
    
    (* Extract index, secret seed, public seed, and address from the secret key *)
    idx <- sk.`1;
    ss <- sk.`2;
    ps <- sk.`3;
    ad <- sk.`4;
    
    (* Compute the WOTS-TW signature on the given message *)
    sigWOTS <@ WOTS_TW_ES.sign((ss, ps, insubd (set_kpidx (set_typeidx ad chtype) (val idx))), m);
    
    (* Compute the list of leaves *)
    leafl <@ leaves_from_sspsad(ss, ps, ad);
    
    (* Construct the authentication path from the computed list of leaves *)
    ap <- cons_ap_trh (list2tree leafl) idx ps (set_typeidx ad trhtype);
    
    sig <- (idx, sigWOTS, ap);
    sk <- (insubd (val idx + 1), ss, ps, ad);
    
    return (sig, sk);
  }
  
  (* Compute the root (hash) value from a message, signature, public seed, and address  *) 
  proc root_from_sigFLXMSSTW(m : msgFLXMSSTW, sig : sigFLXMSSTW, ps : pseed, ad : adrs) : dgstblock = {
    var idx : index;
    var pkWOTS : pkWOTS;
    var sigWOTS : sigWOTS;
    var ap : apFLXMSSTW;
    var leaf : dgstblock;
    var root : dgstblock;
    
    (* Extract index, WOTS-TW signature, and authentication path from the signature *)
    idx <- sig.`1;
    sigWOTS <- sig.`2;
    ap <- sig.`3;
    
    (* Compute WOTS-TW public key *)
    pkWOTS <@ WOTS_TW_ES.pkWOTS_from_sigWOTS(m, sigWOTS, ps, set_kpidx (set_typeidx ad chtype) (val idx));
    
    (* Compute leaf from the computed WOTS-TW public key *)
    leaf <- pkco ps (set_kpidx (set_typeidx ad pkcotype) (val idx)) (flatten (map DigestBlock.val (val pkWOTS)));
    
    (* Compute root from computed leaf (and extracted authentication path) *)
    root <- val_ap_trh ap idx leaf ps (set_typeidx ad trhtype);
    
    return root;
  }
  
  (* 
    Verify the given signature on the given message with the given public key
  *)
  proc verify(pk : pkFLXMSSTW, m : msgFLXMSSTW, sig : sigFLXMSSTW) : bool = {
    var ps : pseed;
    var ad : adrs;
    var root : dgstblock;
    var root' : dgstblock;
    var pkWOTS : pkWOTS;
    var sigWOTS : sigWOTS;
    var pk' : pkFLXMSSTW;
    var is_valid : bool;
  
    (* Extract root (hash) value, public seed, and address from the public key *)     
    root <- pk.`1;
    ps <- pk.`2;
    ad <- pk.`3;
    
    (* Compute root (hash) value to check extracted root (hash) value against *)
    root' <@ root_from_sigFLXMSSTW(m, sig, ps, ad);
    
    return root' = root;
  }
}.


(* -- Adversary classes -- *)
module type Adv_EUFRMA_FLXMSSTWES = {
  proc choose() : adrs
  proc forge(pk : pkFLXMSSTW, msigl : (msgFLXMSSTW * sigFLXMSSTW) list) : msgFLXMSSTW * sigFLXMSSTW
}.


(* -- Notion(s) -- *) 
(* EUF-RMA for Fixed-Length XMSS-TW in an encompassing structure *)
module EUF_RMA_FLXMSSTWES(A : Adv_EUFRMA_FLXMSSTWES)  = {
  proc main() : bool = {
    var ss : sseed;
    var ps : pseed;
    var ad : adrs;
    var pk : pkFLXMSSTW;
    var sk : skFLXMSSTW;
    var m, m' : msgFLXMSSTW;
    var sig, sig' : sigFLXMSSTW;
    var msig : msgFLXMSSTW * sigFLXMSSTW;
    var msigl : (msgFLXMSSTW * sigFLXMSSTW) list;
    var is_valid, is_fresh : bool;
    
    ss <$ dsseed;
    ps <$ dpseed;

    ad <@ A.choose();
    
    (pk, sk) <@ FL_XMSS_TW_ES.keygen(ss, ps, ad);
    
    msigl <- [];
    while (size msigl < l) {
      m <$ dmsgFLXMSSTW;
      
      (sig, sk) <@ FL_XMSS_TW_ES.sign(sk, m);
      
      msig <- (m, sig);
      msigl <- rcons msigl msig;
    }
    
    (m', sig') <@ A.forge(pk, msigl);
    
    is_valid <@ FL_XMSS_TW_ES.verify(pk, m', sig');
    
    is_fresh <- ! m' \in unzip1 msigl; 
    
    return is_valid /\ is_fresh;
  }
}.

(* 
  EUF_RMA_FLXMSSTWES_NOPRF
  Essentially identical to EUF_RMA_FLXMSSTWES, except that everything is inlined and all 
  WOTS_TW secret keys are sampled uniformly at random from their domain (at once) 
  instead of individually generated by a PRF.
*)
module EUF_RMA_FLXMSSTWES_NOPRF(A : Adv_EUFRMA_FLXMSSTWES) = {
  proc main() : bool = {
    var ps : pseed;
    var ad : adrs;    
    var root : dgstblock;
    var pkWOTS_ele, pkWOTS_ele' : dgstblock;
    var skWOTS_ele : dgstblock;
    var sigWOTS_ele, sigWOTS_ele' : dgstblock;
    var em_ele : int;
    var pkWOTS, pkWOTS' : dgstblock list;
    var skWOTS : dgstblock list;
    var sigWOTS, sigWOTS' : dgstblock list;
    var pk : pkFLXMSSTW;
    var sk : skFLXMSSTW;
    var m, m' : msgFLXMSSTW;
    var em : emsgWOTS;
    var sig, sig' : sigFLXMSSTW;
    var idx' : index;
    var leaf, leaf' : dgstblock;
    var root' : dgstblock;
    var ap, ap' : apFLXMSSTW;
    var msig : msgFLXMSSTW * sigFLXMSSTW;
    var skWOTSl : dgstblock list list;
    var leafl : dgstblock list;
    var msigl : (msgFLXMSSTW * sigFLXMSSTW) list;
    var is_valid, is_fresh : bool;
    
    ps <$ dpseed;

    ad <@ A.choose();
    
    (* (pk, sk) <@ FL_XMSS_TW_ES.keygen(ss, ps, ad); *)
    skWOTSl <- [];
    leafl <- [];
    while (size leafl < l) {
      skWOTS <$ ddgstblockl;
    
      (* pkWOTS <@ WOTS_TW_ES.pkWOTS_from_skWOTS(skWOTS, ps, set_kpidx (set_typeidx ad chtype) (size leafl)); *)
      pkWOTS <- [];
      while (size pkWOTS < len) {
        skWOTS_ele <- nth witness skWOTS (size pkWOTS);
        pkWOTS_ele <- cf ps (set_chthidx (set_kpidx (set_typeidx ad chtype) (size leafl)) (size pkWOTS)) 0 (w - 1) (val skWOTS_ele);
        pkWOTS <- rcons pkWOTS pkWOTS_ele;
      }
      
      leaf <- pkco ps (set_kpidx (set_typeidx ad pkcotype) (size leafl)) (flatten (map DigestBlock.val pkWOTS));
      
      skWOTSl <- rcons skWOTSl skWOTS;
      leafl <- rcons leafl leaf;
    }
    
    root <- val_bt_trh (list2tree leafl) ps (set_typeidx ad trhtype) h 0;
    pk <- (root, ps, ad);
    
    msigl <- [];
    while (size msigl < l) {
      m <$ dmsgFLXMSSTW;
      
      (* (sig, sk) <@ FL_XMSS_TW_ES.sign(sk, m); *)
      (* sigWOTS <@ WOTS_TW_ES.sign((ss, ps, set_kpidx (set_typeidx ad chtype) (size msigl)), m); *)
      em <- encode_msgWOTS m;
      skWOTS <- nth witness skWOTSl (size msigl);
      sigWOTS <- [];
      while (size sigWOTS < len){
        skWOTS_ele <- nth witness skWOTS (size sigWOTS);
        em_ele <- BaseW.val (em.[size sigWOTS]);
        sigWOTS_ele <- cf ps (set_chthidx (set_kpidx (set_typeidx ad chtype) (size msigl)) (size sigWOTS)) 0 em_ele (val skWOTS_ele);
        sigWOTS <- rcons sigWOTS sigWOTS_ele;
      }
      
      ap <- cons_ap_trh (list2tree leafl) (insubd (size msigl)) ps (set_typeidx ad trhtype);
      sig <- (insubd (size msigl), DBLL.insubd sigWOTS, ap);
    
      msig <- (m, sig);
      msigl <- rcons msigl msig;
    }
    
    (m', sig') <@ A.forge(pk, msigl);
    
    (* is_valid <@ FL_XMSS_TW_ES.verify(pk, m', sig'); *)
    idx' <- sig'.`1;
    sigWOTS' <- val sig'.`2;
    ap' <- sig'.`3;
    
    (* pkWOTS' <@ WOTS_TW_ES.pkWOTS_from_sigWOTS(m', sigWOTS', ps, set_kpidx (set_typeidx ad chtype) idx'); *)
    em <- encode_msgWOTS m';
    pkWOTS' <- [];
    while (size pkWOTS' < len) {
      sigWOTS_ele' <- nth witness sigWOTS' (size pkWOTS');
      em_ele <- BaseW.val em.[size pkWOTS'];
      pkWOTS_ele' <- cf ps (set_chthidx (set_kpidx (set_typeidx ad chtype) (val idx')) (size pkWOTS')) em_ele (w - 1 - em_ele) (val sigWOTS_ele');
      pkWOTS' <- rcons pkWOTS' pkWOTS_ele';
    }
    
    leaf' <- pkco ps (set_kpidx (set_typeidx ad pkcotype) (val idx')) (flatten (map DigestBlock.val pkWOTS'));
    root' <- val_ap_trh ap' idx' leaf' ps (set_typeidx ad trhtype);
    
    is_valid <- root' = root;
    
    is_fresh <- ! m' \in unzip1 msigl; 
    
    return is_valid /\ is_fresh;
  }
}.


(* -- Reduction Adversaries -- *)
module (R_PRF_FLXMSSTWESInlineNOPRF (A : Adv_EUFRMA_FLXMSSTWES) : PRF_SK_PRF.Adv_PRF) (O : PRF_SK_PRF.Oracle_PRF) = {
  proc distinguish() : bool = {
    var ss : sseed;
    var ps : pseed;
    var ad : adrs;    
    var root : dgstblock;
    var pkWOTS_ele, pkWOTS_ele' : dgstblock;
    var skWOTS_ele : dgstblock;
    var sigWOTS_ele, sigWOTS_ele' : dgstblock;
    var em_ele : int;
    var pkWOTS, pkWOTS' : dgstblock list;
    var skWOTS : dgstblock list;
    var sigWOTS, sigWOTS' : dgstblock list;
    var pk : pkFLXMSSTW;
    var sk : skFLXMSSTW;
    var m, m' : msgFLXMSSTW;
    var em : emsgWOTS;
    var sig, sig' : sigFLXMSSTW;
    var idx' : index;
    var leaf, leaf' : dgstblock;
    var root' : dgstblock;
    var ap, ap' : apFLXMSSTW;
    var msig : msgFLXMSSTW * sigFLXMSSTW;
    var skWOTSl : dgstblock list list;
    var pkWOTSl : dgstblock list list;
    var leafl : dgstblock list;
    var msigl : (msgFLXMSSTW * sigFLXMSSTW) list;
    var is_valid, is_fresh : bool;
    
    ps <$ dpseed;

    ad <@ A.choose();
    
    (* (pk, sk) <@ FL_XMSS_TW_ES.keygen(ss, ps, ad); *)
    skWOTSl <- [];
    pkWOTSl <- [];
    leafl <- [];
    while (size leafl < l) {
      (* skWOTS <@ WOTS_TW_ES.gen_skWOTS(ss, ps, set_kpidx (set_typeidx ad chtype) (size leafl)); *)
      skWOTS <- [];
      while (size skWOTS < len){
        skWOTS_ele <@ O.query((ps, set_htbidx (set_chthidx (set_kpidx (set_typeidx ad chtype) (size leafl)) (size skWOTS)) 0));
        skWOTS <- rcons skWOTS skWOTS_ele;
      }
    
      (* pkWOTS <@ WOTS_TW_ES.pkWOTS_from_skWOTS(skWOTS, ps, set_kpidx (set_typeidx ad chtype) (size leafl)); *)
      pkWOTS <- [];
      while (size pkWOTS < len) {
        skWOTS_ele <- nth witness skWOTS (size pkWOTS);
        pkWOTS_ele <- cf ps (set_chthidx (set_kpidx (set_typeidx ad chtype) (size leafl)) (size pkWOTS)) 0 (w - 1) (val skWOTS_ele);
        pkWOTS <- rcons pkWOTS pkWOTS_ele;
      }
      
      leaf <- pkco ps (set_kpidx (set_typeidx ad pkcotype) (size leafl)) (flatten (map DigestBlock.val pkWOTS));
      
      skWOTSl <- rcons skWOTSl skWOTS;
      pkWOTSl <- rcons pkWOTSl pkWOTS;
      leafl <- rcons leafl leaf;
    }
    
    root <- val_bt_trh (list2tree leafl) ps (set_typeidx ad trhtype) h 0;
    pk <- (root, ps, ad);
    
    msigl <- [];
    while (size msigl < l) {
      m <$ dmsgFLXMSSTW;
      
      (* (sig, sk) <@ FL_XMSS_TW_ES.sign(sk, m); *)
      (* sigWOTS <@ WOTS_TW_ES.sign((ss, ps, set_kpidx (set_typeidx ad chtype) (size msigl)), m); *)
      em <- encode_msgWOTS m;
      skWOTS <- nth witness skWOTSl (size msigl);
      sigWOTS <- [];
      while (size sigWOTS < len){
        skWOTS_ele <- nth witness skWOTS (size sigWOTS);
        em_ele <- BaseW.val (em.[size sigWOTS]);
        sigWOTS_ele <- cf ps (set_chthidx (set_kpidx (set_typeidx ad chtype) (size msigl)) (size sigWOTS)) 0 em_ele (val skWOTS_ele);
        sigWOTS <- rcons sigWOTS sigWOTS_ele;
      }
      
      ap <- cons_ap_trh (list2tree leafl) (insubd (size msigl)) ps (set_typeidx ad trhtype);
      sig <- (insubd (size msigl), DBLL.insubd sigWOTS, ap);
    
      msig <- (m, sig);
      msigl <- rcons msigl msig;
    }
    
    (m', sig') <@ A.forge(pk, msigl);
    
    (* is_valid <@ FL_XMSS_TW_ES.verify(pk, m', sig'); *)
    idx' <- sig'.`1;
    sigWOTS' <- val sig'.`2;
    ap' <- sig'.`3;
    
    (* pkWOTS' <@ WOTS_TW_ES.pkWOTS_from_sigWOTS(m', sigWOTS', ps, set_kpidx (set_typeidx ad chtype) idx'); *)
    em <- encode_msgWOTS m';
    pkWOTS' <- [];
    while (size pkWOTS' < len) {
      sigWOTS_ele' <- nth witness sigWOTS' (size pkWOTS');
      em_ele <- BaseW.val em.[size pkWOTS'];
      pkWOTS_ele' <- cf ps (set_chthidx (set_kpidx (set_typeidx ad chtype) (val idx')) (size pkWOTS')) em_ele (w - 1 - em_ele) (val sigWOTS_ele');
      pkWOTS' <- rcons pkWOTS' pkWOTS_ele';
    }
    
    leaf' <- pkco ps (set_kpidx (set_typeidx ad pkcotype) (val idx')) (flatten (map DigestBlock.val pkWOTS'));
    
    root' <- val_ap_trh ap' idx' leaf' ps (set_typeidx ad trhtype);
    
    is_valid <- root' = root;
    
    is_fresh <- ! m' \in unzip1 msigl; 
    
    return is_valid /\ is_fresh;
  }
}. 

module (R_MEUFGCMAWOTSTWES_EUFRMAFLXMSSTWESNOPRF (A : Adv_EUFRMA_FLXMSSTWES) : Adv_MEUFGCMA_WOTSTWES) (O : Oracle_MEUFGCMA_WOTSTWES, OC : FC.Oracle_THFC) = {
  var ad : adrs
  var ml : msgFLXMSSTW list
  var pkWOTSl : dgstblock list list
  var sigWOTSl : dgstblock list list
  
  proc choose() : unit = {
    var m : msgFLXMSSTW;
    var pkWOTS : pkWOTS;
    var sigWOTS : sigWOTS;
    var i : int;
    
    ad <@ A.choose();
    
    ml <- [];
    pkWOTSl <- [];
    sigWOTSl <- [];
    i <- 0;
    while (i < l) {
      m <$ dmsgFLXMSSTW;
      
      (pkWOTS, sigWOTS) <@ O.query(ChainingAddress.insubd (set_kpidx (set_typeidx ad chtype) i), m);
      
      ml <- rcons ml m;
      pkWOTSl <- rcons pkWOTSl (val pkWOTS);
      sigWOTSl <- rcons sigWOTSl (val sigWOTS);
      i <- i + 1;
    }
  }
  
  proc forge(ps : pseed) : int * msgWOTS * sigWOTS = {
    var leaf : dgstblock;
    var leafl : dgstblock list;
    var ap : apFLXMSSTW;
    var root : dgstblock;
    var pk : pkFLXMSSTW;
    var sig, sig' : sigFLXMSSTW;
    var msig : msgFLXMSSTW * sigFLXMSSTW;
    var msigl : (msgFLXMSSTW * sigFLXMSSTW) list;
    var idx, idx' : index;
    var m, m' : msgFLXMSSTW;
    var pkWOTS : dgstblock list;
    var sigWOTS : dgstblock list;
    var sigWOTS' : sigWOTS;
    
    leafl <- [];
    while (size leafl < l) {
      pkWOTS <- nth witness pkWOTSl (size leafl);
      
      leaf <- pkco ps (set_kpidx (set_typeidx ad pkcotype) (size leafl)) (flatten (map DigestBlock.val pkWOTS)); 
      leafl <- rcons leafl leaf;
    }
    
    root <- val_bt_trh (list2tree leafl) ps (set_typeidx ad trhtype) h 0;
    pk <- (root, ps, ad);
    
    msigl <- [];
    while (size msigl < l) {
      idx <- insubd (size msigl);
      
      sigWOTS <- nth witness sigWOTSl (val idx);
      ap <- cons_ap_trh (list2tree leafl) idx ps (set_typeidx ad trhtype);
    
      m <- nth witness ml (val idx);
      sig <- (idx, DBLL.insubd sigWOTS, ap);
      
      msig <- (m, sig);
      msigl <- rcons msigl msig;
    }
    
    (m', sig') <@ A.forge(pk, msigl);
    
    idx' <- sig'.`1;
    sigWOTS' <- sig'.`2;
    
    return (val idx', m', sigWOTS');
  }
}.

module (R_SMDTTCRCPKCO_EUFRMAFLXMSSTWESNOPRF (A : Adv_EUFRMA_FLXMSSTWES) : PKCOC_TCR.Adv_SMDTTCRC) (O : PKCOC_TCR.Oracle_SMDTTCR, OC : PKCOC.Oracle_THFC) = {
  var ad : adrs
  var skWOTSl : dgstblock list list
  var leafl : dgstblock list
  
  proc pick() : unit = {
    var skWOTS : dgstblock list;
    var pkWOTS : dgstblock list;
    var leaf : dgstblock;
    var pkWOTS_ele : dgstblock;
    var i : int;
    
    ad <@ A.choose();
    
    skWOTSl <- [];
    leafl <- [];
    while (size leafl < l) {
      skWOTS <$ ddgstblockl;
    
      pkWOTS <- [];
      while (size pkWOTS < len) {
        pkWOTS_ele <- nth witness skWOTS (size pkWOTS);
        
        i <- 0;
        while (i < w - 1) {
          pkWOTS_ele <@ OC.query(set_htbidx (set_chthidx (set_kpidx (set_typeidx ad chtype) (size leafl)) (size pkWOTS)) i, val pkWOTS_ele);
          i <- i + 1;
        }
        
        pkWOTS <- rcons pkWOTS pkWOTS_ele;
      }
      
      leaf <@ O.query(set_kpidx (set_typeidx ad pkcotype) (size leafl), flatten (map DigestBlock.val pkWOTS));
      
      skWOTSl <- rcons skWOTSl skWOTS;
      leafl <- rcons leafl leaf;
    }
  }
  
  proc find(ps : pseed) : int * dgst = {
    var skWOTS : dgstblock list;
    var pkWOTS' : dgstblock list;
    var sigWOTS, sigWOTS' : dgstblock list;
    var m, m' : msgFLXMSSTW;
    var em : emsgWOTS;
    var sig, sig' : sigFLXMSSTW;
    var root : dgstblock;
    var ap, ap' : apFLXMSSTW;
    var pk : pkFLXMSSTW;
    var msig : msgFLXMSSTW * sigFLXMSSTW;
    var msigl : (msgFLXMSSTW * sigFLXMSSTW) list;
    var skWOTS_ele : dgstblock;
    var pkWOTS_ele' : dgstblock;
    var sigWOTS_ele, sigWOTS_ele' : dgstblock;
    var em_ele : int;
    var idx' : index;
    
    root <- val_bt_trh (list2tree leafl) ps (set_typeidx ad trhtype) h 0;
    pk <- (root, ps, ad);
    
    msigl <- [];
    while (size msigl < l) {
      m <$ dmsgFLXMSSTW;
      
      (* (sig, sk) <@ FL_XMSS_TW_ES.sign(sk, m); *)
      (* sigWOTS <@ WOTS_TW_ES.sign((ss, ps, set_kpidx (set_typeidx ad chtype) (size msigl)), m); *)
      em <- encode_msgWOTS m;
      skWOTS <- nth witness skWOTSl (size msigl);
      sigWOTS <- [];
      while (size sigWOTS < len){
        skWOTS_ele <- nth witness skWOTS (size sigWOTS);
        em_ele <- BaseW.val (em.[size sigWOTS]);
        sigWOTS_ele <- cf ps (set_chthidx (set_kpidx (set_typeidx ad chtype) (size msigl)) (size sigWOTS)) 0 em_ele (val skWOTS_ele);
        sigWOTS <- rcons sigWOTS sigWOTS_ele;
      }
      
      ap <- cons_ap_trh (list2tree leafl) (insubd (size msigl)) ps (set_typeidx ad trhtype);
      sig <- (insubd (size msigl), DBLL.insubd sigWOTS, ap);
    
      msig <- (m, sig);
      msigl <- rcons msigl msig;
    }
    
    (m', sig') <@ A.forge(pk, msigl);
    
    idx' <- sig'.`1;
    sigWOTS' <- val sig'.`2;
    ap' <- sig'.`3;
    
    em <- encode_msgWOTS m';
    pkWOTS' <- [];
    while (size pkWOTS' < len) {
      sigWOTS_ele' <- nth witness sigWOTS' (size pkWOTS');
      em_ele <- BaseW.val em.[size pkWOTS'];
      pkWOTS_ele' <- cf ps (set_chthidx (set_kpidx (set_typeidx ad chtype) (val idx')) (size pkWOTS')) em_ele (w - 1 - em_ele) (val sigWOTS_ele');
      pkWOTS' <- rcons pkWOTS' pkWOTS_ele';
    }
    
    return (val idx', flatten (map DigestBlock.val pkWOTS'));
  }
}.

module (R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF (A : Adv_EUFRMA_FLXMSSTWES) : TRHC_TCR.Adv_SMDTTCRC) (O : TRHC_TCR.Oracle_SMDTTCR, OC : TRHC.Oracle_THFC) = {
  var ad : adrs
  var skWOTSl : dgstblock list list
  var leafl : dgstblock list
  var adrsll : adrs list list
  var inpll : dgst list list
  var nodell : dgstblock list list
  var root : dgstblock
  
  proc pick() : unit = {
    var skWOTS : dgstblock list;
    var pkWOTS : dgstblock list;
    var leaf : dgstblock;
    var node, lnode, rnode : dgstblock;
    var adrsl : adrs list;
    var inpl : dgst list;
    var nodel, nodel' : dgstblock list;
    var pkWOTS_ele : dgstblock;
    var i : int;
    
    ad <@ A.choose();
    
    skWOTSl <- [];
    leafl <- [];
    while (size leafl < l) {
      skWOTS <$ ddgstblockl;
    
      pkWOTS <- [];
      while (size pkWOTS < len) {
        pkWOTS_ele <- nth witness skWOTS (size pkWOTS);
        
        i <- 0;
        while (i < w - 1) {
          pkWOTS_ele <@ OC.query(set_htbidx (set_chthidx (set_kpidx (set_typeidx ad chtype) (size leafl)) (size pkWOTS)) i, val pkWOTS_ele);
          i <- i + 1;
        }
        
        pkWOTS <- rcons pkWOTS pkWOTS_ele;
      }
      
      leaf <@ OC.query(set_kpidx (set_typeidx ad pkcotype) (size leafl), flatten (map DigestBlock.val pkWOTS));
      
      skWOTSl <- rcons skWOTSl skWOTS;
      leafl <- rcons leafl leaf;
    }
    
    adrsll <- [];
    inpll <- [];
    nodell <- [];
    while (size nodell < h) {
      adrsl <- [];
      inpl <- [];
      nodel <- [];
      
      nodel' <- last leafl nodell;
         
      while (size nodel < 2 ^ (h - size nodell - 1)) {
        lnode <- nth witness nodel' (2 * (size nodel));
        rnode <- nth witness nodel' (2 * (size nodel) + 1);
        
        node <@ O.query(set_thtbidx (set_typeidx ad trhtype) (size nodell + 1) (size nodel), val lnode ++ val rnode);
        
        adrsl <- rcons adrsl (set_thtbidx (set_typeidx ad trhtype) (size nodell + 1) (size nodel));
        inpl <- rcons inpl (val lnode ++ val rnode);
        nodel <- rcons nodel node;
      }
      
      adrsll <- rcons adrsll adrsl;
      inpll <- rcons inpll inpl;
      nodell <- rcons nodell nodel; 
    }
    
    root <- nth witness (nth witness nodell (h - 1)) 0; (* root <- node; *)
  }
  
  proc find(ps : pseed) : int * dgst = {
    var skWOTS : dgstblock list;
    var pkWOTS' : dgstblock list;
    var sigWOTS, sigWOTS' : dgstblock list;
    var m, m' : msgFLXMSSTW;
    var em : emsgWOTS;
    var sig, sig' : sigFLXMSSTW;
    var leaf' : dgstblock;
    var ap, ap' : apFLXMSSTW;
    var x, x' : dgst;
    var hidx, bidx : int;
    var pk : pkFLXMSSTW;
    var msig : msgFLXMSSTW * sigFLXMSSTW;
    var msigl : (msgFLXMSSTW * sigFLXMSSTW) list;
    var skWOTS_ele : dgstblock;
    var pkWOTS_ele' : dgstblock;
    var sigWOTS_ele, sigWOTS_ele' : dgstblock;
    var em_ele : int;
    var idx' : index;
    
    pk <- (root, ps, ad);
    
    msigl <- [];
    while (size msigl < l) {
      m <$ dmsgFLXMSSTW;
      
      em <- encode_msgWOTS m;
      skWOTS <- nth witness skWOTSl (size msigl);
      sigWOTS <- [];
      while (size sigWOTS < len){
        skWOTS_ele <- nth witness skWOTS (size sigWOTS);
        em_ele <- BaseW.val (em.[size sigWOTS]);
        sigWOTS_ele <- cf ps (set_chthidx (set_kpidx (set_typeidx ad chtype) (size msigl)) (size sigWOTS)) 0 em_ele (val skWOTS_ele);
        sigWOTS <- rcons sigWOTS sigWOTS_ele;
      }
      
      ap <- cons_ap_trh (list2tree leafl) (insubd (size msigl)) ps (set_typeidx ad trhtype);
      sig <- (insubd (size msigl), DBLL.insubd sigWOTS, ap);
    
      msig <- (m, sig);
      msigl <- rcons msigl msig;
    }
    
    (m', sig') <@ A.forge(pk, msigl);
    
    idx' <- sig'.`1;
    sigWOTS' <- val sig'.`2;
    ap' <- sig'.`3;
    
    em <- encode_msgWOTS m';
    pkWOTS' <- [];
    while (size pkWOTS' < len) {
      sigWOTS_ele' <- nth witness sigWOTS' (size pkWOTS');
      em_ele <- BaseW.val em.[size pkWOTS'];
      pkWOTS_ele' <- cf ps (set_chthidx (set_kpidx (set_typeidx ad chtype) (val idx')) (size pkWOTS')) em_ele (w - 1 - em_ele) (val sigWOTS_ele');
      pkWOTS' <- rcons pkWOTS' pkWOTS_ele';
    }
    
    leaf' <- pkco ps (set_kpidx (set_typeidx ad pkcotype) (val idx')) (flatten (map DigestBlock.val pkWOTS'));
    
    (x, x', hidx, bidx) <- oget (extract_coll_bt_ap (list2tree leafl) (val ap') (rev (int2bs h (val idx'))) leaf' ps (set_typeidx ad trhtype) h 0);
    
    return (sumz (map size (take (hidx - 1) inpll)) + bidx, x');
  }
}.


(* -- Proof of EUF-RMA for Fixed-Length XMSS-TW (in an encompassing structure) -- *)
section Proof_EUF_RMA_FLXMSSTWES.
(* - Module declarations - *)
declare module A <: Adv_EUFRMA_FLXMSSTWES{-PRF_SK_PRF.O_PRF_Default, -FC.O_THFC_Default, -FC_PRE.O_SMDTPRE_Default, -FC_TCR.O_SMDTTCR_Default, -FC_UD.O_SMDTUD_Default, -PKCOC_TCR.O_SMDTTCR_Default, -PKCOC.O_THFC_Default, -TRHC_TCR.O_SMDTTCR_Default, -TRHC.O_THFC_Default, -O_MEUFGCMA_WOTSTWES, -R_PRF_FLXMSSTWESInlineNOPRF, -R_SMDTUDC_Game23WOTSTWES, -R_SMDTTCRC_Game34WOTSTWES, -R_SMDTPREC_Game4WOTSTWES, -R_MEUFGCMAWOTSTWES_EUFRMAFLXMSSTWESNOPRF, -R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF, -R_SMDTTCRCPKCO_EUFRMAFLXMSSTWESNOPRF, -R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF}.

declare axiom A_choose_ll : islossless A.choose.
declare axiom A_forge_ll : islossless A.forge.


(* - Auxiliary import - *)
(* 
  Import necessary definitions/properties to reason about programs sampling from
  dlist distributions
*)  
local clone import DList.Program as DListSample with
  type t <= dgstblock,
  op d <= ddgstblock.


(* - Game sequence - *)
(* 
  EUF_RMA_FLXMSSTWES -- Inlined version
  Semantically equivalent to EUF_RMA_FLXMSSTWES, but all procedure calls to FL_XMSS_TW_ES
  and WOTS_TW_ES are inlined. Redundant statements arising from this inlining are removed 
*)
local module EUF_RMA_FLXMSSTWES_Inline = {
  proc main() : bool = {
    var ss : sseed;
    var ps : pseed;
    var ad : adrs;    
    var root : dgstblock;
    var pkWOTS_ele, pkWOTS_ele' : dgstblock;
    var skWOTS_ele : dgstblock;
    var sigWOTS_ele, sigWOTS_ele' : dgstblock;
    var em_ele : int;
    var pkWOTS, pkWOTS' : dgstblock list;
    var skWOTS : dgstblock list;
    var sigWOTS, sigWOTS' : dgstblock list;
    var pk : pkFLXMSSTW;
    var sk : skFLXMSSTW;
    var m, m' : msgFLXMSSTW;
    var em : emsgWOTS;
    var sig, sig' : sigFLXMSSTW;
    var idx' : index;
    var leaf, leaf' : dgstblock;
    var root' : dgstblock;
    var ap, ap' : apFLXMSSTW;
    var msig : msgFLXMSSTW * sigFLXMSSTW;
    var skWOTSl : dgstblock list list;
    var pkWOTSl : dgstblock list list;
    var leafl : dgstblock list;
    var msigl : (msgFLXMSSTW * sigFLXMSSTW) list;
    var is_valid, is_fresh : bool;
    
    ss <$ dsseed;
    ps <$ dpseed;

    ad <@ A.choose();
    
    (* (pk, sk) <@ FL_XMSS_TW_ES.keygen(ss, ps, ad); *)
    skWOTSl <- [];
    pkWOTSl <- [];
    leafl <- [];
    while (size leafl < l) {
      (* skWOTS <@ WOTS_TW_ES.gen_skWOTS(ss, ps, set_kpidx (set_typeidx ad chtype) (size leafl)); *)
      skWOTS <- [];
      while (size skWOTS < len){
        skWOTS_ele <- prf_sk ss (ps, set_htbidx (set_chthidx (set_kpidx (set_typeidx ad chtype) (size leafl)) (size skWOTS)) 0);
        skWOTS <- rcons skWOTS skWOTS_ele;
      }
    
      (* pkWOTS <@ WOTS_TW_ES.pkWOTS_from_skWOTS(skWOTS, ps, set_kpidx (set_typeidx ad chtype) (size leafl)); *)
      pkWOTS <- [];
      while (size pkWOTS < len) {
        skWOTS_ele <- nth witness skWOTS (size pkWOTS);
        pkWOTS_ele <- cf ps (set_chthidx (set_kpidx (set_typeidx ad chtype) (size leafl)) (size pkWOTS)) 0 (w - 1) (val skWOTS_ele);
        pkWOTS <- rcons pkWOTS pkWOTS_ele;
      }
      
      leaf <- pkco ps (set_kpidx (set_typeidx ad pkcotype) (size leafl)) (flatten (map DigestBlock.val pkWOTS));
      
      skWOTSl <- rcons skWOTSl skWOTS;
      pkWOTSl <- rcons pkWOTSl pkWOTS;
      leafl <- rcons leafl leaf;
    }
    
    root <- val_bt_trh (list2tree leafl) ps (set_typeidx ad trhtype) h 0;
    pk <- (root, ps, ad);
    
    msigl <- [];
    while (size msigl < l) {
      m <$ dmsgFLXMSSTW;
      
      (* (sig, sk) <@ FL_XMSS_TW_ES.sign(sk, m); *)
      (* sigWOTS <@ WOTS_TW_ES.sign((ss, ps, set_kpidx (set_typeidx ad chtype) (size msigl)), m); *)
      em <- encode_msgWOTS m;
      skWOTS <- nth witness skWOTSl (size msigl);
      sigWOTS <- [];
      while (size sigWOTS < len){
        skWOTS_ele <- nth witness skWOTS (size sigWOTS);
        em_ele <- BaseW.val (em.[size sigWOTS]);
        sigWOTS_ele <- cf ps (set_chthidx (set_kpidx (set_typeidx ad chtype) (size msigl)) (size sigWOTS)) 0 em_ele (val skWOTS_ele);
        sigWOTS <- rcons sigWOTS sigWOTS_ele;
      }
      
      ap <- cons_ap_trh (list2tree leafl) (insubd (size msigl)) ps (set_typeidx ad trhtype);
      sig <- (insubd (size msigl), DBLL.insubd sigWOTS, ap);
    
      msig <- (m, sig);
      msigl <- rcons msigl msig;
    }
    
    (m', sig') <@ A.forge(pk, msigl);
    
    (* is_valid <@ FL_XMSS_TW_ES.verify(pk, m', sig'); *)
    idx' <- sig'.`1;
    sigWOTS' <- val sig'.`2;
    ap' <- sig'.`3;
    
    (* pkWOTS' <@ WOTS_TW_ES.pkWOTS_from_sigWOTS(m', sigWOTS', ps, set_kpidx (set_typeidx ad chtype) idx'); *)
    em <- encode_msgWOTS m';
    pkWOTS' <- [];
    while (size pkWOTS' < len) {
      sigWOTS_ele' <- nth witness sigWOTS' (size pkWOTS');
      em_ele <- BaseW.val em.[size pkWOTS'];
      pkWOTS_ele' <- cf ps (set_chthidx (set_kpidx (set_typeidx ad chtype) (val idx')) (size pkWOTS')) em_ele (w - 1 - em_ele) (val sigWOTS_ele');
      pkWOTS' <- rcons pkWOTS' pkWOTS_ele';
    }
    
    leaf' <- pkco ps (set_kpidx (set_typeidx ad pkcotype) (val idx')) (flatten (map DigestBlock.val pkWOTS'));
    root' <- val_ap_trh ap' idx' leaf' ps (set_typeidx ad trhtype);
    
    is_valid <- root' = root;
    
    is_fresh <- ! m' \in unzip1 msigl; 
    
    return is_valid /\ is_fresh;
  }
}.

(* 
  EUF_RMA_FLXMSSTWES_NOPRF_SampleSample
  Auxiliary game to go from sampling all WOTS-TW secret key from their domain (at once)
  to individually sampling them 
*)
local module EUF_RMA_FLXMSSTWES_NOPRF_SampleSample = {
  proc main() : bool = {
    var ps : pseed;
    var ad : adrs;    
    var root : dgstblock;
    var pkWOTS_ele, pkWOTS_ele' : dgstblock;
    var skWOTS_ele : dgstblock;
    var sigWOTS_ele, sigWOTS_ele' : dgstblock;
    var em_ele : int;
    var pkWOTS, pkWOTS' : dgstblock list;
    var skWOTS : dgstblock list;
    var sigWOTS, sigWOTS' : dgstblock list;
    var pk : pkFLXMSSTW;
    var sk : skFLXMSSTW;
    var m, m' : msgFLXMSSTW;
    var em : emsgWOTS;
    var sig, sig' : sigFLXMSSTW;
    var idx' : index;
    var leaf, leaf' : dgstblock;
    var root' : dgstblock;
    var ap, ap' : apFLXMSSTW;
    var msig : msgFLXMSSTW * sigFLXMSSTW;
    var skWOTSl : dgstblock list list;
    var leafl : dgstblock list;
    var msigl : (msgFLXMSSTW * sigFLXMSSTW) list;
    var is_valid, is_fresh : bool;
    
    ps <$ dpseed;

    ad <@ A.choose();
    
    (* (pk, sk) <@ FL_XMSS_TW_ES.keygen(ss, ps, ad); *)
    skWOTSl <- [];
    leafl <- [];
    while (size leafl < l) {
      skWOTS <@ DListSample.Sample.sample(len);
      
      (* pkWOTS <@ WOTS_TW_ES.pkWOTS_from_skWOTS(skWOTS, ps, set_kpidx (set_typeidx ad chtype) (size leafl)); *)
      pkWOTS <- [];
      while (size pkWOTS < len) {
        skWOTS_ele <- nth witness skWOTS (size pkWOTS);
        pkWOTS_ele <- cf ps (set_chthidx (set_kpidx (set_typeidx ad chtype) (size leafl)) (size pkWOTS)) 0 (w - 1) (val skWOTS_ele);
        pkWOTS <- rcons pkWOTS pkWOTS_ele;
      }
      
      leaf <- pkco ps (set_kpidx (set_typeidx ad pkcotype) (size leafl)) (flatten (map DigestBlock.val pkWOTS));
      
      skWOTSl <- rcons skWOTSl skWOTS;
      leafl <- rcons leafl leaf;
    }
    
    root <- val_bt_trh (list2tree leafl) ps (set_typeidx ad trhtype) h 0;
    pk <- (root, ps, ad);
    
    msigl <- [];
    while (size msigl < l) {
      m <$ dmsgFLXMSSTW;
      
      (* (sig, sk) <@ FL_XMSS_TW_ES.sign(sk, m); *)
      (* sigWOTS <@ WOTS_TW_ES.sign((ss, ps, set_kpidx (set_typeidx ad chtype) (size msigl)), m); *)
      em <- encode_msgWOTS m;
      skWOTS <- nth witness skWOTSl (size msigl);
      sigWOTS <- [];
      while (size sigWOTS < len){
        skWOTS_ele <- nth witness skWOTS (size sigWOTS);
        em_ele <- BaseW.val (em.[size sigWOTS]);
        sigWOTS_ele <- cf ps (set_chthidx (set_kpidx (set_typeidx ad chtype) (size msigl)) (size sigWOTS)) 0 em_ele (val skWOTS_ele);
        sigWOTS <- rcons sigWOTS sigWOTS_ele;
      }
      
      ap <- cons_ap_trh (list2tree leafl) (insubd (size msigl)) ps (set_typeidx ad trhtype);
      sig <- (insubd (size msigl), DBLL.insubd sigWOTS, ap);
    
      msig <- (m, sig);
      msigl <- rcons msigl msig;
    }
    
    (m', sig') <@ A.forge(pk, msigl);
    
    (* is_valid <@ FL_XMSS_TW_ES.verify(pk, m', sig'); *)
    idx' <- sig'.`1;
    sigWOTS' <- val sig'.`2;
    ap' <- sig'.`3;
    
    (* pkWOTS' <@ WOTS_TW_ES.pkWOTS_from_sigWOTS(m', sigWOTS', ps, set_kpidx (set_typeidx ad chtype) idx'); *)
    em <- encode_msgWOTS m';
    pkWOTS' <- [];
    while (size pkWOTS' < len) {
      sigWOTS_ele' <- nth witness sigWOTS' (size pkWOTS');
      em_ele <- BaseW.val em.[size pkWOTS'];
      pkWOTS_ele' <- cf ps (set_chthidx (set_kpidx (set_typeidx ad chtype) (val idx')) (size pkWOTS')) em_ele (w - 1 - em_ele) (val sigWOTS_ele');
      pkWOTS' <- rcons pkWOTS' pkWOTS_ele';
    }
    
    leaf' <- pkco ps (set_kpidx (set_typeidx ad pkcotype) (val idx')) (flatten (map DigestBlock.val pkWOTS'));
    root' <- val_ap_trh ap' idx' leaf' ps (set_typeidx ad trhtype);
    
    is_valid <- root' = root;
    
    is_fresh <- ! m' \in unzip1 msigl; 
    
    return is_valid /\ is_fresh;
  }
}.

(* 
  EUF_RMA_FLXMSSTWES_NOPRF_LoopSnocSample
  Auxiliary game to go from sampling all WOTS-TW secret key from their domain (at once)
  to individually sampling them
*)
local module EUF_RMA_FLXMSSTWES_NOPRF_LoopSnocSample = {
  proc main() : bool = {
    var ps : pseed;
    var ad : adrs;    
    var root : dgstblock;
    var pkWOTS_ele, pkWOTS_ele' : dgstblock;
    var skWOTS_ele : dgstblock;
    var sigWOTS_ele, sigWOTS_ele' : dgstblock;
    var em_ele : int;
    var pkWOTS, pkWOTS' : dgstblock list;
    var skWOTS : dgstblock list;
    var sigWOTS, sigWOTS' : dgstblock list;
    var pk : pkFLXMSSTW;
    var sk : skFLXMSSTW;
    var m, m' : msgFLXMSSTW;
    var em : emsgWOTS;
    var sig, sig' : sigFLXMSSTW;
    var idx' : index;
    var leaf, leaf' : dgstblock;
    var root' : dgstblock;
    var ap, ap' : apFLXMSSTW;
    var msig : msgFLXMSSTW * sigFLXMSSTW;
    var skWOTSl : dgstblock list list;
    var leafl : dgstblock list;
    var msigl : (msgFLXMSSTW * sigFLXMSSTW) list;
    var is_valid, is_fresh : bool;
    
    ps <$ dpseed;

    ad <@ A.choose();
    
    (* (pk, sk) <@ FL_XMSS_TW_ES.keygen(ss, ps, ad); *)
    skWOTSl <- [];
    leafl <- [];
    while (size leafl < l) {
      skWOTS <@ DListSample.LoopSnoc.sample(len);
      
      (* pkWOTS <@ WOTS_TW_ES.pkWOTS_from_skWOTS(skWOTS, ps, set_kpidx (set_typeidx ad chtype) (size leafl)); *)
      pkWOTS <- [];
      while (size pkWOTS < len) {
        skWOTS_ele <- nth witness skWOTS (size pkWOTS);
        pkWOTS_ele <- cf ps (set_chthidx (set_kpidx (set_typeidx ad chtype) (size leafl)) (size pkWOTS)) 0 (w - 1) (val skWOTS_ele);
        pkWOTS <- rcons pkWOTS pkWOTS_ele;
      }
      
      leaf <- pkco ps (set_kpidx (set_typeidx ad pkcotype) (size leafl)) (flatten (map DigestBlock.val pkWOTS));
      
      skWOTSl <- rcons skWOTSl skWOTS;
      leafl <- rcons leafl leaf;
    }
    
    root <- val_bt_trh (list2tree leafl) ps (set_typeidx ad trhtype) h 0;
    pk <- (root, ps, ad);
    
    msigl <- [];
    while (size msigl < l) {
      m <$ dmsgFLXMSSTW;
      
      (* (sig, sk) <@ FL_XMSS_TW_ES.sign(sk, m); *)
      (* sigWOTS <@ WOTS_TW_ES.sign((ss, ps, set_kpidx (set_typeidx ad chtype) (size msigl)), m); *)
      em <- encode_msgWOTS m;
      skWOTS <- nth witness skWOTSl (size msigl);
      sigWOTS <- [];
      while (size sigWOTS < len){
        skWOTS_ele <- nth witness skWOTS (size sigWOTS);
        em_ele <- BaseW.val (em.[size sigWOTS]);
        sigWOTS_ele <- cf ps (set_chthidx (set_kpidx (set_typeidx ad chtype) (size msigl)) (size sigWOTS)) 0 em_ele (val skWOTS_ele);
        sigWOTS <- rcons sigWOTS sigWOTS_ele;
      }
      
      ap <- cons_ap_trh (list2tree leafl) (insubd (size msigl)) ps (set_typeidx ad trhtype);
      sig <- (insubd (size msigl), DBLL.insubd sigWOTS, ap);
    
      msig <- (m, sig);
      msigl <- rcons msigl msig;
    }
    
    (m', sig') <@ A.forge(pk, msigl);
    
    (* is_valid <@ FL_XMSS_TW_ES.verify(pk, m', sig'); *)
    idx' <- sig'.`1;
    sigWOTS' <- val sig'.`2;
    ap' <- sig'.`3;
    
    (* pkWOTS' <@ WOTS_TW_ES.pkWOTS_from_sigWOTS(m', sigWOTS', ps, set_kpidx (set_typeidx ad chtype) idx'); *)
    em <- encode_msgWOTS m';
    pkWOTS' <- [];
    while (size pkWOTS' < len) {
      sigWOTS_ele' <- nth witness sigWOTS' (size pkWOTS');
      em_ele <- BaseW.val em.[size pkWOTS'];
      pkWOTS_ele' <- cf ps (set_chthidx (set_kpidx (set_typeidx ad chtype) (val idx')) (size pkWOTS')) em_ele (w - 1 - em_ele) (val sigWOTS_ele');
      pkWOTS' <- rcons pkWOTS' pkWOTS_ele';
    }
    
    leaf' <- pkco ps (set_kpidx (set_typeidx ad pkcotype) (val idx')) (flatten (map DigestBlock.val pkWOTS'));
    root' <- val_ap_trh ap' idx' leaf' ps (set_typeidx ad trhtype);
    is_valid <- root' = root;
    
    is_fresh <- ! m' \in unzip1 msigl; 
    
    return is_valid /\ is_fresh;
  }
}.

(* 
  EUF_RMA_FLXMSSTWES_NOPRF_Loop
  Auxiliary game to go from sampling all WOTS-TW secret key from their domain (at once)
  to individually sampling them
*)
local module EUF_RMA_FLXMSSTWES_NOPRF_Loop = {
  proc main() : bool = {
    var ps : pseed;
    var ad : adrs;    
    var root : dgstblock;
    var pkWOTS_ele, pkWOTS_ele' : dgstblock;
    var skWOTS_ele : dgstblock;
    var sigWOTS_ele, sigWOTS_ele' : dgstblock;
    var em_ele : int;
    var pkWOTS, pkWOTS' : dgstblock list;
    var skWOTS : dgstblock list;
    var sigWOTS, sigWOTS' : dgstblock list;
    var pk : pkFLXMSSTW;
    var sk : skFLXMSSTW;
    var m, m' : msgFLXMSSTW;
    var em : emsgWOTS;
    var sig, sig' : sigFLXMSSTW;
    var idx' : index;
    var leaf, leaf' : dgstblock;
    var root' : dgstblock;
    var ap, ap' : apFLXMSSTW;
    var msig : msgFLXMSSTW * sigFLXMSSTW;
    var skWOTSl : dgstblock list list;
    var leafl : dgstblock list;
    var msigl : (msgFLXMSSTW * sigFLXMSSTW) list;
    var is_valid, is_fresh : bool;
    
    ps <$ dpseed;

    ad <@ A.choose();
    
    (* (pk, sk) <@ FL_XMSS_TW_ES.keygen(ss, ps, ad); *)
    skWOTSl <- [];
    leafl <- [];
    while (size leafl < l) {
      skWOTS <- [];
      while (size skWOTS < len) {
        skWOTS_ele <$ ddgstblock;
        skWOTS <- rcons skWOTS skWOTS_ele;
      }
      
      (* pkWOTS <@ WOTS_TW_ES.pkWOTS_from_skWOTS(skWOTS, ps, set_kpidx (set_typeidx ad chtype) (size leafl)); *)
      pkWOTS <- [];
      while (size pkWOTS < len) {
        skWOTS_ele <- nth witness skWOTS (size pkWOTS);
        pkWOTS_ele <- cf ps (set_chthidx (set_kpidx (set_typeidx ad chtype) (size leafl)) (size pkWOTS)) 0 (w - 1) (val skWOTS_ele);
        pkWOTS <- rcons pkWOTS pkWOTS_ele;
      }
      
      leaf <- pkco ps (set_kpidx (set_typeidx ad pkcotype) (size leafl)) (flatten (map DigestBlock.val pkWOTS));
      
      skWOTSl <- rcons skWOTSl skWOTS;
      leafl <- rcons leafl leaf;
    }
    
    root <- val_bt_trh (list2tree leafl) ps (set_typeidx ad trhtype) h 0;
    pk <- (root, ps, ad);
    
    msigl <- [];
    while (size msigl < l) {
      m <$ dmsgFLXMSSTW;
      
      (* (sig, sk) <@ FL_XMSS_TW_ES.sign(sk, m); *)
      (* sigWOTS <@ WOTS_TW_ES.sign((ss, ps, set_kpidx (set_typeidx ad chtype) (size msigl)), m); *)
      em <- encode_msgWOTS m;
      skWOTS <- nth witness skWOTSl (size msigl);
      sigWOTS <- [];
      while (size sigWOTS < len){
        skWOTS_ele <- nth witness skWOTS (size sigWOTS);
        em_ele <- BaseW.val (em.[size sigWOTS]);
        sigWOTS_ele <- cf ps (set_chthidx (set_kpidx (set_typeidx ad chtype) (size msigl)) (size sigWOTS)) 0 em_ele (val skWOTS_ele);
        sigWOTS <- rcons sigWOTS sigWOTS_ele;
      }
      
      ap <- cons_ap_trh (list2tree leafl) (insubd (size msigl)) ps (set_typeidx ad trhtype);
      sig <- (insubd (size msigl), DBLL.insubd sigWOTS, ap);
    
      msig <- (m, sig);
      msigl <- rcons msigl msig;
    }
    
    (m', sig') <@ A.forge(pk, msigl);
    
    (* is_valid <@ FL_XMSS_TW_ES.verify(pk, m', sig'); *)
    idx' <- sig'.`1;
    sigWOTS' <- val sig'.`2;
    ap' <- sig'.`3;
    
    (* pkWOTS' <@ WOTS_TW_ES.pkWOTS_from_sigWOTS(m', sigWOTS', ps, set_kpidx (set_typeidx ad chtype) idx'); *)
    em <- encode_msgWOTS m';
    pkWOTS' <- [];
    while (size pkWOTS' < len) {
      sigWOTS_ele' <- nth witness sigWOTS' (size pkWOTS');
      em_ele <- BaseW.val em.[size pkWOTS'];
      pkWOTS_ele' <- cf ps (set_chthidx (set_kpidx (set_typeidx ad chtype) (val idx')) (size pkWOTS')) em_ele (w - 1 - em_ele) (val sigWOTS_ele');
      pkWOTS' <- rcons pkWOTS' pkWOTS_ele';
    }
    
    leaf' <- pkco ps (set_kpidx (set_typeidx ad pkcotype) (val idx')) (flatten (map DigestBlock.val pkWOTS'));
    root' <- val_ap_trh ap' idx' leaf' ps (set_typeidx ad trhtype);
    is_valid <- root' = root;
    
    is_fresh <- ! m' \in unzip1 msigl; 
    
    return is_valid /\ is_fresh;
  }
}.

local equiv EUF_RMA_FLXMSSTWES_NOPRF_Orig_SampleSample :
  EUF_RMA_FLXMSSTWES_NOPRF(A).main ~ EUF_RMA_FLXMSSTWES_NOPRF_SampleSample.main 
    : ={glob A} ==> ={res}.
proof.
proc.
seq 5 5 : (={glob A, ps, ad, skWOTSl, leafl}); last by sim. 
while(   ={ps, ad, skWOTSl, leafl} 
      /\ size skWOTSl{1} = size leafl{1}
      /\ 0 <= size leafl{1} <= l).  
+ seq 1 1 : (#pre /\ ={skWOTS}).
  - by inline{2} 1; wp; rnd; wp; skip.
  wp. 
  while(={ps, ad, skWOTS, pkWOTS, leafl} /\ 0 <= size pkWOTS{1} <= len). 
  - wp; skip => />; smt(size_rcons).
  wp; skip => />; smt(ge2_len size_rcons).
by wp; call(: true); rnd; skip => />; smt(ge2_l).
qed.

local equiv EUF_RMA_FLXMSSTWES_NOPRF_SampleSample_LoopSnocSample :
  EUF_RMA_FLXMSSTWES_NOPRF_SampleSample.main ~ EUF_RMA_FLXMSSTWES_NOPRF_LoopSnocSample.main 
    : ={glob A} ==> ={res}.
proof.
proc.
seq 5 5 : (={glob A, ps, ad, skWOTSl, leafl}); last by sim. 
while(   ={ps, ad, skWOTSl, leafl} 
      /\ size skWOTSl{1} = size leafl{1}
      /\ 0 <= size leafl{1} <= l).  
+ seq 1 1 : (#pre /\ ={skWOTS}).
  by call Sample_LoopSnoc_eq; skip.
  wp. 
  while(={ps, ad, skWOTS, pkWOTS, leafl} /\ 0 <= size pkWOTS{1} <= len). 
  - wp; skip => />; smt(size_rcons).
  wp; skip => />; smt(ge2_len size_rcons).
by wp; call(: true); rnd; skip => />; smt(ge2_l).
qed.

local equiv EUF_RMA_FLXMSSTWES_NOPRF_LoopSnocSample_Loop :
  EUF_RMA_FLXMSSTWES_NOPRF_LoopSnocSample.main ~ EUF_RMA_FLXMSSTWES_NOPRF_Loop.main 
    : ={glob A} ==> ={res}.
proof.
proc.
seq 5 5 : (={glob A, ps, ad, skWOTSl, leafl}); last by sim. 
while(   ={ps, ad, skWOTSl, leafl} 
      /\ size skWOTSl{1} = size leafl{1}
      /\ 0 <= size leafl{1} <= l).  
+ seq 1 2 : (#pre /\ ={skWOTS}).
  inline{1} 1; wp.
  while(   n{1} = len
        /\ l{1} = skWOTS{2}
        /\ i{1} = size skWOTS{2}
        /\ 0 <= size skWOTS{2} <= len).
  - by wp; rnd; skip => />; smt(size_rcons cats1). 
  by wp; skip => />; smt(ge2_len).
  wp. 
  while(={ps, ad, skWOTS, pkWOTS, leafl} /\ 0 <= size pkWOTS{1} <= len). 
  - wp; skip => />; smt(size_rcons).
  wp; skip => />; smt(ge2_len size_rcons).
by wp; call(: true); rnd; skip => />; smt(ge2_l).
qed.

local equiv EUF_RMA_FLXMSSTWES_NOPRF_Orig_Loop :
  EUF_RMA_FLXMSSTWES_NOPRF(A).main ~ EUF_RMA_FLXMSSTWES_NOPRF_Loop.main 
    : ={glob A} ==> ={res}.
proof.
transitivity EUF_RMA_FLXMSSTWES_NOPRF_SampleSample.main 
             (={glob A} ==> ={res})
             (={glob A} ==> ={res}) => // />.
+ by move=> &2; exists (glob A){2}.
+ by apply EUF_RMA_FLXMSSTWES_NOPRF_Orig_SampleSample.
transitivity EUF_RMA_FLXMSSTWES_NOPRF_LoopSnocSample.main 
             (={glob A} ==> ={res})
             (={glob A} ==> ={res}) => // />.
+ by move=> &2; exists (glob A){2}.
+ by apply EUF_RMA_FLXMSSTWES_NOPRF_SampleSample_LoopSnocSample.
by apply EUF_RMA_FLXMSSTWES_NOPRF_LoopSnocSample_Loop.
qed.

(* 
  EUF_RMA_FLXMSSTWES_NOPRF -- Variant with conditions
  Identical to EUF_RMA_FLXMSSTWES_NOPRF, but keeps track of certain conditions in module variables for use in proof
*)
local module EUF_RMA_FLXMSSTWES_NOPRF_Conditions = {
  var valid_WOTSTWES : bool
  var coll_pkco : bool
  
  proc main() : bool = {
    var ps : pseed;
    var ad : adrs;    
    var root : dgstblock;
    var pkWOTS_ele, pkWOTS_ele', skWOTS_ele, sigWOTS_ele, sigWOTS_ele' : dgstblock;
    var em_ele : int;
    var pkWOTS, pkWOTS' : dgstblock list;
    var skWOTS : dgstblock list;
    var sigWOTS, sigWOTS' : dgstblock list;
    var pk : pkFLXMSSTW;
    var sk : skFLXMSSTW;
    var m, m' : msgFLXMSSTW;
    var em : emsgWOTS;
    var sig, sig' : sigFLXMSSTW;
    var idx' : index;
    var leaf, leaf' : dgstblock;
    var root' : dgstblock;
    var ap, ap' : apFLXMSSTW;
    var msig : msgFLXMSSTW * sigFLXMSSTW;
    var pkWOTSl : dgstblock list list;
    var skWOTSl : dgstblock list list;
    var leafl : dgstblock list;
    var msigl : (msgFLXMSSTW * sigFLXMSSTW) list;
    var is_valid, is_fresh : bool;
    
    ps <$ dpseed;

    ad <@ A.choose();
    
    (* (pk, sk) <@ FL_XMSS_TW_ES.keygen(ss, ps, ad); *)
    skWOTSl <- [];
    pkWOTSl <- [];
    leafl <- [];
    while (size leafl < l) {
      skWOTS <$ ddgstblockl;
    
      (* pkWOTS <@ WOTS_TW_ES.pkWOTS_from_skWOTS(skWOTS, ps, set_kpidx (set_typeidx ad chtype) (size leafl)); *)
      pkWOTS <- [];
      while (size pkWOTS < len) {
        skWOTS_ele <- nth witness skWOTS (size pkWOTS);
        pkWOTS_ele <- cf ps (set_chthidx (set_kpidx (set_typeidx ad chtype) (size leafl)) (size pkWOTS)) 0 (w - 1) (val skWOTS_ele);
        pkWOTS <- rcons pkWOTS pkWOTS_ele;
      }
      
      leaf <- pkco ps (set_kpidx (set_typeidx ad pkcotype) (size leafl)) (flatten (map DigestBlock.val pkWOTS));
      
      skWOTSl <- rcons skWOTSl skWOTS;
      pkWOTSl <- rcons pkWOTSl pkWOTS;
      leafl <- rcons leafl leaf;
    }
    
    root <- val_bt_trh (list2tree leafl) ps (set_typeidx ad trhtype) h 0;
    pk <- (root, ps, ad);
    
    msigl <- [];
    while (size msigl < l) {
      m <$ dmsgFLXMSSTW;
      
      (* (sig, sk) <@ FL_XMSS_TW_ES.sign(sk, m); *)
      (* sigWOTS <@ WOTS_TW_ES.sign((ss, ps, set_kpidx (set_typeidx ad chtype) (size msigl)), m); *)
      em <- encode_msgWOTS m;
      skWOTS <- nth witness skWOTSl (size msigl);
      sigWOTS <- [];
      while (size sigWOTS < len){
        skWOTS_ele <- nth witness skWOTS (size sigWOTS);
        em_ele <- BaseW.val (em.[size sigWOTS]);
        sigWOTS_ele <- cf ps (set_chthidx (set_kpidx (set_typeidx ad chtype) (size msigl)) (size sigWOTS)) 0 em_ele (val skWOTS_ele);
        sigWOTS <- rcons sigWOTS sigWOTS_ele;
      }
      
      ap <- cons_ap_trh (list2tree leafl) (insubd (size msigl)) ps (set_typeidx ad trhtype);
      sig <- (insubd (size msigl), DBLL.insubd sigWOTS, ap);
    
      msig <- (m, sig);
      msigl <- rcons msigl msig;
    }
    
    (m', sig') <@ A.forge(pk, msigl);
    
    (* is_valid <@ FL_XMSS_TW_ES.verify(pk, m', sig'); *)
    idx' <- sig'.`1;
    sigWOTS' <- val sig'.`2;
    ap' <- sig'.`3;
    
    (* pkWOTS' <@ WOTS_TW_ES.pkWOTS_from_sigWOTS(m', sigWOTS', ps, set_kpidx (set_typeidx ad chtype) idx'); *)
    em <- encode_msgWOTS m';
    pkWOTS' <- [];
    while (size pkWOTS' < len) {
      sigWOTS_ele' <- nth witness sigWOTS' (size pkWOTS');
      em_ele <- BaseW.val em.[size pkWOTS'];
      pkWOTS_ele' <- cf ps (set_chthidx (set_kpidx (set_typeidx ad chtype) (val idx')) (size pkWOTS')) em_ele (w - 1 - em_ele) (val sigWOTS_ele');
      pkWOTS' <- rcons pkWOTS' pkWOTS_ele';
    }
    
    leaf' <- pkco ps (set_kpidx (set_typeidx ad pkcotype) (val idx')) (flatten (map DigestBlock.val pkWOTS'));
    root' <- val_ap_trh ap' idx' leaf' ps (set_typeidx ad trhtype);
    is_valid <- root' = root;
    
    is_fresh <- ! m' \in unzip1 msigl; 
    
    (* Checks for conditions *)
    pkWOTS <- nth witness pkWOTSl (val idx');
    
    valid_WOTSTWES <- pkWOTS' = pkWOTS;
    
    coll_pkco <-    flatten (map DigestBlock.val pkWOTS') <> flatten (map DigestBlock.val pkWOTS) 
                 /\ pkco ps (set_kpidx (set_typeidx ad pkcotype) (val idx')) (flatten (map DigestBlock.val pkWOTS')) 
                    = 
                    pkco ps (set_kpidx (set_typeidx ad pkcotype) (val idx')) (flatten (map DigestBlock.val pkWOTS));
                    
    return is_valid /\ is_fresh;
  }
}.

(* 
  EUF_RMA_FLXMSSTWES_NOPRF -- Variant with conditions and separated sampling
  Identical to EUF_RMA_FLXMSSTWES_NOPRF, but keeps track of certain conditions in module variables for use in proofs
  as well as separates sampling of messages and secret keys to facilitate the proving process in certain cases
*)
local module EUF_RMA_FLXMSSTWES_NOPRF_Conditions_SSampling = {
  var valid_WOTSTWES : bool
  var coll_pkco : bool
  
  proc main() : bool = {
    var ps : pseed;
    var ad : adrs;    
    var root : dgstblock;
    var pkWOTS_ele, pkWOTS_ele', skWOTS_ele, sigWOTS_ele, sigWOTS_ele' : dgstblock;
    var em_ele : int;
    var pkWOTS, pkWOTS' : dgstblock list;
    var skWOTS : dgstblock list;
    var sigWOTS, sigWOTS' : dgstblock list;
    var pk : pkFLXMSSTW;
    var sk : skFLXMSSTW;
    var m, m' : msgFLXMSSTW;
    var em : emsgWOTS;
    var sig, sig' : sigFLXMSSTW;
    var idx' : index;
    var leaf, leaf' : dgstblock;
    var root' : dgstblock;
    var ap, ap' : apFLXMSSTW;
    var msig : msgFLXMSSTW * sigFLXMSSTW;
    var pkWOTSl : dgstblock list list;
    var skWOTSl : dgstblock list list;
    var leafl : dgstblock list;
    var ml : msgFLXMSSTW list;
    var msigl : (msgFLXMSSTW * sigFLXMSSTW) list;
    var is_valid, is_fresh : bool;
    var i : int;
    
    ps <$ dpseed;

    ad <@ A.choose();
    
    skWOTSl <- [];
    i <- 0;
    while (i < l) {
      skWOTS <$ ddgstblockl;
      skWOTSl <- rcons skWOTSl skWOTS;
      i <- i + 1;
    }
    
    (* (pk, sk) <@ FL_XMSS_TW_ES.keygen(ss, ps, ad); *)
    pkWOTSl <- [];
    leafl <- [];
    while (size leafl < l) {
      skWOTS <- nth witness skWOTSl (size leafl);
    
      (* pkWOTS <@ WOTS_TW_ES.pkWOTS_from_skWOTS(skWOTS, ps, set_kpidx (set_typeidx ad chtype) (size leafl)); *)
      pkWOTS <- [];
      while (size pkWOTS < len) {
        skWOTS_ele <- nth witness skWOTS (size pkWOTS);
        pkWOTS_ele <- cf ps (set_chthidx (set_kpidx (set_typeidx ad chtype) (size leafl)) (size pkWOTS)) 0 (w - 1) (val skWOTS_ele);
        pkWOTS <- rcons pkWOTS pkWOTS_ele;
      }
      
      leaf <- pkco ps (set_kpidx (set_typeidx ad pkcotype) (size leafl)) (flatten (map DigestBlock.val pkWOTS));
      
      pkWOTSl <- rcons pkWOTSl pkWOTS;
      leafl <- rcons leafl leaf;
    }
    
    root <- val_bt_trh (list2tree leafl) ps (set_typeidx ad trhtype) h 0;
    pk <- (root, ps, ad);
    
    ml <- [];
    i <- 0;
    while (i < l) {
      m <$ dmsgFLXMSSTW;
      ml <- rcons ml m;
      i <- i + 1;
    }
    
    msigl <- [];
    while (size msigl < l) {
      m <- nth witness ml (size msigl);
      
      (* (sig, sk) <@ FL_XMSS_TW_ES.sign(sk, m); *)
      (* sigWOTS <@ WOTS_TW_ES.sign((ss, ps, set_kpidx (set_typeidx ad chtype) (size msigl)), m); *)
      em <- encode_msgWOTS m;
      skWOTS <- nth witness skWOTSl (size msigl);
      sigWOTS <- [];
      while (size sigWOTS < len){
        skWOTS_ele <- nth witness skWOTS (size sigWOTS);
        em_ele <- BaseW.val (em.[size sigWOTS]);
        sigWOTS_ele <- cf ps (set_chthidx (set_kpidx (set_typeidx ad chtype) (size msigl)) (size sigWOTS)) 0 em_ele (val skWOTS_ele);
        sigWOTS <- rcons sigWOTS sigWOTS_ele;
      }
      
      ap <- cons_ap_trh (list2tree leafl) (insubd (size msigl)) ps (set_typeidx ad trhtype);
      sig <- (insubd (size msigl), DBLL.insubd sigWOTS, ap);
    
      msig <- (m, sig);
      msigl <- rcons msigl msig;
    }
    
    (m', sig') <@ A.forge(pk, msigl);
    
    (* is_valid <@ FL_XMSS_TW_ES.verify(pk, m', sig'); *)
    idx' <- sig'.`1;
    sigWOTS' <- val sig'.`2;
    ap' <- sig'.`3;
    
    (* pkWOTS' <@ WOTS_TW_ES.pkWOTS_from_sigWOTS(m', sigWOTS', ps, set_kpidx (set_typeidx ad chtype) idx'); *)
    em <- encode_msgWOTS m';
    pkWOTS' <- [];
    while (size pkWOTS' < len) {
      sigWOTS_ele' <- nth witness sigWOTS' (size pkWOTS');
      em_ele <- BaseW.val em.[size pkWOTS'];
      pkWOTS_ele' <- cf ps (set_chthidx (set_kpidx (set_typeidx ad chtype) (val idx')) (size pkWOTS')) em_ele (w - 1 - em_ele) (val sigWOTS_ele');
      pkWOTS' <- rcons pkWOTS' pkWOTS_ele';
    }
    
    leaf' <- pkco ps (set_kpidx (set_typeidx ad pkcotype) (val idx')) (flatten (map DigestBlock.val pkWOTS'));
    
    root' <- val_ap_trh ap' idx' leaf' ps (set_typeidx ad trhtype);
    
    is_valid <- root' = root;
    
    is_fresh <- ! m' \in unzip1 msigl; 
    
    (* Checks for conditions *)
    pkWOTS <- nth witness pkWOTSl (val idx');
    
    valid_WOTSTWES <- pkWOTS' = pkWOTS;
    
    coll_pkco <-    flatten (map DigestBlock.val pkWOTS') <> flatten (map DigestBlock.val pkWOTS) 
                 /\ pkco ps (set_kpidx (set_typeidx ad pkcotype) (val idx')) (flatten (map DigestBlock.val pkWOTS')) 
                    = 
                    pkco ps (set_kpidx (set_typeidx ad pkcotype) (val idx')) (flatten (map DigestBlock.val pkWOTS));
                    
    return is_valid /\ is_fresh;
  }
}.

(* 
  Equivalence between EUF_RMA_FLXMSSTWES_NOPRF with conditions and EUF_RMA_FLXMSSTWES_NOPRF with
  conditions and separated sampling of messages and secret keys; includes equality on
  the condition concerning the validity of the WOTS-TW forgery. 
*)
local equiv EUF_RMA_FLXMSSTWES_NOPRF_Conditions_SSampling_Validity :
  EUF_RMA_FLXMSSTWES_NOPRF_Conditions.main ~ EUF_RMA_FLXMSSTWES_NOPRF_Conditions_SSampling.main : 
    ={glob A} 
    ==> 
    ={res} /\ EUF_RMA_FLXMSSTWES_NOPRF_Conditions.valid_WOTSTWES{1} = EUF_RMA_FLXMSSTWES_NOPRF_Conditions_SSampling.valid_WOTSTWES{2}.
proof.
proc => //=.
seq 6 8 : (   ={glob A, ps, ad, skWOTSl, pkWOTSl, leafl}).
+ while{2} (   size pkWOTSl{2} = size leafl{2}
            /\ 0 <= size leafl{2} <= l
            /\ all ((=) len \o size) (pkWOTSl{2})
            /\ (forall (j n : int), 0 <= j < size pkWOTSl{2} => 0 <= n < len =>
                  nth witness (nth witness pkWOTSl{2} j) n
                  =
                  cf ps{2} (set_chthidx (set_kpidx (set_typeidx ad{2} chtype) j) n) 0 (w - 1) (val (nth witness (nth witness skWOTSl{2} j) n)))
            /\ (forall (j : int), 0 <= j < size leafl{2} =>
                  nth witness leafl{2} j
                  =
                  pkco ps{2} (set_kpidx (set_typeidx ad{2} pkcotype) j) (flatten (map DigestBlock.val (nth witness pkWOTSl{2} j)))))
           (l - size leafl{2}).
  - move=> _ z.
    wp.
    while (   skWOTS = nth witness skWOTSl (size leafl)
           /\ 0 <= size leafl < l
           /\ 0 <= size pkWOTS <= len
           /\ (forall (n : int), 0 <= n < size pkWOTS =>
                 nth witness pkWOTS n
                 =
                 cf ps (set_chthidx (set_kpidx (set_typeidx ad chtype) (size leafl)) n) 0 (w - 1) (val (nth witness skWOTS n)))) 
          (len - size pkWOTS).
    * move=> zp.
      wp; skip => /> &2 ge0_szlfl ltl_szlfl ge0_szpkw _ valpkw ltlen_szpkw.
      rewrite andbC !andbA; split => [| n ge0_n]; first by smt(size_rcons).
      rewrite size_rcons=> ltszpkw1_n; rewrite nth_rcons.
      case (n < size pkWOTS{2}) => [/# | /lezNgt geszpkw_n].
      by rewrite (: n = size pkWOTS{2}) 1:/#.
    wp; skip => /> &m eqszpkwl_lfl ge0_szlfl _ alen_pkwl pkwl_def lfl_def ltl_szlfl.
    split => [| pkw]; first by smt(ge2_len).
    split => [/# | /lezNgt gelen_szpkw _ lelen_szpkw pkw_def].
    rewrite -!andbA 2!andbA; split; first by smt(size_rcons).
    split; first by rewrite -cats1 all_cat /= alen_pkwl /#. 
    by split; 2: split; smt(size_rcons nth_rcons).
  wp.
  while (   ={skWOTSl}
         /\ size leafl{1} = i{2}
         /\ size pkWOTSl{1} = size leafl{1}
         /\ size skWOTSl{1} = size leafl{1}
         /\ 0 <= size leafl{1} <= l
         /\ all ((=) len \o size) (pkWOTSl{1})
         /\ (forall (j n : int), 0 <= j < size pkWOTSl{1} => 0 <= n < len =>
               nth witness (nth witness pkWOTSl{1} j) n
               =
               cf ps{1} (set_chthidx (set_kpidx (set_typeidx ad{1} chtype) j) n) 0 (w - 1) (val (nth witness (nth witness skWOTSl{1} j) n)))
         /\ (forall (j : int), 0 <= j < size leafl{1} =>
               nth witness leafl{1} j
               =
               pkco ps{1} (set_kpidx (set_typeidx ad{1} pkcotype) j) (flatten (map DigestBlock.val (nth witness pkWOTSl{1} j))))).
  - wp.
    while{1} (   0 <= size leafl{1} < l
              /\ 0 <= size pkWOTS{1} <= len
              /\ (forall (n : int), 0 <= n < size pkWOTS{1} =>
                   nth witness pkWOTS{1} n
                   =
                   cf ps{1} (set_chthidx (set_kpidx (set_typeidx ad{1} chtype) (size leafl{1})) n) 0 (w - 1) (val (nth witness skWOTS{1} n)))) 
          (len - size pkWOTS{1}).
    * move=> _ z.
      wp; skip => /> &1 ge0_szlfl ltl_szlfl ge0_szpkw _ valpkw ltlen_szpkw.
      rewrite andbC !andbA; split => [| n ge0_n]; first by smt(size_rcons).
      rewrite size_rcons=> ltszpkw1_n; rewrite nth_rcons.
      case (n < size pkWOTS{1}) => [/# | /lezNgt geszpkw_n].
      by rewrite (: n = size pkWOTS{1}) 1:/#.
    wp; rnd; skip => /> &1 &2 eqszpkwl_szlfl eqszskwl_szlfl ge0_szlfl _ alen_pkwl pkwl_def lfl_def ltl_szlfl skwl skwlin.
    split => [| pkw]; first by smt(ge2_len).
    split => [/# | /lezNgt gelen_szpkw _ lelen_szpkw pkw_def].
    rewrite -!andbA 4!andbA; split; first by smt(size_rcons).
    split; first by rewrite -cats1 all_cat /= alen_pkwl /#.
    by split; 2: split; smt(size_rcons nth_rcons).
  wp; call(: true); rnd; skip => /> ps psin ad.
  split => [| lfl pkwl skwl /lezNgt gel_szlfl _ eqszpwl_szlfl eqszskwl_szlfl _ lel_szlfl alen_pkwl pkwl_def lfl_def]; first by smt(ge2_l).
  split => [| lflp pkwlp]; first by smt(ge2_l).
  split => [/# | /lezNgt gel_szlflp eqszlflp_szpkwlp _ lel_szlflp alen_pkwlp pkwlp_def lflp_def].
  rewrite -andaE; split => [| eqpkwl_pkwlp].
  - apply (eq_from_nth witness) => [/# | j rng_j].
    apply (eq_from_nth witness) => [| n].
    * move/(all_nthP _ _ witness): alen_pkwl alen_pkwlp => /(_ j rng_j) @/(\o) <-.
      rewrite (: size pkwl = size pkwlp) 1:/# in rng_j.
      by move/(all_nthP _ _ witness) => /(_ j rng_j) @/(\o) <-. 
    rewrite (: size (nth witness pkwl j) = len) => [| rng_n]; last by apply DigestBlock.val_inj => /#.
    by move/(all_nthP _ _ witness): alen_pkwl => /(_ j rng_j) @/(\o) <-.
  apply (eq_from_nth witness) => [/# | j ^ /lfl_def ->].
  rewrite (: size lfl = size lflp) 1:/# => /lflp_def ->.
  by rewrite eqpkwl_pkwlp.
seq 4 7 : (#pre /\ ={root, pk, msigl}).
+ while{2} (   size ml{2} = l
            /\ 0 <= size msigl{2} <= l
            /\ (forall (j : int), 0 <= j < size msigl{2} =>
                  (nth witness msigl{2} j).`1
                  =
                  nth witness ml{2} j)
            /\ (forall (j : int), 0 <= j < size msigl{2} =>
                  val (nth witness msigl{2} j).`2.`1 = j)
            /\ (forall (j n : int), 0 <= j < size msigl{2} => 0 <= n < len =>
                  nth witness (val (nth witness msigl{2} j).`2.`2) n
                  =
                  cf ps{2} (set_chthidx (set_kpidx (set_typeidx ad{2} chtype) j) n) 0 (BaseW.val (encode_msgWOTS (nth witness ml{2} j)).[n]) (val (nth witness (nth witness skWOTSl{2} j) n)))
            /\ (forall (j : int), 0 <= j < size msigl{2} =>
                  (nth witness msigl{2} j).`2.`3
                  =
                  cons_ap_trh (list2tree leafl{2}) (insubd j) ps{2} (set_typeidx ad{2} trhtype)))
           (l - size msigl{2}).
  - move=> _ z.
    wp.
    while (   0 <= size msigl < l
           /\ 0 <= size sigWOTS <= len
           /\ size ml = l
           /\ (forall (n : int), 0 <= n < size sigWOTS =>
                 nth witness sigWOTS n
                 =
                 cf ps (set_chthidx (set_kpidx (set_typeidx ad chtype) (size msigl)) n) 0 (BaseW.val em.[n]) (val (nth witness skWOTS n))))
          (len - size sigWOTS).
    * move=> zp.
      wp; skip => /> &1 ge0_szmsigl ltl_szmsigl ge0_szsigw eql_szml _ valsigw ltlen_szpkw.
      rewrite andbC !andbA; split => [| n ge0_n]; first by smt(size_rcons).
      rewrite size_rcons=> ltszpkw1_n; rewrite nth_rcons.
      case (n < size sigWOTS{1}) => [/# | /lezNgt geszpkw_n].
      by rewrite (: n = size sigWOTS{1}) 1:/#.
    wp; skip => /> &1 ? ? ? ? ? msigl_def ? ?; split; 1: smt(ge2_len ge2_l nth_rcons size_rcons).
    move=> sigw; split => [/# | *].
    by do ? split => *; smt(ge2_len ge2_l nth_rcons size_rcons DBLL.insubdK Index.insubdK).
  wp.
  while (   ={ps, ad, skWOTSl, leafl}
         /\ size msigl{1} = i{2}
         /\ i{2} = size ml{2}
         /\ 0 <= size msigl{1} <= l
         /\ (forall (j : int), 0 <= j < size msigl{1} =>
               (nth witness msigl{1} j).`1
               =
               nth witness ml{2} j)
         /\ (forall (j : int), 0 <= j < size msigl{1} =>
                val (nth witness msigl{1} j).`2.`1 = j)
         /\ (forall (j n : int), 0 <= j < size msigl{1} => 0 <= n < len =>
                nth witness (val (nth witness msigl{1} j).`2.`2) n
                =
                cf ps{2} (set_chthidx (set_kpidx (set_typeidx ad{2} chtype) j) n) 0 (BaseW.val (encode_msgWOTS (nth witness ml{2} j)).[n]) (val (nth witness (nth witness skWOTSl{2} j) n)))
            /\ (forall (j : int), 0 <= j < size msigl{1} =>
                  (nth witness msigl{1} j).`2.`3
                  =
                  cons_ap_trh (list2tree leafl{2}) (insubd j) ps{2} (set_typeidx ad{2} trhtype))).
  - wp.
    while{1} (   0 <= size msigl{1} < l
              /\ 0 <= size sigWOTS{1} <= len
              /\ forall (n : int), 0 <= n < size sigWOTS{1} =>
                    nth witness sigWOTS{1} n
                    =
                    cf ps{1} (set_chthidx (set_kpidx (set_typeidx ad{1} chtype) (size msigl{1})) n) 0 (BaseW.val em{1}.[n]) (val (nth witness skWOTS{1} n)))
             (len - size sigWOTS{1}).
    * move=> _ z.
      wp; skip => /> &1 ge0_szmsigl ltl_szmsigl ge0_szsigw _ valsigw ltlen_szpkw.
      rewrite andbC !andbA; split => [| n ge0_n]; first by smt(size_rcons).
      rewrite size_rcons=> ltszpkw1_n; rewrite nth_rcons.
      case (n < size sigWOTS{1}) => [/# | /lezNgt geszpkw_n].
      by rewrite (: n = size sigWOTS{1}) 1:/#.    
    wp; rnd; skip => /> &1 &2 eqszmsigl_ml ge0_szmsigl _ msigl1_def msigl21_def msigl22_def msigl23_def ltl_szmisgl ml mlin.
    split => [| sigwl]; first by smt(ge2_len).
    split => [/# | /lezNgt gelen_szsigwl _ lelen_szsigwl sigwl_def].
    rewrite -!andbA 3!andbA; split; first by smt(size_rcons).
    do 3! (split; first by smt(nth_rcons size_rcons DBLL.insubdK Index.insubdK Index.valKd)).
    by split; smt(nth_rcons size_rcons DBLL.insubdK Index.insubdK Index.valKd).
  wp; skip => /> &2.
  split => [| msigl ml /lezNgt gel_szmsigl _ eqszmsigl_ml _ lel_szmsigl msigl1_def msigl21_def msigl22_def msigl23_def]; first by smt(ge2_l).
  split => [| msiglp]; first by smt(ge2_l).
  split => [/# | /lezNgt gel_szmsiglp eql_szml _ lel_szmsiglp msiglp1_def msiglp21_def msiglp22_def msiglp23_def].
  apply (eq_from_nth witness) => [/# | j rng_j].
  have /#:
    (nth witness msigl j).`1 = (nth witness msiglp j).`1
    /\
    (nth witness msigl j).`2.`1 = (nth witness msiglp j).`2.`1
    /\
    (nth witness msigl j).`2.`2 = (nth witness msiglp j).`2.`2
    /\
    (nth witness msigl j).`2.`3 = (nth witness msiglp j).`2.`3.
  split => [/# |]; last split; first by apply Index.val_inj => /#.
  split.
  - apply DBLL.val_inj; apply (eq_from_nth witness); first by rewrite 2!DBLL.valP.
    rewrite valP => n rng_n.
    apply DigestBlock.val_inj; move/msigl22_def: (rng_j) => /(_ n rng_n) ->.
    rewrite (: size msigl = size msiglp) 1:/# in rng_j.
    by move/msiglp22_def: (rng_j) => /(_ n rng_n) ->.
  rewrite (msigl23_def j rng_j). 
  rewrite (: size msigl = size msiglp) 1:/# in rng_j.
  by rewrite (msiglp23_def j rng_j).
by sim : (   ={is_valid, is_fresh} 
          /\ EUF_RMA_FLXMSSTWES_NOPRF_Conditions.valid_WOTSTWES{1} 
             = 
             EUF_RMA_FLXMSSTWES_NOPRF_Conditions_SSampling.valid_WOTSTWES{2}).
qed.

(* 
  EUF_RMA_FLXMSSTWES_NOPRF -- Variant with conditions and samplings/computations in the same while loop 
  Identical to EUF_RMA_FLXMSSTWES_NOPRF, but keeps track of certain conditions in module variables for use in proof
  as well as combines sampling and computations to facilitate the proving process in certain cases
*)
local module EUF_RMA_FLXMSSTWES_NOPRF_Conditions_Mono = {
  var valid_WOTSTWES : bool
  var coll_pkco : bool
  
  proc main() : bool = {
    var ps : pseed;
    var ad : adrs;    
    var root : dgstblock;
    var pkWOTS_ele, pkWOTS_ele', skWOTS_ele, sigWOTS_ele, sigWOTS_ele' : dgstblock;
    var em_ele : int;
    var pkWOTS, pkWOTS' : dgstblock list;
    var skWOTS : dgstblock list;
    var sigWOTS, sigWOTS' : dgstblock list;
    var pk : pkFLXMSSTW;
    var sk : skFLXMSSTW;
    var m, m' : msgFLXMSSTW;
    var em : emsgWOTS;
    var sig, sig' : sigFLXMSSTW;
    var idx' : index;
    var leaf, leaf' : dgstblock;
    var root' : dgstblock;
    var ap, ap' : apFLXMSSTW;
    var msig : msgFLXMSSTW * sigFLXMSSTW;
    var pkWOTSl : dgstblock list list;
    var sigWOTSl : dgstblock list list;
    var leafl : dgstblock list;
    var ml : msgFLXMSSTW list;
    var msigl : (msgFLXMSSTW * sigFLXMSSTW) list;
    var is_valid, is_fresh : bool;
    var i : int;
    
    ps <$ dpseed;

    ad <@ A.choose();
    
    (* (pk, sk) <@ FL_XMSS_TW_ES.keygen(ss, ps, ad); *)
    ml <- [];
    pkWOTSl <- [];
    sigWOTSl <- [];
    while (size ml < l) {
      m <$ dmsgFLXMSSTW;
      skWOTS <$ ddgstblockl;
    
      (* pkWOTS <@ WOTS_TW_ES.pkWOTS_from_skWOTS(skWOTS, ps, set_kpidx (set_typeidx ad chtype) (size leafl)); *)
      pkWOTS <- [];
      while (size pkWOTS < len) {
        skWOTS_ele <- nth witness skWOTS (size pkWOTS);
        pkWOTS_ele <- cf ps (set_chthidx (set_kpidx (set_typeidx ad chtype) (size ml)) (size pkWOTS)) 0 (w - 1) (val skWOTS_ele);
        pkWOTS <- rcons pkWOTS pkWOTS_ele;
      }
      
      em <- encode_msgWOTS m;
      sigWOTS <- [];
      while (size sigWOTS < len) {
        skWOTS_ele <- nth witness skWOTS (size sigWOTS);
        em_ele <- BaseW.val em.[size sigWOTS];
        sigWOTS_ele <- cf ps (set_chthidx (set_kpidx (set_typeidx ad chtype) (size ml)) (size sigWOTS)) 0 em_ele (val skWOTS_ele);
        sigWOTS <- rcons sigWOTS sigWOTS_ele;
      }
      
      ml <- rcons ml m;
      pkWOTSl <- rcons pkWOTSl pkWOTS;
      sigWOTSl <- rcons sigWOTSl sigWOTS; 
    }
    
    
    leafl <- [];
    while (size leafl < l) {
      pkWOTS <- nth witness pkWOTSl (size leafl);
      
      leaf <- pkco ps (set_kpidx (set_typeidx ad pkcotype) (size leafl)) (flatten (map DigestBlock.val pkWOTS));
      leafl <- rcons leafl leaf;
    }
    
    root <- val_bt_trh (list2tree leafl) ps (set_typeidx ad trhtype) h 0;
    pk <- (root, ps, ad);
    
    msigl <- [];
    while (size msigl < l) {
      m <- nth witness ml (size msigl);
      sigWOTS <- nth witness sigWOTSl (size msigl);
            
      ap <- cons_ap_trh (list2tree leafl) (insubd (size msigl)) ps (set_typeidx ad trhtype);
      sig <- (insubd (size msigl), DBLL.insubd sigWOTS, ap);
    
      msig <- (m, sig);
      msigl <- rcons msigl msig;
    }
    
    (m', sig') <@ A.forge(pk, msigl);
    
    (* is_valid <@ FL_XMSS_TW_ES.verify(pk, m', sig'); *)
    idx' <- sig'.`1;
    sigWOTS' <- val sig'.`2;
    ap' <- sig'.`3;
    
    (* pkWOTS' <@ WOTS_TW_ES.pkWOTS_from_sigWOTS(m', sigWOTS', ps, set_kpidx (set_typeidx ad chtype) idx'); *)
    em <- encode_msgWOTS m';
    pkWOTS' <- [];
    while (size pkWOTS' < len) {
      sigWOTS_ele' <- nth witness sigWOTS' (size pkWOTS');
      em_ele <- BaseW.val em.[size pkWOTS'];
      pkWOTS_ele' <- cf ps (set_chthidx (set_kpidx (set_typeidx ad chtype) (val idx')) (size pkWOTS')) em_ele (w - 1 - em_ele) (val sigWOTS_ele');
      pkWOTS' <- rcons pkWOTS' pkWOTS_ele';
    }
    
    leaf' <- pkco ps (set_kpidx (set_typeidx ad pkcotype) (val idx')) (flatten (map DigestBlock.val pkWOTS'));
    root' <- val_ap_trh ap' idx' leaf' ps (set_typeidx ad trhtype);
    is_valid <- root' = root;
    
    is_fresh <- ! m' \in unzip1 msigl; 
    
    (* Checks for conditions *)
    pkWOTS <- nth witness pkWOTSl (val idx');
    
    valid_WOTSTWES <- pkWOTS' = pkWOTS;
    
    coll_pkco <-    flatten (map DigestBlock.val pkWOTS') <> flatten (map DigestBlock.val pkWOTS') 
                 /\ pkco ps (set_kpidx (set_typeidx ad pkcotype) (val idx')) (flatten (map DigestBlock.val pkWOTS')) 
                    = 
                    pkco ps (set_kpidx (set_typeidx ad pkcotype) (val idx')) (flatten (map DigestBlock.val pkWOTS'));
                    
    return is_valid /\ is_fresh;
  }
}.

(* 
  Equivalence between EUF_RMA_FLXMSSTWES_NOPRF with conditions and separated sampling 
  and EUF_RMA_FLXMSSTWES_NOPRF with conditions and combined sampling and computations; 
  includes equality on the condition concerning the validity of the WOTS-TW forgery. 
 *)
local equiv EUF_RMA_FLXMSSTWES_NOPRF_Conditions_SSampling_Mono_Validity :
  EUF_RMA_FLXMSSTWES_NOPRF_Conditions_SSampling.main ~ EUF_RMA_FLXMSSTWES_NOPRF_Conditions_Mono.main :
    ={glob A} 
    ==> 
    ={res} /\ EUF_RMA_FLXMSSTWES_NOPRF_Conditions_SSampling.valid_WOTSTWES{1} = EUF_RMA_FLXMSSTWES_NOPRF_Conditions_Mono.valid_WOTSTWES{2}.
proof.
proc => //=.
swap{1} [11..13] -5; swap{1} 6 -3.
fusion{1} 6!1 @ 2, 2.
seq 6 6 : (   ={glob A, ps, ad, ml}
           /\ size skWOTSl{1} = l
           /\ size ml{2} = l
           /\ size pkWOTSl{2} = l
           /\ size sigWOTSl{2} = l
           /\ all ((=) len \o size) (pkWOTSl{2})
           /\ all ((=) len \o size) (sigWOTSl{2})
           /\ (forall (j n : int), 0 <= j < l => 0 <= n < len =>
                 nth witness (nth witness pkWOTSl{2} j) n
                 =
                 cf ps{1} (set_chthidx (set_kpidx (set_typeidx ad{1} chtype) j) n) 0 (w - 1) (val (nth witness (nth witness skWOTSl{1} j) n)))
           /\ (forall (j n : int), 0 <= j < l => 0 <= n < len =>
                 nth witness (nth witness sigWOTSl{2} j) n
                 =
                 cf ps{1} (set_chthidx (set_kpidx (set_typeidx ad{1} chtype) j) n) 0 (BaseW.val (encode_msgWOTS (nth witness ml{1} j)).[n]) (val (nth witness (nth witness skWOTSl{1} j) n)))).
+ while (   ={ps, ad, ml}
         /\ i{1} = size ml{2}
         /\ i{1} = size skWOTSl{1}
         /\ size ml{2} = size pkWOTSl{2}
         /\ size ml{2} = size sigWOTSl{2}
         /\ 0 <= size ml{2} <= l
         /\ all ((=) len \o size) (pkWOTSl{2})
         /\ all ((=) len \o size) (sigWOTSl{2})
         /\ (forall (j n : int), 0 <= j < size pkWOTSl{2} => 0 <= n < len =>
                 nth witness (nth witness pkWOTSl{2} j) n
                 =
                 cf ps{1} (set_chthidx (set_kpidx (set_typeidx ad{1} chtype) j) n) 0 (w - 1) (val (nth witness (nth witness skWOTSl{1} j) n)))
         /\ (forall (j n : int), 0 <= j < size sigWOTSl{2} => 0 <= n < len =>
                 nth witness (nth witness sigWOTSl{2} j) n
                 =
                 cf ps{1} (set_chthidx (set_kpidx (set_typeidx ad{1} chtype) j) n) 0 (BaseW.val (encode_msgWOTS (nth witness ml{1} j)).[n]) (val (nth witness (nth witness skWOTSl{1} j) n)))).
  - wp.
    while{2} (   0 <= size ml{2} < l 
              /\ 0 <= size sigWOTS{2} <= len
              /\ all ((=) len \o size) (sigWOTSl{2})
              /\  (forall (n : int), 0 <= n < size sigWOTS{2} =>
                   nth witness sigWOTS{2} n
                   =
                   cf ps{2} (set_chthidx (set_kpidx (set_typeidx ad{2} chtype) (size ml{2})) n) 0 (BaseW.val em{2}.[n]) (val (nth witness skWOTS{2} n))))
             (len - size sigWOTS{2}).
    * move=> _ z.
      wp; skip => /> &1 ge0_szmsigl ltl_szmsigl ge0_szsigw eql_szml _ valsigw ltlen_szpkw.
      rewrite andbC !andbA; split => [| n ge0_n]; first by smt(size_rcons).
      rewrite size_rcons=> ltszpkw1_n; rewrite nth_rcons.
      case (n < size sigWOTS{1}) => [/# | /lezNgt geszpkw_n].
      by rewrite (: n = size sigWOTS{1}) 1:/#.
    wp.
    while{2} (   0 <= size ml{2} < l
              /\ 0 <= size pkWOTS{2} <= len
              /\ all ((=) len \o size) (pkWOTSl{2})
              /\ (forall (n : int), 0 <= n < size pkWOTS{2} =>
                   nth witness pkWOTS{2} n
                   =
                   cf ps{2} (set_chthidx (set_kpidx (set_typeidx ad{2} chtype) (size ml{2})) n) 0 (w - 1) (val (nth witness skWOTS{2} n))))
             (len - size pkWOTS{2}).
    * move=> _ z.
      wp; skip => /> &2 ge0_szmsigl ltl_szmsigl ge0_szsigw eql_szml _ valsigw ltlen_szpkw.
      rewrite andbC !andbA; split => [| n ge0_n]; first by smt(size_rcons).
      rewrite size_rcons=> ltszpkw1_n; rewrite nth_rcons.
      case (n < size pkWOTS{2}) => [/# | /lezNgt geszpkw_n].
      by rewrite (: n = size pkWOTS{2}) 1:/#.
    swap{1} 3 -2; wp; rnd; rnd; skip => /> &1 &2 eqszml_szskwl eqszml_szpkwl eqszml_szsigwl ge0_szml _ alen_pkwl alen_sigwl pkwl_def sigwl_def ltl_szml m min skwlp skwlpin.
    split => [| pkw]; first by smt(ge2_len).
    split => [/# | /lezNgt gelen_szpkw _ lelen_szpkw pkw_def].
    split => [| sigw]; first by smt(ge2_len).
    split => [/# | /lezNgt gelen_szsigw _ lelen_szsigw sigw_def].
    rewrite -!andbA 5!andbA; split; first by smt(size_rcons).
    rewrite andbA; split; first by rewrite -2!cats1 2!all_cat /#. 
    by split; 2: split; by smt(ge2_len nth_rcons size_rcons). 
  by wp; call (: true); rnd; skip => />; smt(ge2_l).
seq 7 6 : (={glob A, ps, ad, pkWOTSl, root, pk, msigl}).
+ while (   ={ps, ad, ml, leafl, msigl}
         /\ size sigWOTSl{2} = l
         /\ 0 <= size msigl{1} <= l
         /\ all ((=) len \o size) (sigWOTSl{2})
         /\ (forall (j n : int), 0 <= j < l => 0 <= n < len =>
               nth witness (nth witness sigWOTSl{2} j) n
               =
               cf ps{1} (set_chthidx (set_kpidx (set_typeidx ad{1} chtype) j) n) 0 (BaseW.val (encode_msgWOTS (nth witness ml{1} j)).[n]) (val (nth witness (nth witness skWOTSl{1} j) n)))).
  - wp.
    while{1} (   ={msigl}
              /\ skWOTS{1} = nth witness skWOTSl{1} (size msigl{1})
              /\ em{1} = encode_msgWOTS (nth witness ml{1} (size msigl{1}))
              /\ size sigWOTSl{2} = l
              /\ 0 <= size msigl{1} < l
              /\ 0 <= size sigWOTS{1} <= len
              /\ all ((=) len \o size) (sigWOTSl{2})
              /\ (forall (j n : int), 0 <= j < l => 0 <= n < len =>
                   nth witness (nth witness sigWOTSl{2} j) n
                   =
                   cf ps{1} (set_chthidx (set_kpidx (set_typeidx ad{1} chtype) j) n) 0 (BaseW.val (encode_msgWOTS (nth witness ml{1} j)).[n]) (val (nth witness (nth witness skWOTSl{1} j) n)))
              /\ (forall (n : int), 0 <= n < size sigWOTS{1} =>
                    nth witness sigWOTS{1} n 
                    = 
                    nth witness (nth witness sigWOTSl{2} (size msigl{2})) n))
             (len - size sigWOTS{1}).
    * move=> &2 z.
      wp; skip => /> &1 eql_szsigwl ge0_szmsigl ltl_szmsigl ge0_szsigw _ allen valsigwl valsigw ltlen_szpkw.
      rewrite andbC !andbA; split => [| n ge0_n]; first by smt(size_rcons).
      rewrite size_rcons=> ltszpkw1_n; rewrite nth_rcons.
      case (n < size sigWOTS{1}) => [/# | /lezNgt geszpkw_n].
      by rewrite (: n = size sigWOTS{1}) /#.  
    wp; skip => /> &1 &2 eql_szsigwl ge0_msigl _ alen_sigwl sigwl_def ltl_szmsigl.
    split => [| sigwlp]; first by smt(ge2_len).
    split => [/#| /lezNgt gelen_szsigwlp _ lelen_szsigwlp sigwlp_def].
    rewrite -!andbA; split; last by smt(size_rcons).
    do 4! congr; apply (eq_from_nth witness); last by apply sigwlp_def.
    rewrite (: size sigwlp = len) 1:/#. 
    by move/(all_nthP _ _ witness): alen_sigwl => /(_ (size msigl{2}) _) /#.
  wp.
  while (   ={ps, ad, leafl}
           /\ size pkWOTSl{2} = l
           /\ size leafl{1} = size pkWOTSl{1}
           /\ 0 <= size leafl{1} <= l
           /\ all ((=) len \o size) (pkWOTSl{2})
           /\ (forall (j n : int), 0 <= j < l => 0 <= n < len =>
                 nth witness (nth witness pkWOTSl{2} j) n
                 =
                 cf ps{1} (set_chthidx (set_kpidx (set_typeidx ad{1} chtype) j) n) 0 (w - 1) (val (nth witness (nth witness skWOTSl{1} j) n)))
           /\ (forall (n : int), 0 <= n < size pkWOTSl{1} =>
                 nth witness pkWOTSl{1} n = nth witness pkWOTSl{2} n)).
  - wp.
    while{1} (   ={leafl}
              /\ skWOTS{1} = nth witness skWOTSl{1} (size leafl{1})
              /\ 0 <= size leafl{1} < l
              /\ 0 <= size pkWOTS{1} <= len
              /\ all ((=) len \o size) (pkWOTSl{2})
              /\ (forall (j n : int), 0 <= j < l => 0 <= n < len =>
                   nth witness (nth witness pkWOTSl{2} j) n
                   =
                   cf ps{1} (set_chthidx (set_kpidx (set_typeidx ad{1} chtype) j) n) 0 (w - 1) (val (nth witness (nth witness skWOTSl{1} j) n)))
              /\ (forall (n : int), 0 <= n < size pkWOTS{1} =>
                    nth witness pkWOTS{1} n 
                    = 
                    nth witness (nth witness pkWOTSl{2} (size leafl{2})) n))
             (len - size pkWOTS{1}).
    * move=> &2 z.
      wp; skip => /> &1 ge0_szlfl ltl_szlfl ge0_szpkw _ allen valpkwl valpkw ltlen_szpkw.
      rewrite andbC !andbA; split => [| n ge0_n]; first by smt(size_rcons).
      rewrite size_rcons=> ltszpkw1_n; rewrite nth_rcons.
      case (n < size pkWOTS{1}) => [/# | /lezNgt geszpkw_n].
      rewrite (: n = size pkWOTS{1}) /#.
    wp; skip => /> &1 &2 eql_szpkwl eqszpkwl_szlfl ge0_szlfl _ alen_pkwl pkwl_def pkwl_rel ltl_szlfl.
    split => [| pkw]; first by smt(ge2_len). 
    split => [/#| /lezNgt gelen_szpkw _ lelen_szpkw pkw_def].
    rewrite -!andbA; split.
    * do 4! congr; apply (eq_from_nth witness); last by apply pkw_def.
      rewrite (: size pkw = len) 1:/#. 
      by move/(all_nthP _ _ witness): alen_pkwl => /(_ (size leafl{2}) _) /#.
    rewrite 2!andbA; split; first by smt(size_rcons).
    split; last by smt(size_rcons).
    move=> n ge0_n; rewrite size_rcons => ltszpkwl1_n.
    rewrite nth_rcons; case (n < size pkWOTSl{1}) => [ltszpkw_n /# | /lezNgt geszpkw_n].
    rewrite (: n = size pkWOTSl{1}) 1:/# /=; apply (eq_from_nth witness).
    * rewrite (: size pkw = len) 1:/#.
      by move/(all_nthP _ _ witness): alen_pkwl => /(_ (size pkWOTSl{1}) _) /#.
    by rewrite -eqszpkwl_szlfl &(pkw_def).
  wp; skip => /> *. 
  split => [| *]; first by smt(ge2_l).
  split => [| *]; first by smt(ge2_l).
  by apply (eq_from_nth witness) => /#.
by sim.          
qed.

local equiv EUF_RMA_FLXMSSTWES_NOPRF_Conditions_Mono_Validity :
  EUF_RMA_FLXMSSTWES_NOPRF_Conditions.main ~ EUF_RMA_FLXMSSTWES_NOPRF_Conditions_Mono.main :
    ={glob A} 
    ==> 
    ={res} /\ EUF_RMA_FLXMSSTWES_NOPRF_Conditions.valid_WOTSTWES{1} = EUF_RMA_FLXMSSTWES_NOPRF_Conditions_Mono.valid_WOTSTWES{2}.
proof.
transitivity EUF_RMA_FLXMSSTWES_NOPRF_Conditions_SSampling.main
             (={glob A} 
              ==> 
              ={res} /\ 
              EUF_RMA_FLXMSSTWES_NOPRF_Conditions.valid_WOTSTWES{1}
              =
              EUF_RMA_FLXMSSTWES_NOPRF_Conditions_SSampling.valid_WOTSTWES{2})
             (={glob A} 
              ==> 
              ={res} /\ 
              EUF_RMA_FLXMSSTWES_NOPRF_Conditions_SSampling.valid_WOTSTWES{1}
              =
              EUF_RMA_FLXMSSTWES_NOPRF_Conditions_Mono.valid_WOTSTWES{2}) => //.
+ by move=> &1 *; exists (glob A){1} => //.
+ by apply EUF_RMA_FLXMSSTWES_NOPRF_Conditions_SSampling_Validity.
by apply EUF_RMA_FLXMSSTWES_NOPRF_Conditions_SSampling_Mono_Validity.
qed.


(* - Game-Playing Proof - *)
(* 
  Zeroeth step: 
  Show equivalence between EUF_RMA_FLXMSSTWES and EUF_RMA_FLXMSSTWES_Inline 
*)
local equiv EUFRMA_FLXMSSTWES_Inline :
  EUF_RMA_FLXMSSTWES(A).main ~ EUF_RMA_FLXMSSTWES_Inline.main : ={glob A} ==> ={res}.
proof.
proc; inline *.
seq 3 3 : (={glob A, ss, ps, ad}); first by call(: true); rnd; rnd; skip.
seq 9 4 : (   ={glob A, leafl}
           /\ ss0{1} = ss{2}
           /\ ps0{1} = ps{2}
           /\ ad0{1} = ad{2} 
           /\ all ((=) len \o size) skWOTSl{2}
           /\ all ((=) len \o size) pkWOTSl{2}
           /\ size skWOTSl{2} = l
           /\ size pkWOTSl{2} = l
           /\ size leafl{2} = l
           /\ (forall (i j : int), 0 <= i < l => 0 <= j < len => 
                  nth witness (nth witness skWOTSl{2} i) j 
                  = 
                  prf_sk ss{2} (ps{2}, set_htbidx (set_chthidx (set_kpidx (set_typeidx ad{2} chtype) i) j) 0))
           /\ (forall (i j : int), 0 <= i < l => 0 <= j < len => 
                  nth witness (nth witness pkWOTSl{2} i) j 
                  = 
                  cf ps{2} (set_chthidx (set_kpidx (set_typeidx ad{2} chtype) i) j) 0 (w - 1) (val (nth witness (nth witness skWOTSl{2} i) j)))
           /\ (forall (i : int), 0 <= i < l => 
                  nth witness leafl{2} i
                  =
                  pkco ps{2} (set_kpidx (set_typeidx ad{2} pkcotype) i) (flatten (map DigestBlock.val (nth witness pkWOTSl{2} i))))).
+ wp.
  while(   ss2{1} = ss{2}
        /\ ps3{1} = ps{2}
        /\ ad3{1} = ad{2}
        /\ leafl1{1} = leafl{2}
        /\ 0 <= size leafl{2} <= l
        /\ size skWOTSl{2} = size leafl{2}
        /\ size pkWOTSl{2} = size leafl{2}
        /\ all ((=) len \o size) skWOTSl{2}
        /\ all ((=) len \o size) pkWOTSl{2}
        /\ (forall (i j : int), 0 <= i < size leafl{2} => 0 <= j < len => 
                  nth witness (nth witness skWOTSl{2} i) j 
                  = 
                  prf_sk ss{2} (ps{2}, set_htbidx (set_chthidx (set_kpidx (set_typeidx ad{2} chtype) i) j) 0))
        /\ (forall (i j : int), 0 <= i < size leafl{2} => 0 <= j < len => 
                  nth witness (nth witness pkWOTSl{2} i) j 
                  = 
                  cf ps{2} (set_chthidx (set_kpidx (set_typeidx ad{2} chtype) i) j) 0 (w - 1) (val (nth witness (nth witness skWOTSl{2} i) j)))
        /\ (forall (i : int), 0 <= i < size leafl{2} => 
                  nth witness leafl{2} i
                  =
                  pkco ps{2} (set_kpidx (set_typeidx ad{2} pkcotype) i) (flatten (map DigestBlock.val (nth witness pkWOTSl{2} i))))).
  - swap{2} 7 -2; swap{2} 7 -4. 
    wp.
    while(   ps8{1} = ps{2}
          /\ ad8{1} = set_kpidx (set_typeidx ad{2} chtype) (size leafl{2})
          /\ skWOTS5{1} = DBLL.insubd skWOTS{2}
          /\ pkWOTS3{1} = pkWOTS{2}
          /\ size skWOTS{2} = len
          /\ 0 <= size leafl{2} < l
          /\ 0 <= size pkWOTS{2} <= len
          /\ (forall (i : int), 0 <= i < size pkWOTS{2} =>
                  nth witness pkWOTS{2} i
                  =
                  cf ps{2} (set_chthidx (set_kpidx (set_typeidx ad{2} chtype) (size leafl{2})) i) 0 (w - 1) (val (nth witness skWOTS{2} i)))).
    * wp; skip => /> &2 eqlen_szskw ge0_szlfl ltl_szlfl ge0_szpkw _ valsigw ltlen_szpkw.
      rewrite insubdK //=; split => [| n ge0_n]; first by smt(size_rcons).
      rewrite size_rcons=> ltszpkw1_n; rewrite nth_rcons.
      case (n < size pkWOTS{2}) => [/# | /lezNgt geszpkw_n].
      by rewrite (: n = size pkWOTS{2}) 1:/#.
    wp.
    while(   ss5{1} = ss{2}
          /\ ps7{1} = ps{2}
          /\ ad7{1} = set_kpidx (set_typeidx ad{2} chtype) (size leafl{2})
          /\ skWOTS4{1} = skWOTS{2}
          /\ 0 <= size skWOTS{2} <= len
          /\ (forall (i : int), 0 <= i < size skWOTS{2} =>
                nth witness skWOTS{2} i
                =
                prf_sk ss{2} (ps{2}, set_htbidx (set_chthidx (set_kpidx (set_typeidx ad{2} chtype) (size leafl{2})) i) 0))).
    * by wp; skip => />; smt(nth_rcons size_rcons).
    wp; skip => /> &2 ge0_szlfl _ eqsz_sklfl eqsz_pklfl alllen_szsk alllen_szpk skl_def pkl_def lfl_def ltl_szlfl.
    split => [| skW /lezNgt gelen_szskw _ ge0_szskw lelen_szskw skw_def]; first by smt(ge2_len).
    split => [| pkW /lezNgt gelen_szpkw _ eqlen_szskw ge0_szpkw lelen_szpkw pkw_def]; first by smt(ge2_len).
    rewrite insubdK 1:/# /= 2!andbA; split; first by smt(size_rcons).
    rewrite andbA; split; first by rewrite ?(-cats1, all_cat) alllen_szsk alllen_szpk /= /(\o) /#.
    rewrite size_rcons; split => [i j |]; last split => [i j | i ].
    * move => ge0_i ltszlfl1_i ge0_j ltlen_j.
      rewrite nth_rcons; case (i < size skWOTSl{2}) => [ltszskl_i | /lezNgt geszskl_i].
      + by rewrite skl_def 1,2:/#.
      by rewrite (: i = size skWOTSl{2}) 1:/# /= skw_def 1:/# eqsz_sklfl.
    * move => ge0_i ltszlfl1_i ge0_j ltlen_j.
      rewrite nth_rcons; case (i < size pkWOTSl{2}) => [ltszpkl_i | /lezNgt geszpkl_i].
      + by rewrite pkl_def 1,2:/# nth_rcons eqsz_sklfl -eqsz_pklfl ltszpkl_i.
      rewrite (: i = size pkWOTSl{2}) 1:/# /= pkw_def 1:/# eqsz_pklfl.
      by rewrite nth_rcons eqsz_sklfl -eqsz_pklfl.
    move => ge0_i ltlfl1_i; rewrite nth_rcons. 
    case (i < size leafl{2}) => [ltszlfl_i | /lezNgt geszlfl_i].
    * by rewrite nth_rcons eqsz_pklfl ltszlfl_i /= lfl_def.
    by rewrite (: i = size leafl{2}) 1:/# nth_rcons eqsz_pklfl.
  wp; skip => /> &2.
  split => [| *]; first by smt(ge2_l). 
  rewrite 2!andbA; split; first by smt(ge2_l).
  by split; 2: split; smt(ge2_l).
seq 7 5 : (   ={pk, msigl, m', sig'}
           /\ pk{2} = (root{2}, ps{2}, ad{2})).
+ call(: true).
  sp; conseq />.
  while(   ={msigl}
        /\ sk{1} = (insubd (size msigl{2}), ss{2}, ps{2}, ad{2})
        /\ all ((=) len \o size) skWOTSl{2}
        /\ all ((=) len \o size) pkWOTSl{2}
        /\ size skWOTSl{2} = l
        /\ size pkWOTSl{2} = l
        /\ size leafl{2} = l
        /\ 0 <= size msigl{2} <= l 
        /\ (forall (i j : int), 0 <= i < l => 0 <= j < len => 
                  nth witness (nth witness skWOTSl{2} i) j 
                  = 
                  prf_sk ss{2} (ps{2}, set_htbidx (set_chthidx (set_kpidx (set_typeidx ad{2} chtype) i) j) 0))
           /\ (forall (i j : int), 0 <= i < l => 0 <= j < len => 
                  nth witness (nth witness pkWOTSl{2} i) j 
                  = 
                  cf ps{2} (set_chthidx (set_kpidx (set_typeidx ad{2} chtype) i) j) 0 (w - 1) (val (nth witness (nth witness skWOTSl{2} i) j)))
           /\ (forall (i : int), 0 <= i < l => 
                  nth witness leafl{2} i
                  =
                  pkco ps{2} (set_kpidx (set_typeidx ad{2} pkcotype) i) (flatten (map DigestBlock.val (nth witness pkWOTSl{2} i))))).
  - wp.
    while{1}(   ss4{1} = ss{2}
             /\ ps5{1} = ps{2}
             /\ ad5{1} = ad{2}
             /\ 0 <= size leafl2{1} <= l
             /\ all ((=) len \o size) skWOTSl{2}
             /\ all ((=) len \o size) pkWOTSl{2}
             /\ size skWOTSl{2} = l
             /\ size pkWOTSl{2} = l
             /\ size leafl{2} = l
             /\ (forall (i j : int), 0 <= i < l => 0 <= j < len => 
                  nth witness (nth witness skWOTSl{2} i) j 
                  = 
                  prf_sk ss{2} (ps{2}, set_htbidx (set_chthidx (set_kpidx (set_typeidx ad{2} chtype) i) j) 0))
           /\ (forall (i j : int), 0 <= i < l => 0 <= j < len => 
                  nth witness (nth witness pkWOTSl{2} i) j 
                  = 
                  cf ps{2} (set_chthidx (set_kpidx (set_typeidx ad{2} chtype) i) j) 0 (w - 1) (val (nth witness (nth witness skWOTSl{2} i) j)))
           /\ (forall (i : int), 0 <= i < l => 
                  nth witness leafl{2} i
                  =
                  pkco ps{2} (set_kpidx (set_typeidx ad{2} pkcotype) i) (flatten (map DigestBlock.val (nth witness pkWOTSl{2} i))))
             /\ (forall (i : int), 0 <= i < size leafl2{1} =>
                   nth witness leafl2{1} i = nth witness leafl{2} i))
            (l - size leafl2{1}).
    * move=> &2 z. 
      wp.
      while(   is_chtype ad11
            /\ 0 <= size leafl2 < l
            /\ 0 <= size pkWOTS4 <= len
            /\ (forall (i : int), 0 <= i < len =>
                  nth witness (val skWOTS8) i 
                  =
                  prf_sk ss7 (ps11, set_htbidx (set_chthidx ad11 i) 0))
            /\ (forall (i : int), 0 <= i < size pkWOTS4 =>
                  nth witness pkWOTS4 i
                  =
                  cf ps11 (set_chthidx ad11 i) 0 (w - 1) (val (nth witness (val skWOTS8) i))))
           (len - size pkWOTS4).
      + move => z'. 
        wp; skip => /> &1 adch ge0_szlfl ltl_szlfl ge0_szsigw _ valskw valpkw ltlen_szpkw.
        rewrite andbC !andbA; split => [| n ge0_n]; first by smt(size_rcons).
        rewrite size_rcons=> ltszpkw1_n; rewrite nth_rcons.
        case (n < size pkWOTS4{1}) => [/# | /lezNgt geszpkw_n].
        by rewrite (: n = size pkWOTS4{1}) 1:/#.
      wp.
      while(   0 <= size skWOTS7 <= len
            /\ (forall (i : int), 0 <= i < size skWOTS7 =>
                  nth witness skWOTS7 i 
                  =
                  prf_sk ss7 (ps10, set_htbidx (set_chthidx ad10 i) 0)))
           (len- size skWOTS7).
      + move => z'. 
        by wp; skip => />; smt(nth_rcons size_rcons).
      wp; skip => /> &1 ge0_szlfl2 _ alllen_skl alllen_pkl eql_szskl eql_szpkl eql_szlfl skl_def pkl_def lfl_def lfl_rel ltl_szlfl2.
      split => [| skW]; first by smt(ge2_len).
      split => [/# | /lezNgt gelen_szskw _ lelen_szskw skw_def].
      split => [| pkw]; first split; last by smt(ge2_len DBLL.insubdK).
      + by rewrite ischtype_setkpidx 1:ischtype_settypeidx.
      split => [/# | /lezNgt gelen_skpkw _ _ lelen_szpkw skwf_def pkw_def].
      rewrite -andbA; split; first by smt(size_rcons).
      rewrite size_rcons; split => [i ge0_i leszlfl1_i | ]; last by smt(size_rcons).
      rewrite nth_rcons; case (i < size leafl2{1}) => [ltszlfl2_i | /lezNgt geszlfl2_i].
      + by rewrite lfl_rel 1:/#.
      rewrite (: i = size leafl2{1}) 1:/# lfl_def 1:/# /=.
      do 3! congr; apply (eq_from_nth witness).
      + rewrite valP; move/all_nthP /(_ witness (size leafl2{1}) _): alllen_pkl.
        - by smt().
        by rewrite /(\o).
      rewrite insubdK 1:/#; move=> j rng_j.
      rewrite pkw_def 1:rng_j pkl_def 1,2:/#.
      do 3! congr; apply (eq_from_nth witness).
      + move/all_nthP /(_ witness (size leafl2{1}) _): alllen_skl.
        - by smt().
        by rewrite valP /(\o).
      by rewrite insubdK 1:/#; move=> k rng_k; rewrite skw_def 1:rng_k skl_def 1,2:/#.
    wp.
    while(   ={em, msigl}
          /\ idx{1} = insubd (size msigl{2})
          /\ ps4{1} = ps{2}
          /\ ad4{1} = set_kpidx (set_typeidx ad{2} chtype) (size msigl{2})
          /\ skWOTS2{1} = DBLL.insubd skWOTS{2}
          /\ size skWOTS{2} = len
          /\ sig2{1} = sigWOTS{2}
          /\ 0 <= size sig2{1} <= len).
    * by wp; skip => />; smt(size_rcons DBLL.insubdK).
    wp.
    while{1}(   0 <= size skWOTS6{1} <= len
             /\ (forall (i : int), 0 <= i < size skWOTS6{1} =>
                   nth witness skWOTS6{1} i
                   =
                   prf_sk ss6{1} (ps9{1}, set_htbidx (set_chthidx ad9{1} i) 0)))
            (len - size skWOTS6{1}).
    * move=> _ z.
      wp; skip => /> &1 ge0_skw _ skw_def ltlen_skw.
      rewrite -andbA; split; first by smt(size_rcons).
      split; last by smt(size_rcons).
      rewrite size_rcons => i ge0_i ltszskw1_i; rewrite nth_rcons.
      case (i < size skWOTS6{1}) => [ltszsk_i | /lezNgt geszsk_i].
      + by rewrite skw_def 1:/#.
      by rewrite (: i = size skWOTS6{1}) 1:/#.
    wp; rnd; skip => /> &2 alllen_skl alllen_pkl eql_szskl eql_szpkl eql_szlfl ge0_ml _ skl_def pkl_def lfl_def ltl_ml m _.
    split => [| skW]; first by smt(ge2_len).
    split => [/# | /lezNgt gelen_szskw _ lelen_szskw skw_def].
    split => [| sigW /lezNgt gelen_szsigw _ _ skweq _ _ lelen_szsigw]. 
    * rewrite insubdK 1:/# insubdK 1:ischtype_setkpidx 1:ischtype_settypeidx //=.
      rewrite andbA; split; last by smt(ge2_len). 
      split; first congr; apply (eq_from_nth witness).
      + rewrite (: size skW = len) 1:/#.
        move/all_nthP /(_ witness (size msigl{2}) _): alllen_skl; first by smt().
        by rewrite /(\o).
      + by move=> i rng_i; rewrite skw_def 2:skl_def // 1:/# insubdK 1:// insubdK 1:ischtype_setkpidx 1:ischtype_settypeidx.
      by move/all_nthP /(_ witness (size msigl{2}) _): alllen_skl; smt().
    split => [/# | lfl2]; split => [/# | /lezNgt gel_szlfl2 _ lel_szlfl2 lfl_rel].
    rewrite -!andbA andbA; split; last by smt(size_rcons).
    split; last by rewrite insubdK 1:// size_rcons.
    do ? congr; apply (eq_from_nth witness) => [/#| ].
    by apply lfl_rel.
  by wp; skip => />; smt(ge2_l).
wp.
while(   sig4{1} = DBLL.insubd sigWOTS'{2}
      /\ em0{1} = em{2}
      /\ ps12{1} = ps{2}
      /\ ad12{1} = set_kpidx (set_typeidx ad{2} chtype) (val idx'{2}) 
      /\ pkWOTS5{1} = pkWOTS'{2}
      /\ size sigWOTS'{2} = len
      /\ 0 <= size pkWOTS'{2} <= len).
+ by wp; skip => />; smt(size_rcons DBLL.insubdK).
wp; skip => /> &2 *.
split => [| pkw *]; first by smt(ge2_len DBLL.valP DBLL.valK).
by rewrite DBLL.insubdK 1:/#.
qed.


(* 
  First step: 
  Reduce PRF of prf_sk to distinguishing between EUF_RMA_FLXMSSTWES_Inline 
  and EUFRMA_FLXMSSTWES_NOPRF
*)
local lemma Step_EUFRMAFLXMSSTWESInlineNOPRF_PRF &m :
  `|Pr[EUF_RMA_FLXMSSTWES_Inline.main() @ &m : res] - Pr[EUF_RMA_FLXMSSTWES_NOPRF(A).main() @ &m : res]|
  =
  `|Pr[PRF_SK_PRF.PRF(R_PRF_FLXMSSTWESInlineNOPRF(A), PRF_SK_PRF.O_PRF_Default).main(false) @ &m : res] - Pr[PRF_SK_PRF.PRF(R_PRF_FLXMSSTWESInlineNOPRF(A), PRF_SK_PRF.O_PRF_Default).main(true) @ &m : res]|.
proof.
do 2! congr; last congr.
+ byequiv => //.
  proc; inline{2} 2.
  wp 22 23.
  seq 7 7 : (={glob A, ps, ad, skWOTSl, leafl}).
  - while(   #post
          /\ ss{1} = PRF_SK_PRF.O_PRF_Default.k{2}
          /\ PRF_SK_PRF.O_PRF_Default.b{2} = false  
          /\ size skWOTSl{1} = size leafl{1}
          /\ 0 <= size leafl{1} <= l).
    * wp.
      while(   ={ps, ad, skWOTS, pkWOTS, leafl}
            /\ size skWOTS{1} = len
            /\ 0 <= size leafl{1} < l
            /\ 0 <= size pkWOTS{1} <= len).
      + by wp; skip => />; smt(size_rcons).
      wp.
      while(   ={ps, ad, skWOTS, leafl}
            /\ ss{1} = PRF_SK_PRF.O_PRF_Default.k{2}
            /\ PRF_SK_PRF.O_PRF_Default.b{2} = false
            /\ 0 <= size leafl{1} < l
            /\ 0 <= size skWOTS{1} <= len).
      + inline{2} 1.
        rcondf{2} 2; first by auto.
        by wp; skip => />; smt(size_rcons).        
      by wp; skip => />; smt(ge2_len size_rcons).
    inline{2} 1.
    by wp; call(: true); rnd; wp; rnd; wp; skip => />; smt(ge2_l).
  wp 15 15.
  by sim : (={is_valid, is_fresh}).
have ->: 
  Pr[EUF_RMA_FLXMSSTWES_NOPRF(A).main() @ &m : res]
  =
  Pr[EUF_RMA_FLXMSSTWES_NOPRF_Loop.main() @ &m : res].
+ by byequiv EUF_RMA_FLXMSSTWES_NOPRF_Orig_Loop.  
byequiv => //.
proc; inline{2} 2.
wp 20 22.
seq 5 7 : (={glob A, ps, ad, skWOTSl, leafl}).
- while(   #post
        /\ PRF_SK_PRF.O_PRF_Default.b{2} = true  
        /\ size skWOTSl{1} = size leafl{1}
        /\ 0 <= size leafl{1} <= l
        /\ (forall (psad : pseed * adrs),
             (psad \in PRF_SK_PRF.O_PRF_Default.m{2}
              <=>
              (exists (i j : int), 
                  0 <= i < size leafl{2} /\ 0 <= j < len /\
                  psad = (ps{2}, set_htbidx (set_chthidx (set_kpidx (set_typeidx ad{2} chtype) i) j) 0))))).
  * wp.
    while(   ={ps, ad, skWOTS, pkWOTS, leafl}
          /\ size skWOTS{1} = len
          /\ 0 <= size leafl{1} < l
          /\ 0 <= size pkWOTS{1} <= len).
    + by wp; skip => />; smt(size_rcons).
    wp.
    while(   ={ps, ad, skWOTS, leafl}
          /\ PRF_SK_PRF.O_PRF_Default.b{2} = true
          /\ 0 <= size leafl{1} < l
          /\ 0 <= size skWOTS{1} <= len
          /\ (forall (psad : pseed * adrs),
                (psad \in PRF_SK_PRF.O_PRF_Default.m{2}
                 <=>
                 ((exists (i j : int), 
                    0 <= i < size leafl{2} /\ 0 <= j < len /\
                    psad = (ps{2}, set_htbidx (set_chthidx (set_kpidx (set_typeidx ad{2} chtype) i) j) 0))
                   \/
                   (exists (j : int),
                     0 <= j < size skWOTS{2} /\ 
                     psad = (ps{2}, set_htbidx (set_chthidx (set_kpidx (set_typeidx ad{2} chtype) (size leafl{2})) j) 0)))))).
    + inline{2} 1.
      rcondt{2} 2; first by auto.
      rcondt{2} 2. 
      - move => &2; wp; skip => />. 
        move => &h ge0_szlfl ltl_szlfl ge0_szskw _ m_def ltlen_szskw.
        rewrite m_def negb_or 2!negb_exists /=.
        split => i.
        * rewrite negb_exists => j /=; rewrite andbA negb_and -implybE => -[rng_i rng_j].
          apply setkpidx_setchidx_sethidx_neqkpidx; last 7 smt(ge2_l ge2_len val_w). 
          + rewrite /set_typidx /is_chtype getadrsK 1:-madrs_dom /valid_adidxs //=.
            by smt(madidxs_valid ge2_l ge2_len val_w). 
          rewrite /set_typidx /is_chtype getadrsK 1:-madrs_dom /valid_adidxs //=.
          by smt(madidxs_valid ge2_l ge2_len val_w).
        rewrite negb_and -implybE => rng_i.
        apply setchidx_sethidx_neqchidx; last 5 smt(ge2_l ge2_len val_w).
        * by rewrite /set_typidx /set_kpidx /is_chtype ?getadrsK -?madrs_dom /valid_adidxs //=; smt(madidxs_valid ge2_l ge2_len val_w).
        by rewrite /set_typidx /set_kpidx /is_chtype ?getadrsK -?madrs_dom /valid_adidxs //=; smt(madidxs_valid ge2_l ge2_len val_w).
      wp; rnd; wp; skip => /> &2 ge0_szlfl ltl_szlfl ge0_szskw _ m_def ltl_skw skw_ele _.
      split; last by smt(size_rcons).
      split; last split => [| psad]; first by smt(size_rcons).
      - by congr; rewrite get_set_sameE oget_some.
      split => [/mem_set [/m_def [/# | [j] [rng_j psad_val]] | psad_val] | mp_def].
      - by right; exists j; smt(size_rcons).
      - by right; exists (size skWOTS{2}); smt(size_rcons).
      rewrite mem_set; move: mp_def => -[] -[i].
      - move => j [rng_i] [rng_j] ->; left.
        by apply m_def; left; exists i j.
      rewrite size_rcons => -[rng_i] ->.
      case (i < size skWOTS{2}) => [ltszskw_i | /lezNgt geszskw_i].
      - by left; apply m_def; right; exists i => /#.
      by rewrite (: i = size skWOTS{2}) /#.
    wp; skip => /> &2 eqszlfl_skw ge0_szlsl _ m_def ltl_szlfl.
    split => [| mr skw /lezNgt gelen_szskw _ _ lelen_szskw mp_def].
    + split => [| psad]; first by smt(ge2_len).
      by split => [/m_def /# | [/m_def //| /#]].
    split => [| pkw /lezNgt gelen_szpkw _ eqlen_skw _ lelen_szpkw]; first by smt(ge2_len).
    rewrite andbA; split => [| psad]; first by smt(size_rcons).
    split => [/mp_def [[i j] [rng_i] [rng_j] -> | [j] [rng_j] ->] | i j].
    + by rewrite size_rcons; exists i j => /#. 
    + by rewrite size_rcons; exists (size leafl{2}) j => /#.
    rewrite size_rcons => ge0_i ltszlfl1_i ge0_j ltlen_j.
    apply mp_def; case (i < size leafl{2}) => [ltszlfl_i | /lezNgt geszlfl_i].
    + by left; exists i j => /#.
    by right; exists j => /#.
  inline{2} 1.
  wp; call(: true); rnd; wp; rnd{2}; wp; skip => /> k _ ps _ ad.
  split => [ | psad]; first by smt(ge2_l).
  split => [psadinf | /#].
  by apply implyFb; move: psadinf => /=; apply mem_empty.
wp 15 15.
by sim : (={is_valid, is_fresh}).
qed.


(* 
  Second step: 
  Reduce solving EUFRMA_FLXMSSTWES_NOPRF to solving M_EUF_GCMA for WOTS_TW_ES (without PRF),
  SM_DT_TCR_C for PKCO, and SM_DT_TCR_C for TCR.    
*)
lemma EUFRMA_FLXMSSTWES_NOPRF &m:
  l <= WOTS_TW.d =>
    Pr[EUF_RMA_FLXMSSTWES_NOPRF(A).main() @ &m : res]
    <=
    (w - 2)%r * 
  `|Pr[FC_UD.SM_DT_UD_C(R_SMDTUDC_Game23WOTSTWES(R_MEUFGCMAWOTSTWES_EUFRMAFLXMSSTWESNOPRF(A)), FC_UD.O_SMDTUD_Default, FC.O_THFC_Default).main(false) @ &m : res] - 
    Pr[FC_UD.SM_DT_UD_C(R_SMDTUDC_Game23WOTSTWES(R_MEUFGCMAWOTSTWES_EUFRMAFLXMSSTWESNOPRF(A)), FC_UD.O_SMDTUD_Default, FC.O_THFC_Default).main(true) @ &m : res]| 
    +
    Pr[FC_TCR.SM_DT_TCR_C(R_SMDTTCRC_Game34WOTSTWES(R_MEUFGCMAWOTSTWES_EUFRMAFLXMSSTWESNOPRF(A)), FC_TCR.O_SMDTTCR_Default, FC.O_THFC_Default).main() @ &m : res] 
    +
    Pr[FC_PRE.SM_DT_PRE_C(R_SMDTPREC_Game4WOTSTWES(R_MEUFGCMAWOTSTWES_EUFRMAFLXMSSTWESNOPRF(A)), FC_PRE.O_SMDTPRE_Default, FC.O_THFC_Default).main() @ &m : res]
    +
    Pr[PKCOC_TCR.SM_DT_TCR_C(R_SMDTTCRCPKCO_EUFRMAFLXMSSTWESNOPRF(A), PKCOC_TCR.O_SMDTTCR_Default, PKCOC.O_THFC_Default).main() @ &m : res]
    +
    Pr[TRHC_TCR.SM_DT_TCR_C(R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF(A), TRHC_TCR.O_SMDTTCR_Default, TRHC.O_THFC_Default).main() @ &m : res].
proof.
move=> gel_d.
move: (MEUFGCMA_WOTSTWES_NOPRF (R_MEUFGCMAWOTSTWES_EUFRMAFLXMSSTWESNOPRF(A)) _ _ &m).
+ move=> O OC Oll OCll. 
  proc => //=.
  while (true) (l - i).
  - move=> z.
    by wp; call(: true); rnd; skip; smt(dmsgFLXMSSTW_ll).
  by wp; call A_choose_ll; skip; smt(ge2_l). 
+ move=> O OC.
  proc => //=.
  wp; call A_forge_ll.
  while (true) (l - size msigl).
  - move=> z. 
    by wp; skip; smt(size_rcons).
  wp.
  while (true) (l - size leafl).
  - move=> z. 
    by wp; skip; smt(size_rcons).
  by wp; skip => /> /#.
move=> thm_defgcma_wotstw_noprf.
have ->:
  Pr[EUF_RMA_FLXMSSTWES_NOPRF(A).main() @ &m : res]
  =
  Pr[EUF_RMA_FLXMSSTWES_NOPRF_Conditions.main() @ &m : res].
+ byequiv => //.
  proc.
  seq 21 22 : (={is_valid, is_fresh}); first by sim.
  by wp; skip.
rewrite Pr[mu_split EUF_RMA_FLXMSSTWES_NOPRF_Conditions.valid_WOTSTWES] addrC.
rewrite Pr[mu_split EUF_RMA_FLXMSSTWES_NOPRF_Conditions.coll_pkco] addrC -2!andbA.
rewrite -addrA ler_add 2:ler_add. 
+ apply (ler_trans Pr[M_EUF_GCMA_WOTSTWES(R_MEUFGCMAWOTSTWES_EUFRMAFLXMSSTWESNOPRF(A), O_MEUFGCMA_WOTSTWES_NOPRF, FC.O_THFC_Default).main() @ &m : res]); last by apply thm_defgcma_wotstw_noprf.
  have ->:
    Pr[EUF_RMA_FLXMSSTWES_NOPRF_Conditions.main() @ &m : res /\ EUF_RMA_FLXMSSTWES_NOPRF_Conditions.valid_WOTSTWES]
    =
    Pr[EUF_RMA_FLXMSSTWES_NOPRF_Conditions_Mono.main() @ &m : res /\ EUF_RMA_FLXMSSTWES_NOPRF_Conditions_Mono.valid_WOTSTWES].
  - by byequiv EUF_RMA_FLXMSSTWES_NOPRF_Conditions_Mono_Validity.
  byequiv => //=.
  proc => //=.
  inline{2} 5.
  inline{2} 11.
  seq 12 17 : (   ={glob A, ps, root, pk, msigl, leafl}
               /\ ps{1} = O_MEUFGCMA_WOTSTWES.ps{2}
               /\ ad{1} = R_MEUFGCMAWOTSTWES_EUFRMAFLXMSSTWESNOPRF.ad{2}
               /\ ml{1} = R_MEUFGCMAWOTSTWES_EUFRMAFLXMSSTWESNOPRF.ml{2}
               /\ pkWOTSl{1} = R_MEUFGCMAWOTSTWES_EUFRMAFLXMSSTWESNOPRF.pkWOTSl{2}
               /\ sigWOTSl{1} = R_MEUFGCMAWOTSTWES_EUFRMAFLXMSSTWESNOPRF.sigWOTSl{2}
               /\ ml{1} = unzip1 msigl{1}
               /\ FC.O_THFC_Default.tws{2} = []
               /\ uniq_preffour (map (fun (q : adrs * msgWOTS * pkWOTS * sigWOTS) => q.`1) O_MEUFGCMA_WOTSTWES.qs{2})
               /\ size ml{1} = l
               /\ size leafl{1} = l
               /\ size pkWOTSl{1} = l
               /\ size sigWOTSl{1} = l
               /\ size O_MEUFGCMA_WOTSTWES.qs{2} = l
               /\ (forall (j : int), 0 <= j < l =>
                     nth witness O_MEUFGCMA_WOTSTWES.qs{2} j
                     =
                     (set_kpidx (set_typeidx ad{1} chtype) j,
                      nth witness ml{1} j,
                      DBLL.insubd (nth witness pkWOTSl{1} j),
                      DBLL.insubd (nth witness sigWOTSl{1} j)))).
  - while (   ={leafl, msigl}
           /\ ps{1} = ps0{2}
           /\ ad{1} = R_MEUFGCMAWOTSTWES_EUFRMAFLXMSSTWESNOPRF.ad{2}
           /\ ml{1} = R_MEUFGCMAWOTSTWES_EUFRMAFLXMSSTWESNOPRF.ml{2}
           /\ sigWOTSl{1} = R_MEUFGCMAWOTSTWES_EUFRMAFLXMSSTWESNOPRF.sigWOTSl{2}
           /\ size ml{1} = l
           /\ size leafl{1} = l
           /\ size sigWOTSl{1} = l
           /\ 0 <= size msigl{1} <= l
           /\ (forall (j : int), 0 <= j < size msigl{1} =>
                 nth witness ml{1} j
                 =
                 nth witness (unzip1 msigl{1}) j)).
    * by wp; skip => />; smt(size_rcons nth_rcons map_rcons size_map Index.insubdK).
    wp.
    while (   ={leafl}
           /\ ps{1} = ps0{2}
           /\ ad{1} = R_MEUFGCMAWOTSTWES_EUFRMAFLXMSSTWESNOPRF.ad{2}
           /\ pkWOTSl{1} = R_MEUFGCMAWOTSTWES_EUFRMAFLXMSSTWESNOPRF.pkWOTSl{2}
           /\ size pkWOTSl{1} = l
           /\ 0 <= size leafl{1} <= l).
    * by wp; skip => />; smt(size_rcons).
    wp.
    while (   ps{1} = O_MEUFGCMA_WOTSTWES.ps{2}
           /\ ad{1} = R_MEUFGCMAWOTSTWES_EUFRMAFLXMSSTWESNOPRF.ad{2}
           /\ ml{1} = R_MEUFGCMAWOTSTWES_EUFRMAFLXMSSTWESNOPRF.ml{2}
           /\ pkWOTSl{1} = R_MEUFGCMAWOTSTWES_EUFRMAFLXMSSTWESNOPRF.pkWOTSl{2}
           /\ sigWOTSl{1} = R_MEUFGCMAWOTSTWES_EUFRMAFLXMSSTWESNOPRF.sigWOTSl{2}
           /\ uniq_preffour (map (fun (q : adrs * msgWOTS * pkWOTS * sigWOTS) => q.`1) O_MEUFGCMA_WOTSTWES.qs{2})
           /\ size ml{1} = i0{2}
           /\ size ml{1} = size pkWOTSl{1}
           /\ size ml{1} = size sigWOTSl{1}
           /\ i0{2} = size R_MEUFGCMAWOTSTWES_EUFRMAFLXMSSTWESNOPRF.ml{2}
           /\ i0{2} = size R_MEUFGCMAWOTSTWES_EUFRMAFLXMSSTWESNOPRF.pkWOTSl{2}
           /\ i0{2} = size R_MEUFGCMAWOTSTWES_EUFRMAFLXMSSTWESNOPRF.sigWOTSl{2}
           /\ i0{2} = size O_MEUFGCMA_WOTSTWES.qs{2}
           /\ 0 <= size ml{1} <= l
           /\ (forall (j : int), 0 <= j < size O_MEUFGCMA_WOTSTWES.qs{2} =>
                 nth witness O_MEUFGCMA_WOTSTWES.qs{2} j
                 =
                 (set_kpidx (set_typeidx ad{1} chtype) j,
                  nth witness ml{1} j,
                  DBLL.insubd (nth witness pkWOTSl{1} j),
                  DBLL.insubd (nth witness sigWOTSl{1} j)))).
    * inline{2} 2.
      wp.
      while (   ={em}
             /\ ps{1} = O_MEUFGCMA_WOTSTWES.ps{2}
             /\ set_kpidx (set_typeidx ad{1} chtype) (size ml{1}) = ad0{2}
             /\ sigWOTS{1} = sig1{2}
             /\ skWOTS{1} = sk{2}
             /\ size skWOTS{1} = len
             /\ 0 <= size sigWOTS{1} <= len).
      + by wp; skip => />; smt(size_rcons).
      wp.
      while (   ps{1} = O_MEUFGCMA_WOTSTWES.ps{2}
             /\ set_kpidx (set_typeidx ad{1} chtype) (size ml{1}) = ad0{2}
             /\ pkWOTS{1} = pk0{2}
             /\ skWOTS{1} = sk{2}
             /\ size skWOTS{1} = len
             /\ 0 <= size pkWOTS{1} <= len).
      + by wp; skip => />; smt(size_rcons).
      swap{2} 5 -3.
      wp; rnd; rnd; skip => /> &2 uqpfqs eqszpkwl_szml eqszsigwl_szml eqszqs_szml ge0_szml _ qs_def ltl_szml m min skwl skwlin.
      split => [| pkw /lezNgt gelen_szpkw _ eqad eqlen_szskw ge0_szpkw lelen_szpkw]. 
      + split; last first.
        - split; last by smt(ge2_len).
          move: skwlin => @/ddgstoneliftl.
          by apply supp_dlist_size; smt(ge2_len).
        by rewrite ChainingAddress.insubdK 1:ischtype_setkpidx 1:ischtype_settypeidx.
      split => [| sigw /lezNgt gelen_szsigw _ _ lelen_szsigw]; first by smt(ge2_len).
      rewrite ?insubdK 1:ischtype_setkpidx 1:ischtype_settypeidx // 1,2:/# /=.
      rewrite -!andbA andbC -!andbA 8!andbA; split; first by smt(size_rcons).
      rewrite !andbA andbC -!andbA andbA; split; last by smt(size_rcons).
      split; last by smt(size_rcons nth_rcons).
      rewrite /uniq_preffour 2!map_rcons /= rcons_uniq /=.
      move: uqpfqs => @/uniq_preffour -> /=.
      rewrite mapP negb_exists /= => adrs.
      rewrite negb_and -implybE => /mapP [q] [qin /= ->].
      move: (qs_def (index q O_MEUFGCMA_WOTSTWES.qs{2}) _); first by smt(index_mem index_ge0).
      rewrite nth_index // => -> /= @/get_preffour /=. 
      do 3! (rewrite negb_and; right).
      by rewrite /set_kpidx ?getadrsK /= 1..4:-madrs_dom /valid_adidxs /=; smt(madidxs_valid val_w ge2_len ge2_l index_mem index_ge0).
    inline *; wp; call(: true); wp; rnd; rnd{2}; skip => /> *.
    do 3! (split => [| *]; first by smt(ge2_l)).
    by split; [apply (eq_from_nth witness); smt(size_map) | smt(ge2_l)].
  inline{2} 11; inline{2} 10; inline{2} 9; inline{2} 8; inline{2} 5.
  swap{1} [8..10] 4.
  wp.
  seq 3 3: (   #pre
            /\ ={idx'}
            /\ sigWOTS'{1} = val sigWOTS'{2} 
            /\ m'{1} = m'0{2} 
            /\ sig'{1} = sig'0{2}); first by wp; call(: true).
  sp; wp => /=.
  inline *; wp. 
  while (   ={em}
         /\ ps{1} = ps2{2}
         /\ set_kpidx (set_typeidx ad{1} chtype) (val idx'{1}) = ad1{2}
         /\ pkWOTS'{1} = pkWOTS3{2}
         /\ sigWOTS'{1} = val sig2{2}
         /\ 0 <= size pkWOTS'{1} <= len).
  - by wp; skip => />; smt(size_rcons). 
  wp; skip => /> &2 nthqs uqpfqs eql_szunz1 eql_szlfl eql_szpkwl eql_szsigwl eql_szqs qs_def.
  rewrite insubdK; move: (qs_def (val idx'{2}) _) (nthqs); 1,3: by rewrite valP.
  - move => /= // -> /= [#] -> _ _ _ /=.
    by rewrite ischtype_setkpidx 1:ischtype_settypeidx /valid_kpidx 1:valP.
  move => /= // -> /= [#] -> _ -> _ /=.
  split => [| ? ? ? ? mp_nmem]; first by smt(ge2_len).
  split; first by smt(size_ge0).
  split; first by smt(Index.valP).
  split; last by rewrite /disj_preffour hasPn.
  move: mp_nmem; apply contra => ->.
  move: (qs_def (val idx'{2}) _) nthqs; first by smt(Index.valP).
  by move=> -> [#] _ -> _ _; apply mem_nth; smt(size_map Index.valP).
+ byequiv => //=.
  proc; inline{2} *.
  wp.
  while (   ={ps, em, idx', sigWOTS', pkWOTS'}
         /\ ad{1} = R_SMDTTCRCPKCO_EUFRMAFLXMSSTWESNOPRF.ad{2}
         /\ 0 <= size pkWOTS'{1} <= len).
  - by wp; skip => />; smt(size_rcons).
  wp.
  call (: true).
  while (   ={ps, msigl}
         /\ ad{1} = R_SMDTTCRCPKCO_EUFRMAFLXMSSTWESNOPRF.ad{2}
         /\ skWOTSl{1} = R_SMDTTCRCPKCO_EUFRMAFLXMSSTWESNOPRF.skWOTSl{2}
         /\ leafl{1} = R_SMDTTCRCPKCO_EUFRMAFLXMSSTWESNOPRF.leafl{2}
         /\ 0 <= size msigl{1} <= l).
  - wp.
    while (   ={ps, em, sigWOTS, msigl}
           /\ ad{1} = R_SMDTTCRCPKCO_EUFRMAFLXMSSTWESNOPRF.ad{2}
           /\ skWOTS{1} = skWOTS0{2}
           /\ 0 <= size sigWOTS{1} <= len
           /\ 0 <= size msigl{1} < l).
    * by wp; skip => />; smt(size_rcons).
    by wp; rnd; skip => />; smt(ge2_len size_rcons).
  wp => /=.
  while (   ps{1} = PKCOC_TCR.O_SMDTTCR_Default.pp{2}
         /\ ps{1} = PKCOC.O_THFC_Default.pp{2}
         /\ ad{1} = R_SMDTTCRCPKCO_EUFRMAFLXMSSTWESNOPRF.ad{2}
         /\ skWOTSl{1} = R_SMDTTCRCPKCO_EUFRMAFLXMSSTWESNOPRF.skWOTSl{2}
         /\ map (flatten \o map DigestBlock.val) pkWOTSl{1} = unzip2 PKCOC_TCR.O_SMDTTCR_Default.ts{2}
         /\ leafl{1} = R_SMDTTCRCPKCO_EUFRMAFLXMSSTWESNOPRF.leafl{2}
         /\ (forall (i : int), 0 <= i < size PKCOC_TCR.O_SMDTTCR_Default.ts{2} =>
               (nth witness PKCOC_TCR.O_SMDTTCR_Default.ts{2} i).`1
               =
               set_kpidx (set_typeidx R_SMDTTCRCPKCO_EUFRMAFLXMSSTWESNOPRF.ad{2} pkcotype) i)
         /\ uniq (unzip1 PKCOC_TCR.O_SMDTTCR_Default.ts{2})
         /\ all is_chtype PKCOC.O_THFC_Default.tws{2}
         /\ PKCOC.disj_lists (unzip1 PKCOC_TCR.O_SMDTTCR_Default.ts{2}) PKCOC.O_THFC_Default.tws{2} 
         /\ size leafl{1} = size skWOTSl{1}
         /\ size leafl{1} = size pkWOTSl{1}
         /\ size leafl{1} = size PKCOC_TCR.O_SMDTTCR_Default.ts{2}
         /\ 0 <= size leafl{1} <= l).
  - wp => /=.
    while (   ={skWOTS, pkWOTS}
           /\ ps{1} = PKCOC.O_THFC_Default.pp{2}
           /\ ad{1} = R_SMDTTCRCPKCO_EUFRMAFLXMSSTWESNOPRF.ad{2}
           /\ size skWOTS{2} = len
           /\ size leafl{1} = size R_SMDTTCRCPKCO_EUFRMAFLXMSSTWESNOPRF.leafl{2}
           /\ size R_SMDTTCRCPKCO_EUFRMAFLXMSSTWESNOPRF.leafl{2} = size PKCOC_TCR.O_SMDTTCR_Default.ts{2}
            /\ (forall (i : int), 0 <= i < size PKCOC_TCR.O_SMDTTCR_Default.ts{2} =>
               (nth witness PKCOC_TCR.O_SMDTTCR_Default.ts{2} i).`1
               =
               set_kpidx (set_typeidx R_SMDTTCRCPKCO_EUFRMAFLXMSSTWESNOPRF.ad{2} pkcotype) i)
           /\ all is_chtype PKCOC.O_THFC_Default.tws{2}
           /\ PKCOC.disj_lists (unzip1 PKCOC_TCR.O_SMDTTCR_Default.ts{2}) PKCOC.O_THFC_Default.tws{2}
           /\ 0 <= size leafl{1} < l
           /\ 0 <= size pkWOTS{1} <= len).
    * wp => /=.
      while{2} (   pkWOTS_ele{2} 
                   = 
                   cf PKCOC.O_THFC_Default.pp{2} (set_chthidx (set_kpidx (set_typeidx R_SMDTTCRCPKCO_EUFRMAFLXMSSTWESNOPRF.ad{2} chtype) (size R_SMDTTCRCPKCO_EUFRMAFLXMSSTWESNOPRF.leafl{2})) (size pkWOTS{2})) 0 i0{2} (val (nth witness skWOTS{2} (size pkWOTS{2})))
                /\ all is_chtype PKCOC.O_THFC_Default.tws{2}
                /\ 0 <= i0{2} <= w - 1
                /\ 0 <= size R_SMDTTCRCPKCO_EUFRMAFLXMSSTWESNOPRF.leafl{2} < l
                /\ 0 <= size pkWOTS{2} < len)
               (w - 1 - i0{2}).
      + move=> _ z.
        wp; skip => /> &2 allch ge0_i _ ge0_szlfl ltl_szlfl ge0_szpk ltlen_szpk ltw1_i.
        rewrite -!andbA andbA; split; last by smt(val_w size_rcons).
        rewrite valP //=.
        split; last first. 
        - rewrite -cats1 all_cat /= allch /=.
          by rewrite ischtype_sethidx 1:ischtype_setchidx 1:ischtype_setkpidx 1:ischtype_settypeidx.
        case (i0{2} = 0) => [-> | neq0_i] /= @/cf.
        - rewrite ch0 // 1:ischtype_setchidx 1:ischtype_setkpidx 1:ischtype_settypeidx // 1:valP //.
          rewrite ch1 1:ischtype_setchidx 1:ischtype_setkpidx 1:ischtype_settypeidx // 1:valP // 1:/# -/f.
          by rewrite insubdK 1:valP.
        by rewrite eq_sym chS 1:ischtype_setchidx 1:ischtype_setkpidx 1:ischtype_settypeidx // 1:valP // /#.
      wp; skip => /> &1 &2 eqlen_szskw eqsz_lfl eqszlfl_ts ts_def allch djl_tstws ge0_szlfl ltl_szlfl ge0_szpkw _ ltlen_szpkw.      
      split => [@/cf | tws i].
      + rewrite ch0 1:ischtype_setchidx 1:ischtype_setkpidx 1:ischtype_settypeidx // 1:/# 1:valP //.
        by rewrite valKd /=; smt(val_w).
      split => [/# | /lezNgt gew1_i allchp *].
      rewrite -!andbA andbA; split; last by smt(size_rcons).
      split => [/# |].
      rewrite /disj_lists hasPn => adrs; apply contraL => adrsin.
      apply nth_nmem => j; rewrite size_map => rng_j.
      rewrite (nth_map witness witness _ _ _ rng_j) /= (ts_def j rng_j).
      move: adrsin; apply contraL => <-.
      move/allP: allchp => /(_ ((set_kpidx (set_typeidx R_SMDTTCRCPKCO_EUFRMAFLXMSSTWESNOPRF.ad{2} pkcotype) j))) /contra /(_ _) //.
      move: (ispkcotype_setkpidx (set_typeidx R_SMDTTCRCPKCO_EUFRMAFLXMSSTWESNOPRF.ad{2} pkcotype) j _ _).
      + by apply ispkcotype_settypeidx. 
      + by smt(ge2_l).
      by smt(dist_adrstypes).  
    wp; rnd; skip => /> &1 &2 rel_pkwl_ts ts_def uqts allch djl_ts_tws eqszlfl_szskwl eqszlfl_szpkwl eqszlfl_szts ge0_szlfl _ ltl_szlfl skw skwin.
    split => [| tws pkw /lezNgt gelen_szpkw _ eqlen_szskw allchp djl_ts_twsp ge0_szpkw lelen_szpkw].
    * split; last by smt(ge2_len).
      move: skwin => @/ddgstoneliftl; rewrite supp_dlist; first by smt(ge2_len).
      by move=> [-> /=].
    rewrite 3!andbA; split; last by smt(size_rcons).
    rewrite -!andbA; split.
    * by rewrite 2!map_rcons /=; congr.
    split; first by smt(size_rcons nth_rcons).
    split.
    * rewrite map_rcons rcons_uniq /= uqts /=.
      apply nth_nmem => i; rewrite size_map => rng_i.
      rewrite (nth_map witness witness) //= (ts_def i rng_i).
      by apply setkpidx_neq; smt(ispkcotype_settypeidx).
    rewrite map_rcons /= /disj_lists -cats1 has_cat /= negb_or. 
    move: djl_ts_twsp => @/disj_lists -> /=.
    move/allP: allchp => /(_ ((set_kpidx (set_typeidx R_SMDTTCRCPKCO_EUFRMAFLXMSSTWESNOPRF.ad{2} pkcotype) (size R_SMDTTCRCPKCO_EUFRMAFLXMSSTWESNOPRF.leafl{2})))) /contra /(_ _) //.
    move: (ispkcotype_setkpidx (set_typeidx R_SMDTTCRCPKCO_EUFRMAFLXMSSTWESNOPRF.ad{2} pkcotype) (size R_SMDTTCRCPKCO_EUFRMAFLXMSSTWESNOPRF.leafl{2}) _ _).
    + by apply ispkcotype_settypeidx. 
    + by smt(ge2_l).
    by smt(dist_adrstypes).  
  wp; call (: true); wp; rnd; skip => /> ps psin adrs.
  split => [| pkwl lfl skwl ts tws /lezNgt gel_szlfl _ rel_pkwl_ts ts_def uqts allch djl_ts_tws eqszlfl_szskwl eqszlfl_szpkwl eqszlfl_szts ge0_szlfl lel_szlfl]; first by smt(ge2_l).
  split => [| msigl /lezNgt gel_szmsigl _ _ lel_szmsigl msig]; first by smt(ge2_l).
  split => [| pkwp /lezNgt gelen_szpkwp _ _ lelen_szpkwp valap msig_nin neqnth_pkw coll coll_img]; first by smt(ge2_len).
  split => [/# |].
  have ->:
    (nth witness tws (val msig.`2.`1)).`2
    =
    flatten (map DigestBlock.val (nth witness pkwl (val msig.`2.`1))).
  - rewrite (: (nth witness tws (val msig.`2.`1)).`2 = (nth witness (unzip2 tws) (val msig.`2.`1))) 1:(nth_map witness witness); first 2 by smt(Index.valP).
    by rewrite -rel_pkwl_ts /(\o) (nth_map witness witness); first by smt(Index.valP).
  rewrite eq_sym coll /=; smt(Index.valP).
byequiv => //=.
proc.
inline{2} 5; inline{2} 4; inline{2} 3; inline{2} 2.
seq 6 11 : (   ={glob A}
            /\ ps{1} = pp{2}
            /\ ps{1} = TRHC.O_THFC_Default.pp{2}
            /\ ps{1} = TRHC_TCR.O_SMDTTCR_Default.pp{2}
            /\ ad{1} = R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.ad{2}
            /\ skWOTSl{1} = R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.skWOTSl{2}
            /\ leafl{1} = R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.leafl{2}
            /\ TRHC_TCR.O_SMDTTCR_Default.ts{2} = []
            /\ all (fun (adrs : adrs) => ! is_trhtype adrs) TRHC.O_THFC_Default.tws{2}
            /\ all (support ddgstblockl) skWOTSl{1}
            /\ all ((=) len \o size) pkWOTSl{1}
            /\ size skWOTSl{1} = l
            /\ size pkWOTSl{1} = l
            /\ size leafl{1} = l 
            /\ (forall (j n : int), 0 <= j < l => 0 <= n < len =>
                  nth witness (nth witness pkWOTSl{1} j) n
                  =
                  cf ps{1} (set_chthidx (set_kpidx (set_typeidx ad{1} chtype) j) n) 0 (w - 1) (val (nth witness (nth witness skWOTSl{1} j) n)))
            /\ (forall (j : int), 0 <= j < l =>
                  nth witness leafl{1} j
                  =
                  pkco ps{1} (set_kpidx (set_typeidx ad{1} pkcotype) j) (flatten (map DigestBlock.val (nth witness pkWOTSl{1} j))))).
+ while (   ={glob A} 
         /\ ps{1} = pp{2} 
         /\ ps{1} = TRHC.O_THFC_Default.pp{2} 
         /\ ps{1} = TRHC_TCR.O_SMDTTCR_Default.pp{2} 
         /\ ad{1} = R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.ad{2} 
         /\ skWOTSl{1} = R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.skWOTSl{2} 
         /\ leafl{1} = R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.leafl{2} 
         /\ TRHC_TCR.O_SMDTTCR_Default.ts{2} = [] 
         /\ all (fun (adrs : adrs) => ! is_trhtype adrs) TRHC.O_THFC_Default.tws{2} 
         /\ all (support ddgstblockl) skWOTSl{1} 
         /\ all ((=) len \o size) pkWOTSl{1} 
         /\ size skWOTSl{1} = size leafl{1} 
         /\ size pkWOTSl{1} = size leafl{1} 
         /\ 0 <= size leafl{1} <= l 
         /\ (forall (j n : int), 0 <= j && j < size pkWOTSl{1} => 0 <= n && n < len =>
               nth witness (nth witness pkWOTSl{1} j) n 
               =
               cf ps{1} (set_chthidx (set_kpidx (set_typeidx ad{1} chtype) j) n) 0
                 (w - 1) (val (nth witness (nth witness skWOTSl{1} j) n))) 
         /\ (forall (j : int),0 <= j && j < size leafl{1} =>
                nth witness leafl{1} j 
                =
                pkco ps{1} (set_kpidx (set_typeidx ad{1} pkcotype) j)
                  (flatten (map DigestBlock.val (nth witness pkWOTSl{1} j))))).
  - inline{2} 4.
    wp => /=.
    while (   ={pkWOTS}
           /\ ps{1} = pp{2} 
           /\ ps{1} = TRHC.O_THFC_Default.pp{2} 
           /\ ps{1} = TRHC_TCR.O_SMDTTCR_Default.pp{2} 
           /\ ad{1} = R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.ad{2}  
           /\ leafl{1} = R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.leafl{2}
           /\ skWOTS{1} = skWOTS0{2}
           /\ support ddgstblockl skWOTS{1}
           /\ all (fun (adrs : adrs) => ! is_trhtype adrs) TRHC.O_THFC_Default.tws{2}
           /\ 0 <= size leafl{1} < l
           /\ 0 <= size pkWOTS{1} <= len
           /\ (forall (j : int), 0 <= j < size pkWOTS{1} =>
                 nth witness pkWOTS{1} j
                 =
                 cf TRHC.O_THFC_Default.pp{2} (set_chthidx (set_kpidx (set_typeidx R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.ad{2} chtype) (size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.leafl{2})) j) 0 (w - 1) (val (nth witness skWOTS0{2} j)))).
    * wp => /=.
      while{2} (   pkWOTS_ele{2} = cf TRHC.O_THFC_Default.pp{2} (set_chthidx (set_kpidx (set_typeidx R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.ad{2} chtype) (size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.leafl{2})) (size pkWOTS{2})) 0 i0{2} (val (nth witness skWOTS0{2} (size pkWOTS{2})))
                /\ support ddgstblockl skWOTS0{2}
                /\ all (fun (adrs : adrs) => ! is_trhtype adrs) TRHC.O_THFC_Default.tws{2}
                /\ 0 <= size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.leafl{2} < l 
                /\ 0 <= size pkWOTS{2} < len
                /\ 0 <= i0{2} <= w - 1)
               (w - 1 - i0{2}).
      + move=> _ z.
        inline 1.
        wp; skip => /> &2 skwin alltrh ge0_szlfl ltl_szlfl ge0_szpkw ltlen_szpkw ge0_i0 _ ltw1_i0.
        rewrite -!andbA andbA; split => [| /#].
        split; last first.
        rewrite -cats1 all_cat alltrh /=; pose adrs := set_htbidx _ _.
        suff: is_chtype adrs; first by smt(dist_adrstypes). 
        by rewrite ischtype_sethidx // ischtype_setchidx // ischtype_setkpidx // ischtype_settypeidx.
        by rewrite valP -/f /cf (chS _ _ _ _ (i0{2} + 1)) 1:ischtype_setchidx // 1:ischtype_setkpidx // 1:ischtype_settypeidx // 1:valP // /#.  
      wp; skip => /> &2 skwin alltrh ge0_szlfl ltl_szlfl ge0_szpkw _ pkw_def ltlen_szpkw.
      rewrite /cf ch0 1:ischtype_setchidx // 1:ischtype_setkpidx // 1:ischtype_settypeidx // 1:valP //= valKd /=.
      split => [| tws i0]; first by smt(val_w ch0).
      split => [/# | /lezNgt gew1_i0 alltrhp ge0_i0 lew1_i0].
      rewrite -!andbA 3!andbA; split; last by smt(size_rcons nth_rcons).
      rewrite andbC -!andbA; split; last by smt(size_rcons nth_rcons).
      move=> n ge0_n; rewrite size_rcons => ltszpkwl1_n.
      rewrite nth_rcons; case (n < size pkWOTS{2}) => [ltszpkw_n /# | /lezNgt geszpkw_n].
      by rewrite (: n = size pkWOTS{2}) 1:/#.
    wp; rnd; skip => /> &1 &2 alltrh allsup alllen eqszlfl_szskwl eqszlfl_szpkwl ge0_szlfl _ pkwl_def lfl_def ltl_szlfl skw skwin.
    split => [| tws pkw /lezNgt gelen_szpkw _ alltrhp ge0_szpkw lelen_szpkw pkw_def]; first by smt(ge2_len).
    rewrite -!andbA 4!andbA; split; last first.
    * rewrite 2!andbA; split; first by smt(size_rcons).
      rewrite andbA; split; last by smt(size_rcons).
      by split; smt(size_rcons nth_rcons).
    have eq8n_szflpkw: size (flatten (map DigestBlock.val pkw)) = 8 * n * len.
    * rewrite size_flatten // StdBigop.Bigint.sumzE 2!StdBigop.Bigint.BIA.big_mapT /(\o).
      pose bi := StdBigop.Bigint.BIA.big _ _ _.
      rewrite (: bi = StdBigop.Bigint.BIA.big predT (fun (_ : dgstblock) => 8 * n) pkw).
      * by rewrite /bi &(StdBigop.Bigint.BIA.eq_big_seq) => x xin /=; rewrite valP.
      by rewrite StdBigop.Bigint.big_constz count_predT; congr => /#.
    rewrite -!andbA; split; last first.
    * rewrite -3!cats1 3!all_cat alltrhp allsup alllen /=.
      rewrite andbC -2!andbA andbA; split => [/# |].
      rewrite /(\o) size_rcons size_cat //=; split => [/# |].
      pose adrs := set_kpidx _ _.
      suff: is_pkcotype adrs; first by smt(dist_adrstypes). 
      by rewrite ispkcotype_setkpidx // ispkcotype_settypeidx.
    by congr; rewrite eq8n_szflpkw.
  wp; call (: true); wp; rnd; skip => /> *.
  split => [| *]; first by smt(ge2_l).
  rewrite 2!andbA; split; first by smt(ge2_l size_rcons).
  by split; smt(ge2_l size_rcons).
inline{2} 24; inline{2} 23; inline{2} 22; inline{2} 21; inline{2} 20.
wp => /=.
seq 5 10 : (   ={m', sig', ps}
            /\ ps{1} = pp{2}
            /\ ps{1} = TRHC.O_THFC_Default.pp{2}
            /\ ps{1} = TRHC_TCR.O_SMDTTCR_Default.pp{2}
            /\ ad{1} = R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.ad{2}
            /\ skWOTSl{1} = R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.skWOTSl{2}
            /\ leafl{1} = R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.leafl{2}
            /\ root{1} = val_bt_trh (list2tree leafl{1}) ps{1} (set_typeidx ad{1} trhtype) h 0
            /\ all (fun (adrs : adrs) => ! is_trhtype adrs) TRHC.O_THFC_Default.tws{2}
            /\ all (support ddgstblockl) skWOTSl{1}
            /\ all ((=) len \o size) pkWOTSl{1}
            /\ TRHC.disj_lists (unzip1 TRHC_TCR.O_SMDTTCR_Default.ts{2}) TRHC.O_THFC_Default.tws{2}
            /\ unzip1 TRHC_TCR.O_SMDTTCR_Default.ts{2} = flatten R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.adrsll{2}
            /\ unzip2 TRHC_TCR.O_SMDTTCR_Default.ts{2} = flatten R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.inpll{2}
            /\ size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2} = h
            /\ size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.adrsll{2} = h 
            /\ size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.inpll{2} = h
            /\ size skWOTSl{1} = l
            /\ size pkWOTSl{1} = l
            /\ size leafl{1} = l 
            /\ (forall (j n : int), 0 <= j < l => 0 <= n < len =>
                  nth witness (nth witness pkWOTSl{1} j) n
                  =
                  cf ps{1} (set_chthidx (set_kpidx (set_typeidx ad{1} chtype) j) n) 0 (w - 1) (val (nth witness (nth witness skWOTSl{1} j) n)))
            /\ (forall (j : int), 0 <= j < l =>
                  nth witness leafl{1} j
                  =
                  pkco ps{1} (set_kpidx (set_typeidx ad{1} pkcotype) j) (flatten (map DigestBlock.val (nth witness pkWOTSl{1} j))))
            /\ (forall (j : int), 0 <= j < size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.adrsll{2} =>
                  size (nth witness R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.adrsll{2} j) 
                  = 
                  size (nth witness R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2} j))
            /\ (forall (j : int), 0 <= j < size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.inpll{2} =>
                  size (nth witness R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.inpll{2} j) 
                  = 
                  size (nth witness R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2} j))
            /\ (forall (j : int), 0 <= j < size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2} =>
                  size (nth witness R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2} j) = 2 ^ (h - j - 1))
            /\ (forall (n : int), 1 <= size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2} => 0 <= n < 2 ^ (h - 1) =>
                  nth witness (nth witness R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2} 0) n
                  =
                  trh TRHC_TCR.O_SMDTTCR_Default.pp{2} (set_thtbidx (set_typeidx R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.ad{2} trhtype) 1 n) (val (nth witness R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.leafl{2} (2 * n)) ++ val (nth witness R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.leafl{2} (2 * n + 1))))
            /\ (forall (j n : int), 1 <= j < size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2} => 0 <= n < 2 ^ (h - j - 1) =>
                  nth witness (nth witness R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2} j) n
                  =
                  trh TRHC_TCR.O_SMDTTCR_Default.pp{2} (set_thtbidx (set_typeidx R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.ad{2} trhtype) (j + 1) n) (val (nth witness (nth witness R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2} (j - 1)) (2 * n)) ++ val (nth witness (nth witness R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2} (j - 1)) (2 * n + 1))))
            /\ (forall (j n : int), 0 <= j < size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.adrsll{2} => 0 <= n < 2 ^ (h - j - 1) =>
                  nth witness (nth witness R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.adrsll{2} j) n
                  =
                  set_thtbidx (set_typeidx R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.ad{2} trhtype) (j + 1) n) 
            /\ (forall (j n : int), 1 <= size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.inpll{2} => 0 <= n < 2 ^ (h - 1) =>
                  nth witness (nth witness R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.inpll{2} 0) n
                  =
                  val (nth witness R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.leafl{2} (2 * n)) ++ val (nth witness R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.leafl{2} (2 * n + 1))) 
            /\ (forall (j n : int), 1 <= j < size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.inpll{2} => 0 <= n < 2 ^ (h - j - 1) =>
                  nth witness (nth witness R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.inpll{2} j) n
                  =
                  val (nth witness (nth witness R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2} (j - 1)) (2 * n)) ++ val (nth witness (nth witness R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2} (j - 1)) (2 * n + 1)))
            /\ (forall (j n : int), 0 <= j < size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2} => 0 <= n < 2 ^ (h - j - 1) =>
                  nth witness (nth witness R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2} j) n
                  =
                  val_bt_trh (oget (sub_bt (list2tree R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.leafl{2}) (rev (int2bs (h - j - 1) n)))) TRHC_TCR.O_SMDTTCR_Default.pp{2} (set_typeidx R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.ad{2} trhtype) (j + 1) n)).          
+ call (: true).
  while (   ={ps, msigl}
         /\ ad{1} = R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.ad{2}
         /\ skWOTSl{1} = R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.skWOTSl{2} 
         /\ leafl{1} = R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.leafl{2}
         /\ 0 <= size msigl{2} <= l).
  - wp.
    while (   ={ps, em, skWOTS, sigWOTS, msigl}
           /\ ad{1} = R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.ad{2}
           /\ 0 <= size msigl{1} < l
           /\ 0 <= size sigWOTS{1} <= len).
    * by wp; skip => />; smt(size_rcons).
    by wp; rnd; skip => />; smt(ge2_len size_rcons).
  wp => /=.  
  while{2} (   TRHC.disj_lists (unzip1 TRHC_TCR.O_SMDTTCR_Default.ts{2}) TRHC.O_THFC_Default.tws{2}
            /\ all (fun (adrs : adrs) => ! is_trhtype adrs) TRHC.O_THFC_Default.tws{2}
            /\ unzip1 TRHC_TCR.O_SMDTTCR_Default.ts{2} = flatten R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.adrsll{2}
            /\ unzip2 TRHC_TCR.O_SMDTTCR_Default.ts{2} = flatten R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.inpll{2}
            /\ size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.adrsll{2} = size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2}
            /\ size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.inpll{2} = size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2}
            /\ size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.leafl{2} = l
            /\ 0 <= size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2} <= h
            /\ (forall (j : int), 0 <= j < size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.adrsll{2} =>
                  size (nth witness R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.adrsll{2} j) 
                  = 
                  size (nth witness R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2} j))
            /\ (forall (j : int), 0 <= j < size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.inpll{2} =>
                  size (nth witness R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.inpll{2} j) 
                  = 
                  size (nth witness R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2} j))
            /\ (forall (j : int), 0 <= j < size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2} =>
                  size (nth witness R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2} j) = 2 ^ (h - j - 1))
            /\ (forall (n : int), 1 <= size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2} => 0 <= n < 2 ^ (h - 1) =>
                  nth witness (nth witness R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2} 0) n
                  =
                  trh TRHC_TCR.O_SMDTTCR_Default.pp{2} (set_thtbidx (set_typeidx R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.ad{2} trhtype) 1 n) (val (nth witness R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.leafl{2} (2 * n)) ++ val (nth witness R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.leafl{2} (2 * n + 1))))
            /\ (forall (j n : int), 1 <= j < size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2} => 0 <= n < 2 ^ (h - j - 1) =>
                  nth witness (nth witness R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2} j) n
                  =
                  trh TRHC_TCR.O_SMDTTCR_Default.pp{2} (set_thtbidx (set_typeidx R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.ad{2} trhtype) (j + 1) n) (val (nth witness (nth witness R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2} (j - 1)) (2 * n)) ++ val (nth witness (nth witness R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2} (j - 1)) (2 * n + 1))))
            /\ (forall (j n : int), 0 <= j < size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.adrsll{2} => 0 <= n < 2 ^ (h - j - 1) =>
                  nth witness (nth witness R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.adrsll{2} j) n
                  =
                  set_thtbidx (set_typeidx R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.ad{2} trhtype) (j + 1) n) 
            /\ (forall (j n : int), 1 <= size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.inpll{2} => 0 <= n < 2 ^ (h - 1) =>
                  nth witness (nth witness R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.inpll{2} 0) n
                  =
                  val (nth witness R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.leafl{2} (2 * n)) ++ val (nth witness R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.leafl{2} (2 * n + 1))) 
            /\ (forall (j n : int), 1 <= j < size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.inpll{2} => 0 <= n < 2 ^ (h - j - 1) =>
                  nth witness (nth witness R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.inpll{2} j) n
                  =
                  val (nth witness (nth witness R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2} (j - 1)) (2 * n)) ++ val (nth witness (nth witness R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2} (j - 1)) (2 * n + 1)))
            /\ (forall (j n : int), 0 <= j < size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2} => 0 <= n < 2 ^ (h - j - 1) =>
                  nth witness (nth witness R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2} j) n
                  =
                  val_bt_trh (oget (sub_bt (list2tree R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.leafl{2}) (rev (int2bs (h - j - 1) n)))) TRHC_TCR.O_SMDTTCR_Default.pp{2} (set_typeidx R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.ad{2} trhtype) (j + 1) n))
           (h - size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2}).
  - move=> _ z.
    inline *; wp => /=.
    while (   unzip1 TRHC_TCR.O_SMDTTCR_Default.ts = flatten (rcons R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.adrsll adrsl)
           /\ unzip2 TRHC_TCR.O_SMDTTCR_Default.ts = flatten (rcons R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.inpll inpl)
           /\ size adrsl = size nodel
           /\ size inpl = size nodel
           /\ 0 <= size nodel <= 2 ^ (h - size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell - 1)
           /\ (forall (j : int), 0 <= j < size adrsl =>
                 nth witness adrsl j
                 =
                 set_thtbidx (set_typeidx R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.ad trhtype) (size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell + 1) j)
           /\ (forall (j : int), 0 <= j < size inpl =>
                 nth witness inpl j
                 =
                 val (nth witness nodel' (2 * j)) ++ val (nth witness nodel' (2 * j + 1)))
           /\ (forall (j : int), 0 <= j < size nodel =>
                 nth witness nodel j
                 =
                 trh TRHC_TCR.O_SMDTTCR_Default.pp (nth witness adrsl j) (nth witness inpl j)))   
          (2 ^ (h - size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell - 1) - size nodel).
    * move=> z'.
      wp; skip => /> &2 equnz1ts_fladl equnz2ts_flinpl eqszad_sznl eqszinpl_sznl ge0_dznl _ adl_def inpl_def nl_def lt2h1_sznl.
      rewrite -!andbA andbA; split; last by smt(size_rcons nth_rcons).
      split; first by rewrite map_rcons /= equnz1ts_fladl ?flatten_rcons rcons_cat.
      by rewrite map_rcons /= equnz2ts_flinpl ?flatten_rcons rcons_cat.
    wp; skip => /> &2 djl_ts_tws alltrh equnz1ts_flinpl equnz2ts_fladl eqszadl_sznl eqszinpl_sznl eql_szlfl ge0_sznl _ eqsznthadl_nl eqsznthinpl_nl sznthnl h0nl_def hanl_def adl_def h0inpl_def hainpl_def nl_valbt lth_sznl.
    split => [| ts adl inpl nodel].
    * rewrite 2!andbA; split; last by smt().
      by rewrite 2!flatten_rcons 2!cats0 equnz1ts_flinpl equnz2ts_fladl expr_ge0.
    split => [/# | /lezNgt ge2h_sznl equnz1ts_flrcadl equnz2ts_flrcinpl eqszadl_nlp eqszinpl_nlp _ le2h_sznl adlp_def inplp_def nlp_def].
    split; last by smt(size_rcons).
    rewrite -!andbA 2!andbA; split.
    * rewrite -!andbA; split; last by smt(size_rcons).
      rewrite equnz1ts_flrcadl /disj_lists hasPn => adrs /flattenP [adrsl []].
      rewrite mem_rcons /= => -[-> adin| adlin adin]; apply nth_nmem => i rng_i.
      + move/(nth_index witness): (adin) => <-.
        rewrite adlp_def; first by smt(index_ge0 index_mem).
        move/(all_nthP _ _ witness): alltrh => /(_ i rng_i) /= ntrhnth.
        pose adset := set_thtbidx _ _ _. 
        rewrite eqad_eqadidxstup; suff /#: is_trhtype adset.
        rewrite /adset istrhtype_setthtbidx 1:istrhtype_settypeidx 1:/#.
        rewrite /valid_tbidx andaE; smt(index_ge0 index_mem).
        move/(nth_index witness): (adlin); move/(nth_index witness): (adin) => <- <-.
        rewrite adl_def; first by smt(index_ge0 index_mem).
        split => [| _]; first by smt(index_ge0).
        by rewrite -sznthnl 2:-eqsznthadl_nl; smt(index_ge0 index_mem nth_index).
      move/(all_nthP _ _ witness): alltrh => /(_ i rng_i) /= ntrhnth.
      pose adset := set_thtbidx _ _ _; suff /#: is_trhtype adset.
      by rewrite /adset istrhtype_setthtbidx 1:istrhtype_settypeidx; smt(index_ge0 index_mem nth_index).
    rewrite 4!andbA; split; first by smt(size_rcons nth_rcons).
    split => [n | ].
    * rewrite size_rcons => ge1_sz1 ge0_n lt2h1_n.
      rewrite nth_rcons; case (size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2} = 0) => [eq0_sz | neq0_sz].
      + rewrite eq0_sz => /=; rewrite nlp_def 1:/# adlp_def 1:/# inplp_def 1:/#.
        by move/size_eq0: eq0_sz => ->.
      by rewrite (: 0 < size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2}) /#.
    split => [j n ge1_j + ge0_n lt2hj1_n |].
    * rewrite size_rcons=> ltsz1_j; rewrite ?nth_rcons.
      case (j < size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2}) => [ltsz_j /# | /lezNgt gesz_j].
      rewrite (: j = size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2}) 1:/# /=.
      rewrite (: size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2} - 1 < size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2}) 1:/# /=.
      rewrite nlp_def 1:/# adlp_def 1:/# inplp_def 1:/#.
      rewrite (nth_change_dfl R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.leafl{2} witness) 1:/#.
      by rewrite nth_last.
    split => [j n ge1_j + ge0_n lt2hj1_n |].
    * rewrite size_rcons=> ltsz1_j; rewrite ?nth_rcons.
      case (j < size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.adrsll{2}) => [ltsz_j /# | /lezNgt gesz_j].
      rewrite (: j = size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.adrsll{2}) 1:/# /=.
      by rewrite adlp_def /#.
    split => [n | ].
    * rewrite size_rcons => ge1_sz1 ge0_n lt2h1_n.
      rewrite nth_rcons; case (size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.inpll{2} = 0) => [eq0_sz | neq0_sz].
      + rewrite eq0_sz => /=; rewrite inplp_def 1:/#.
        by move: eq0_sz; rewrite eqszinpl_sznl size_eq0 => ->.
      by rewrite (: 0 < size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.inpll{2}) /#.
    split => [j n ge1_j + ge0_n lt2hj1_n |].
    * rewrite size_rcons=> ltsz1_j; rewrite ?nth_rcons.
      rewrite (: size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2} = size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.inpll{2}) 1:/#.
      case (j < size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.inpll{2}) => [ltsz_j /# | /lezNgt gesz_j].
      rewrite (: j = size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.inpll{2}) 1:/# /=.
      rewrite (: size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.inpll{2} - 1 < size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.inpll{2}) 1:/# /=.
      rewrite inplp_def 1:/# -nth_last.
      by rewrite (nth_change_dfl R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.leafl{2} witness) /#.
    move=> j n ge0_j + ge0_n lt2hj1_n.
    rewrite size_rcons=> ltsz1_j; rewrite nth_rcons.
    case (j < size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2}) => [ltsz_j /# | /lezNgt gesz_j].
    rewrite (: j = size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2}) 1:/# /=.
    rewrite nlp_def 1:/# adlp_def 1:/# inplp_def 1:/#.
    rewrite (: h - size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2} - 1 = h - (size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2} + 1)) 1:/#.
    rewrite (: h = height (list2tree R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.leafl{2})).
    * by rewrite (list2tree_height _ h) //; smt(ge1_h).
    rewrite valbttrh_subbt 1:istrhtype_settypeidx.
    * by rewrite (list2tree_fullybalanced _ h) //; smt(ge1_h).
    * by rewrite (list2tree_height _ h) //; smt(size_ge0 ge1_h).
    case (size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2} = 0) => [eq0_sz | neq0_sz].
    * move/size_eq0: (eq0_sz) => -> /=.
      rewrite ?subbt_list2tree_idx 1,4:ge0_height 1,3:(list2tree_height _ h) //; 1,3: by smt(ge1_h).
      + split => [/# | _].
        rewrite eql_szlfl /l (: h = h - 1 + 1) 2:exprD_nneg //; first smt(ge1_h).
        by rewrite mulzC expr1 /#.
      split => [/# | _].
      rewrite eql_szlfl /l (: h = h - 1 + 1) 2:exprD_nneg //; first smt(ge1_h).
      by rewrite mulzC expr1 /#.
    have eqsz_j: size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2} = j by smt().
    rewrite -nth_last -(nth_change_dfl R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.leafl{2} witness) 1:/# ?nl_valbt 1,3:/#.
    * split => [/# | _].
      rewrite eqsz_j (: h - (j - 1) - 1 = h - j - 1 + 1) 1:/# exprD_nneg //; first smt(ge1_h).
      by rewrite mulzC expr1 /#.
    * split => [/# | _].
      rewrite eqsz_j (: h - (j - 1) - 1 = h - j - 1 + 1) 1:/# exprD_nneg //; first smt(ge1_h).
      by rewrite mulzC expr1 /#.
    rewrite (: h = height (list2tree R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.leafl{2})) 2:/#.
    by rewrite (list2tree_height _ h) //; smt(ge1_h).
  wp; skip => /> &1 &2 alltrh allsup allen eql_szskwl eql_szpkwl eql_szlfl pkwl_def lfl_def. 
  split=> [| adl inpl nl ts]; first by smt(ge1_h).
  split=> [/# | /lezNgt geh_sznl djl_ts_tws equnz1ts_adl equnz2ts_inpl eqszadl_sznl eqszinpl_sznl _ leh_sznl eqsznthadl_nl eqsznthinpl_nl sznthnl h0nl_def hanl_def adl_def h0inpl_def hainpl_def nl_valbt].
  split => [| msigl /lezNgt gel_szmsigl _ _ lel_szmsigl]; first by smt(ge2_l).
  split => [| /#].
  rewrite nl_valbt 2:expr_gt0 //; first by smt(ge1_h).
  rewrite (: h - (h - 1) - 1 = 0) 1:/# int2bs0s /rev /=.
  by case (list2tree R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.leafl{2}).
while (   ={ps, em, idx', sigWOTS', pkWOTS'}
       /\ ad{1} = R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.ad{2}
       /\ 0 <= val idx'{1} < l
       /\ 0 <= size pkWOTS'{1} <= len
       /\ (forall (j : int), 0 <= j < size pkWOTS'{1} =>
             nth witness pkWOTS'{1} j
             =
             cf ps{1} (set_chthidx (set_kpidx (set_typeidx ad{1} chtype) (val idx'{1})) j) (BaseW.val em{1}.[j]) (w - 1 - BaseW.val em{1}.[j]) (val (nth witness sigWOTS'{1} j)))).
+ wp; skip => /> &2 ge0_idxp ltl_idxp ge0_szpkwp _ valpkwp ltlen_szpkwp.
  split => [| n ge0_n]; first by smt(size_rcons).
  rewrite size_rcons=> ltszpkw1_n; rewrite nth_rcons.
  case (n < size pkWOTS'{2}) => [/# | /lezNgt geszpkw_n].
  by rewrite (: n = size pkWOTS'{2}) 1:/#.
wp; skip => /> &1 &2 alltrh allsup allen djl_ts_tws equnz1ts_fladl equnz2ts_flinpl eqh_sznl eqh_szadl eqh_szinpl eql_szskwl eql_szpkwl eql_szlfl pkwl_def lfl_def eqsznthadl_nl eqsznthinpl_nl sznthnl h0nl_def hanl_def adl_def h0inpl_def hainpl_def nl_valbt.
split => [| pkwp /lezNgt gelen_szpkwp _ ge0_vs lel_vs ge0_szpkwp lelen_szpkwp pkwp_def valaptrh nmemunz1msigl_m neq_pkws]; first by smt(ge2_len Index.valP).
move/negb_and => /= [ | neq_leafs].
+ apply contraLR => _.
  move: neq_pkws; apply contra => eqfl.
  have: injective (map DigestBlock.val) by apply /inj_map /DigestBlock.val_inj.
  apply; apply eq_from_flatten_nth => //.
  - rewrite 2!size_map; move/(all_nthP _ _ witness): allen => /(_ (val sig'{2}.`1) _).
    * by rewrite eql_szpkwl.
    by rewrite /(\o) => <- /#.
  move=> i; rewrite size_map => rng_i; rewrite ?(nth_map witness witness) //.
  move/(all_nthP _ _ witness): allen => /(_ (val sig'{2}.`1) _); first 2 by smt().
  by rewrite 2!valP.
split.
+ split => [| _]; first by rewrite size_ge0.
  rewrite (: size TRHC_TCR.O_SMDTTCR_Default.ts{2} = size (unzip1 TRHC_TCR.O_SMDTTCR_Default.ts{2})); first by rewrite size_map.
  rewrite equnz1ts_fladl (: size (flatten R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.adrsll{2}) = size (flatten R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2})).
  - rewrite 2!size_flatten 2!StdBigop.Bigint.sumzE 2!StdBigop.Bigint.BIA.big_mapT /(\o) /=.
    rewrite (StdBigop.Bigint.BIA.big_nth witness) /(\o) /predT /= -/predT.
    rewrite eq_sym (StdBigop.Bigint.BIA.big_nth witness) /(\o) /predT /= -/predT.
    rewrite eqh_sznl eqh_szadl.
    by apply StdBigop.Bigint.BIA.eq_big_int => /#.
  rewrite (: size (flatten R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2}) = size (flatten (rev R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2}))). 
  - rewrite 2!size_flatten 2!StdBigop.Bigint.sumzE 2!StdBigop.Bigint.BIA.big_mapT /(\o) /=.
    by rewrite &(StdBigop.Bigint.BIA.eq_big_perm) perm_eq_rev.
  have:
    forall (j : int), 0 <= j < h => size (nth witness (rev R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2}) j) = 2 ^ j.
  - by move=> j rng_j; move: (sznthnl j _); rewrite ?nth_rev /#.
  rewrite /l size_flatten StdBigop.Bigint.sumzE StdBigop.Bigint.BIA.big_mapT /(\o) /=. 
  rewrite (StdBigop.Bigint.BIA.big_nth witness) /(\o) /predT /= -/predT (: size (rev R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.nodell{2}) = h) 1:size_rev 1://.
  case (0 <= h); last by smt(ge1_h).
  elim: h => //=; first by rewrite expr0 StdBigop.Bigint.BIA.big_geq.
  move=> h' ge0_hp ih sznth.
  rewrite StdBigop.Bigint.BIA.big_int_recr //= (: 2 ^ (h' + 1) - 1 = (2 ^ h' - 1) + 2 ^ h').
  - by rewrite exprD_nneg // expr1 /#. 
  by rewrite ler_add 1:ih /#.  
split.
+ rewrite equnz1ts_fladl uniq_flatten 1:-(all_nthP _ _ witness).
  - move=> i rng_i.
    apply nth_uniq => j n rng_j rng_n neqn_j.
    rewrite adl_def 3:adl_def // 1,2:/#.
    by apply setthtbidx_neqtbidx => //; 1,2: apply istrhtype_settypeidx; smt().
  - move=> x y ^ ^ + + /(nth_index witness) xnthind ^ ^ + + /(nth_index witness) ynthind.
    rewrite -{1}index_mem => ltszadl_indx xin; rewrite -{1}index_mem => ltszadl_indy yin.
    apply contraLR => neqy_x; rewrite hasPn => z ^ ^ + + /(nth_index witness) znthind. 
    rewrite -{1}index_mem => ltszadl_indz zin.
    rewrite nth_nmem // -xnthind -znthind -ynthind => i rng_i.
    do 2! (rewrite adl_def; first 2 by smt(index_ge0)).
    by apply setthtbidx_neqthidx => //; 1,2: apply istrhtype_settypeidx; smt(index_ge0).
  apply size_nth_uniq => i j rng_i rng_j neqj_i.
  rewrite eqsznthadl_nl // eqsznthadl_nl // sznthnl 1:/# sznthnl 1:/#.
  case (i < j) => [ltj_i | /lezNgt [lti_j | /#]].
  - suff: 2 ^ (h - j - 1) < 2 ^ (h - i - 1); first by smt().
    by apply gt_exprsbde => // /#.
  suff: 2 ^ (h - i - 1) < 2 ^ (h - j - 1); first by smt().
  by apply gt_exprsbde => // /#.
move: (extract_coll_bt_ap_Ph0
        (list2tree R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.leafl{2})
         sig'{2}.`3
         sig'{2}.`1
        (pkco TRHC_TCR.O_SMDTTCR_Default.pp{2} (set_kpidx (set_typeidx R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.ad{2} pkcotype) (val sig'{2}.`1)) (flatten (map DigestBlock.val pkwp)))
        (pkco TRHC_TCR.O_SMDTTCR_Default.pp{2} (set_kpidx (set_typeidx R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.ad{2} pkcotype) (val sig'{2}.`1)) (flatten (map DigestBlock.val ((nth witness pkWOTSl{1} (val sig'{2}.`1))))))
         TRHC_TCR.O_SMDTTCR_Default.pp{2}
        (set_typeidx R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.ad{2} trhtype)).
rewrite istrhtype_settypeidx /= => /(_ _ _ _ _ _); 1,4: smt().
+ by apply (list2tree_fullybalanced _ h); smt(ge1_h).
+ by apply (list2tree_height _ h); smt(ge1_h).
+ by rewrite list2tree_lvb 4:(onth_nth witness) 5:lfl_def; smt(ge1_h).
pose extr_coll := extract_coll_bt_ap _ _ _ _ _ _ _ _. 
move=> -[x x' i j] [#] coll_val.
rewrite coll_val oget_some /= => eq8n2_szx eq8n2_szxp xval vali vali1 valij vali12j vali12j1 ge1_i leh_i jval neqx_xp eq_trhxxp.
have nthxval:
  x = (nth witness TRHC_TCR.O_SMDTTCR_Default.ts{2} (sumz (map size (take (i - 1) R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.inpll{2})) + j)).`2.
+ have ->:
    (nth witness TRHC_TCR.O_SMDTTCR_Default.ts{2} (sumz (map size (take (i - 1) R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.inpll{2})) + j)).`2
    =
    nth witness (unzip2 TRHC_TCR.O_SMDTTCR_Default.ts{2}) (sumz (map size (take (i - 1) R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.inpll{2})) + j).
  - rewrite (nth_map witness) => //=. 
    split => [| _]; first by rewrite addz_ge0 2:/# sumz_ge0 allP => xt /mapP [? [? ->]]; rewrite size_ge0.
    rewrite (: size TRHC_TCR.O_SMDTTCR_Default.ts{2} = size (unzip2 TRHC_TCR.O_SMDTTCR_Default.ts{2})) 1:size_map // -size_flatten equnz2ts_flinpl.
    suff /#:
      size (flatten (take (i - 1) R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.inpll{2})) + j < size (flatten (take i R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.inpll{2})) <= size (flatten R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.inpll{2}).
    split=> [| _].
    * rewrite {2}(: i = i - 1 + 1) // (take_nth witness) 1:/# flatten_rcons size_cat.
      by rewrite ltz_add2l /#.
    rewrite -{2}(cat_take_drop i) flatten_cat size_cat.
    by rewrite lez_addl size_ge0.
  rewrite xval equnz2ts_flinpl nth_flatten 1,2:/#.
  case (i = 1) => [eq1_i | neq1_i].
  - rewrite eq1_i /= h0inpl_def 1,2:/#.
    by congr; rewrite subbt_list2tree_idx 1,2,3:/# oget_some.
  rewrite hainpl_def 1,2:/# /=.
  by congr; rewrite nl_valbt /#.
split; first by rewrite -nthxval.
have -> //=:
  (nth witness TRHC_TCR.O_SMDTTCR_Default.ts{2} (sumz (map size (take (i - 1) R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.inpll{2})) + j)).`1
  =
  nth witness (unzip1 TRHC_TCR.O_SMDTTCR_Default.ts{2}) (sumz (map size (take (i - 1) R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.adrsll{2})) + j).
+ rewrite (nth_map witness) => //=. 
  - split => [| _]; first by rewrite addz_ge0 2:/# sumz_ge0 allP => xt /mapP [? [? ->]]; rewrite size_ge0.
    rewrite (: size TRHC_TCR.O_SMDTTCR_Default.ts{2} = size (unzip1 TRHC_TCR.O_SMDTTCR_Default.ts{2})) 1:size_map // -size_flatten equnz1ts_fladl.
    suff /#:
      size (flatten (take (i - 1) R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.adrsll{2})) + j < size (flatten (take i R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.adrsll{2})) <= size (flatten R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.adrsll{2}).
    split=> [| _].
    * rewrite {2}(: i = i - 1 + 1) // (take_nth witness) 1:/# flatten_rcons size_cat.
      by rewrite ltz_add2l /#.
    rewrite -{2}(cat_take_drop i) flatten_cat size_cat.
    by rewrite lez_addl size_ge0.
  do 4! congr. 
  apply (eq_from_nth witness); first by rewrite 2!size_map ?size_take /#. 
  rewrite size_map size_take 1:/#.
  rewrite (: i - 1 < size R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF.inpll{2}) 1:/# /= => k k_rng.
  rewrite ?(nth_map witness) ?size_take 1..4:/#.
  by rewrite ?nth_take // /#.
rewrite equnz1ts_fladl nth_flatten 1,2:/# ?adl_def 1,2:/# /=.
by rewrite -nthxval.
qed.  


(* Security Theorem *)
lemma EUFRMA_FLXMSSTWES &m :
  l <= WOTS_TW.d =>
    Pr[EUF_RMA_FLXMSSTWES(A).main() @ &m : res]
    <=
  `|Pr[PRF_SK_PRF.PRF(R_PRF_FLXMSSTWESInlineNOPRF(A), PRF_SK_PRF.O_PRF_Default).main(false) @ &m : res] - 
    Pr[PRF_SK_PRF.PRF(R_PRF_FLXMSSTWESInlineNOPRF(A), PRF_SK_PRF.O_PRF_Default).main(true) @ &m : res]|
    +
    (w - 2)%r * 
  `|Pr[FC_UD.SM_DT_UD_C(R_SMDTUDC_Game23WOTSTWES(R_MEUFGCMAWOTSTWES_EUFRMAFLXMSSTWESNOPRF(A)), FC_UD.O_SMDTUD_Default, FC.O_THFC_Default).main(false) @ &m : res] - 
    Pr[FC_UD.SM_DT_UD_C(R_SMDTUDC_Game23WOTSTWES(R_MEUFGCMAWOTSTWES_EUFRMAFLXMSSTWESNOPRF(A)), FC_UD.O_SMDTUD_Default, FC.O_THFC_Default).main(true) @ &m : res]| 
    +
    Pr[FC_TCR.SM_DT_TCR_C(R_SMDTTCRC_Game34WOTSTWES(R_MEUFGCMAWOTSTWES_EUFRMAFLXMSSTWESNOPRF(A)), FC_TCR.O_SMDTTCR_Default, FC.O_THFC_Default).main() @ &m : res] 
    +
    Pr[FC_PRE.SM_DT_PRE_C(R_SMDTPREC_Game4WOTSTWES(R_MEUFGCMAWOTSTWES_EUFRMAFLXMSSTWESNOPRF(A)), FC_PRE.O_SMDTPRE_Default, FC.O_THFC_Default).main() @ &m : res]
    +
    Pr[PKCOC_TCR.SM_DT_TCR_C(R_SMDTTCRCPKCO_EUFRMAFLXMSSTWESNOPRF(A), PKCOC_TCR.O_SMDTTCR_Default, PKCOC.O_THFC_Default).main() @ &m : res]
    +
    Pr[TRHC_TCR.SM_DT_TCR_C(R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF(A), TRHC_TCR.O_SMDTTCR_Default, TRHC.O_THFC_Default).main() @ &m : res].
proof.
move=> gel_d.
move/(EUFRMA_FLXMSSTWES_NOPRF &m): gel_d => thm_nprf.
have ->:
  Pr[EUF_RMA_FLXMSSTWES(A).main() @ &m : res]
  =
  Pr[EUF_RMA_FLXMSSTWES_Inline.main() @ &m : res].
+ by byequiv EUFRMA_FLXMSSTWES_Inline. 
rewrite -addr0 -(subrr Pr[EUF_RMA_FLXMSSTWES_NOPRF(A).main() @ &m : res]).
rewrite (addrC Pr[EUF_RMA_FLXMSSTWES_NOPRF(A).main() @ &m : res]) addrA.
apply (ler_trans (`|Pr[EUF_RMA_FLXMSSTWES_Inline.main() @ &m : res] -
                    Pr[EUF_RMA_FLXMSSTWES_NOPRF(A).main() @ &m : res]| 
                    +
                    Pr[EUF_RMA_FLXMSSTWES_NOPRF(A).main() @ &m : res])).
+ by smt(ler_trans ler_norm ler_norm_add).
rewrite -4!addrA ler_add; first by rewrite (Step_EUFRMAFLXMSSTWESInlineNOPRF_PRF &m).
by rewrite !addrA thm_nprf.
qed.

end section Proof_EUF_RMA_FLXMSSTWES.



(* --- Fixed-Length XMSS-TW as standalone --- *)
(* -- Clones and imports -- *)
(* Import relevant definitions for key-updating signature scheme *)
clone import DigitalSignatures as FLXMSSTW with
  type pk_t <= pkFLXMSSTW,
  type sk_t <= skFLXMSSTW,
  type msg_t <= msgFLXMSSTW,
  type sig_t <= sigFLXMSSTW
  
  proof *.
  
clone import FLXMSSTW.KeyUpdating.EUFRMA as FLXMSSTW_EUFRMA with
  op n_eufrma <= l,
   
  op dmsg <= dmsgFLXMSSTW
  
  proof *. 
  realize ge0_neufrma by smt(IntOrder.expr_ge0 ge1_h).
  realize dmsg_ll by rewrite /dmsgFLXMSSTW dmsgFLXMSSTW_ll.


(* -- Specification of Fixed-Length XMSS-TW as standalone -- *)
module FL_XMSS_TW : FLXMSSTW.KeyUpdating.Scheme = {
  proc keygen() : pkFLXMSSTW * skFLXMSSTW = {
    var ss : sseed;
    var ps : pseed;
    var ad : adrs;
    var pk : pkFLXMSSTW;
    var sk : skFLXMSSTW;
        
    ss <$ dsseed;
    ps <$ dpseed;
    (*ad <- get_adrs (0, 0, 0, 0, 0, 0);*)
    ad <- witness;
    
    (pk, sk) <@ FL_XMSS_TW_ES.keygen(ss, ps, ad);
    
    return (pk, sk);
  }
  
  proc sign(sk : skFLXMSSTW, m : msgFLXMSSTW) : sigFLXMSSTW * skFLXMSSTW = {
    var sig : sigFLXMSSTW;
    
    (sig, sk) <@ FL_XMSS_TW_ES.sign(sk, m);
    
    return (sig, sk);
  }
  
  proc verify(pk : pkFLXMSSTW, m : msgFLXMSSTW, sig : sigFLXMSSTW) : bool = {
    var ver : bool;
    
    ver <@ FL_XMSS_TW_ES.verify(pk, m, sig);
    
    return ver;
  }
}.

lemma FLXMSSTW_keygen_ll: islossless FL_XMSS_TW.keygen.
proof.
islossless; while true (l - size leafl); auto=> [|/#].
inline *; auto.
while true (len - size pkWOTS0); auto; 1:smt(size_rcons).
by while true (len - size skWOTS0); auto; smt(size_rcons).
qed.

lemma FLXMSSTW_sign_ll: islossless FL_XMSS_TW.sign.
proof.
islossless.
+ while true (l - size leafl); auto=> [|/#].
  inline *; auto.
  while true (len - size pkWOTS0); auto; 1:smt(size_rcons).
  by while true (len - size skWOTS0); auto; smt(size_rcons).
+ by while true (len - size sig); auto; smt(size_rcons).
+ by while true (len - size skWOTS); auto; smt(size_rcons).
qed.

lemma FLXMSSTW_verify_ll: islossless FL_XMSS_TW.verify.
proof. by islossless; while true (len - size pkWOTS); auto; smt(size_rcons). qed.


(* -- Reduction adversaries -- *)
module R_EUFRMAFLXMSSTW_EUFRMAFLXMSSTWES (A : Adv_EUFRMA) : Adv_EUFRMA_FLXMSSTWES = {
  proc choose() : adrs = {
    var ad : adrs;
    
    (*ad <- get_adrs (0, 0, 0, 0, 0, 0);*)
    ad <- witness;
    
    return ad;
  }
  
  proc forge(pk : pkFLXMSSTW, msigl : (msgFLXMSSTW * sigFLXMSSTW) list) : msgFLXMSSTW * sigFLXMSSTW = {
    var msig : msgFLXMSSTW * sigFLXMSSTW;
    
    msig <@ A.forge(pk, msigl);
    
    return msig; 
  }
}.

(* -- Proof of EUF-RMA for Fixed-Length XMSS-TW as standalone -- *)
section Proof_EUF_RMA_FLXMSSTW.
(* - Module declarations - *)
declare module A <: Adv_EUFRMA{-PRF_SK_PRF.O_PRF_Default, -FC.O_THFC_Default, -FC_PRE.O_SMDTPRE_Default, -FC_TCR.O_SMDTTCR_Default, -FC_UD.O_SMDTUD_Default, -O_MEUFGCMA_WOTSTWES, -PKCOC.O_THFC_Default, -PKCOC_TCR.O_SMDTTCR_Default, -TRHC.O_THFC_Default, -TRHC_TCR.O_SMDTTCR_Default, -R_SMDTUDC_Game23WOTSTWES, -R_SMDTTCRC_Game34WOTSTWES, -R_PRF_FLXMSSTWESInlineNOPRF, -R_SMDTPREC_Game4WOTSTWES, -R_MEUFGCMAWOTSTWES_EUFRMAFLXMSSTWESNOPRF, -R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF, -R_SMDTTCRCPKCO_EUFRMAFLXMSSTWESNOPRF, -R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF, -R_EUFRMAFLXMSSTW_EUFRMAFLXMSSTWES}.

declare axiom A_forge_ll : islossless A.forge.


(* - Steps - *)
(*  
  First step: Reduce EUF-RMA for Fixed-Length XMSS-TW in an encompassing structure to EUF-RMA
  for Fixed-Length XMSS-TW as standalone  
*)
local lemma Step_EUFRMA_FLXMSSTW_FLXMSSTWES &m:
  Pr[EUF_RMA(FL_XMSS_TW, A).main() @ &m : res]
  =
  Pr[EUF_RMA_FLXMSSTWES(R_EUFRMAFLXMSSTW_EUFRMAFLXMSSTWES(A)).main() @ &m : res].
proof.
byequiv => //=.
proc.
inline{1} 5; inline{1} 1; inline{2} 7; inline{2} 3.
seq 8 11 : (={pk, m', sig', msigl}); last by sim.
wp; call (: true); wp.
while (={ps, ad, pk, sk, msigl}).
+ inline{1} 2.
  wp; call (: true); first by sim.
  by wp; rnd; skip.
wp; call (: true); first by sim.
by wp; rnd; rnd; skip. 
qed.

(* Security Theorem *)
lemma EUFRMA_FLXMSSTW &m :
  l <= WOTS_TW.d =>
    Pr[EUF_RMA(FL_XMSS_TW, A).main() @ &m : res]
    <=
  `|Pr[PRF_SK_PRF.PRF(R_PRF_FLXMSSTWESInlineNOPRF(R_EUFRMAFLXMSSTW_EUFRMAFLXMSSTWES(A)), PRF_SK_PRF.O_PRF_Default).main(false) @ &m : res] - 
    Pr[PRF_SK_PRF.PRF(R_PRF_FLXMSSTWESInlineNOPRF(R_EUFRMAFLXMSSTW_EUFRMAFLXMSSTWES(A)), PRF_SK_PRF.O_PRF_Default).main(true) @ &m : res]|
    +
    (w - 2)%r * 
  `|Pr[FC_UD.SM_DT_UD_C(R_SMDTUDC_Game23WOTSTWES(R_MEUFGCMAWOTSTWES_EUFRMAFLXMSSTWESNOPRF(R_EUFRMAFLXMSSTW_EUFRMAFLXMSSTWES(A))), FC_UD.O_SMDTUD_Default, FC.O_THFC_Default).main(false) @ &m : res] - 
    Pr[FC_UD.SM_DT_UD_C(R_SMDTUDC_Game23WOTSTWES(R_MEUFGCMAWOTSTWES_EUFRMAFLXMSSTWESNOPRF(R_EUFRMAFLXMSSTW_EUFRMAFLXMSSTWES(A))), FC_UD.O_SMDTUD_Default, FC.O_THFC_Default).main(true) @ &m : res]| 
    +
    Pr[FC_TCR.SM_DT_TCR_C(R_SMDTTCRC_Game34WOTSTWES(R_MEUFGCMAWOTSTWES_EUFRMAFLXMSSTWESNOPRF(R_EUFRMAFLXMSSTW_EUFRMAFLXMSSTWES(A))), FC_TCR.O_SMDTTCR_Default, FC.O_THFC_Default).main() @ &m : res] 
    +
    Pr[FC_PRE.SM_DT_PRE_C(R_SMDTPREC_Game4WOTSTWES(R_MEUFGCMAWOTSTWES_EUFRMAFLXMSSTWESNOPRF(R_EUFRMAFLXMSSTW_EUFRMAFLXMSSTWES(A))), FC_PRE.O_SMDTPRE_Default, FC.O_THFC_Default).main() @ &m : res]
    +
    Pr[PKCOC_TCR.SM_DT_TCR_C(R_SMDTTCRCPKCO_EUFRMAFLXMSSTWESNOPRF(R_EUFRMAFLXMSSTW_EUFRMAFLXMSSTWES(A)), PKCOC_TCR.O_SMDTTCR_Default, PKCOC.O_THFC_Default).main() @ &m : res]
    +
    Pr[TRHC_TCR.SM_DT_TCR_C(R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF(R_EUFRMAFLXMSSTW_EUFRMAFLXMSSTWES(A)), TRHC_TCR.O_SMDTTCR_Default, TRHC.O_THFC_Default).main() @ &m : res].
proof.
move=> gel_d.
rewrite Step_EUFRMA_FLXMSSTW_FLXMSSTWES &(EUFRMA_FLXMSSTWES (R_EUFRMAFLXMSSTW_EUFRMAFLXMSSTWES(A))) //.
+ by proc; wp.
by proc; call A_forge_ll.
qed.

end section Proof_EUF_RMA_FLXMSSTW.
