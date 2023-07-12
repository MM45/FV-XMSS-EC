(* --- Require/Import --- *)
(* -- Built-In (Standard Library) -- *)
require import AllCore List Distr DList DInterval IntDiv RealExp StdOrder SmtMap StdBigop BitEncoding FinType.
require (*--*) Word Subtype.
(*---*) import RField IntOrder RealOrder Bigreal Bigint BIA BS2Int.


(* -- Local -- *)
require (*--*) HashAddresses KeyedHashFunctions TweakableHashFunctions DigitalSignatures.



(* --- Generic auxilliary properties --- *)
lemma gt_exprsbde (x n m : int) :
  1 < x => 0 <= n < m => x ^ n < x ^ m.
proof.
move=> gt1_x [ge0_n gtn_m]. 
have ge0_m: 0 <= m by smt(). 
elim: n ge0_n m ge0_m gtn_m => [| i ge0_i ih m ge0_m gti1_m].
+ by elim => [/# | *]; rewrite expr0 exprn_egt1 /#.
rewrite exprD_nneg // expr1 (: m = m - 1 + 1) // exprD_nneg 1:/# // expr1.
by rewrite ltr_pmul2r 2:(ih (m - 1)) /#.
qed.

lemma drop_putK (s : 'a list) (i j : int) (x : 'a) :
     j < i 
  => drop i (put s j x) = drop i s.
proof.
elim: s i j => [ * | x' s ih i j gtj_i]; 1: by rewrite put_empty. 
case (i <= 0) => [le0_i | /ltzNge gt0_i]; 1: by rewrite put_out /#.
case (j = 0) => [-> /# | neq0_j].
by rewrite put_consS // /= ih /#.
qed.

lemma drop_putC (s : 'a list) (i j : int) (x : 'a) :
     0 <= i <= j 
  => drop i (put s j x) = put (drop i s) (j - i) x.
proof.
elim: s i j => [ * | x' s ih i j [ge0_i gei_j] /=]; 1: smt(put_empty).
case (i = 0) => [-> /# | neq0_i].
by rewrite put_consS 1:/# /= (: ! i <= 0) 1:/# /= ih /#.
qed.

lemma take_putK (s : 'a list) (i j : int) (x : 'a) :
     i <= j 
  => take i (put s j x) = take i s.
proof.
elim: s i j => [ * | x' s ih i j gej_i]; 1: by rewrite put_empty. 
case (i <= 0) => [le0_i | nle0_i]; 1: by rewrite take_le0 /#.
by rewrite put_consS 1:/# /= nle0_i /= ih /#.
qed.

lemma take_putC (s : 'a list) (i j : int) (x : 'a) :
     j < i
  => take i (put s j x) = put (take i s) j x.
proof.
elim: s i j => [ * | x' s ih i j lti_j /=]; 1: smt(put_empty).
case (i <= 0) => [le0_i | nle0_i]; 1: by rewrite take_le0 2:put_empty.
case (j = 0) => [-> | neq0_j]; 1: by rewrite 2!put_cons0 /= nle0_i.
by rewrite ?put_consS //= nle0_i /= ih /#.
qed. 

lemma take_put (s : 'a list) (i j : int) (x : 'a) :
  take i (put s j x) = if i <= j then take i s else put (take i s) j x.
proof. by case (i <= j) => [| /ltzNge]; [apply take_putK | apply take_putC]. qed.

lemma neq_from_nth (x0 : 'a) (s1 s2 : 'a list) (i : int) :
     nth x0 s1 i <> nth x0 s2 i 
  => s1 <> s2.
proof. by apply contra => ->. qed.

lemma nth_nmem (s : 'a list) (x : 'a) :
     (forall (i : int), 0 <= i < size s => nth witness s i <> x)
  => ! (x \in s).
proof.
elim: s => // y l ih /= nnth.
rewrite negb_or; split.
+ by move: (nnth 0 _) => /=; [smt(size_ge0) | rewrite eq_sym].
apply ih => i rng_i.
by move: (nnth (i + 1) _) => /#.
qed.

lemma nth_uniq (s : 'a list) :
      (forall (i j : int), 0 <= i < size s => 0 <= j < size s => i <> j =>
         nth witness s i <> nth witness s j)
  =>  uniq s.
proof.
elim: s => //= x s ih neq_nth.
split.
+ apply nth_nmem => i rng_i.
  by move: (neq_nth (i + 1) 0 _ _ _); smt(size_ge0).
apply ih => i j rng_i rng_j neqj_i.
by move: (neq_nth (i + 1) (j + 1) _ _ _) => /#.
qed.

lemma size_nth_uniq (s : 'a list list) :
      (forall (i j : int), 0 <= i < size s => 0 <= j < size s => i <> j =>
         size (nth witness s i) <> size (nth witness s j))
  =>  uniq s.
proof. by smt(nth_uniq). qed.

lemma map_size_ge0 (s : 'a list list) :
  all ((<=) 0) (map size s).
proof. by rewrite allP => i /mapP; smt(size_ge0). qed.

lemma sumz_ge0 (sz : int list) :
  all ((<=) 0) sz => 0 <= sumz sz.
proof.
elim: sz => //= x s ih [ge0_x ge0_s] @/sumz /= @-/(sumz s).
by rewrite addr_ge0 2:ih.
qed.

lemma flatten_rcons (s : 'a list list) (x : 'a list)  :
  flatten (rcons s x) = flatten s ++ x.
proof. by rewrite -cats1 flatten_cat flatten_seq1. qed.

lemma uniq_mapP (f : 'a -> 'b) (s : 'a list) (x x' : 'a) :
  x \in s => x' \in s => x <> x' => uniq (map f s) => f x <> f x'.
proof. by elim: s => //; smt(map_f). qed.

lemma uniq_flatten (s : 'a list list) :
     all uniq s 
  => (forall x y, x \in s => y \in s => has (mem x) y => x = y) 
  => uniq s 
  => uniq (flatten s).
proof.
elim: s => /= [| x s ih [uqx uqins] hasn [ninsx uqs]].
+ by rewrite flatten_nil.
rewrite flatten_cons cat_uniq uqx /= ih //= 1:/#.
apply: hasPn => a /flattenP [x'] [xpin ainp]; apply: negP => ain. 
have ->> //: x = x'; apply: hasn => //; first by rewrite xpin.
by rewrite hasP; exists a.
qed.

lemma uniq_flatten_map_in (f : 'a -> 'b list) (s : 'a list) :
     all uniq (map f s) 
  => (forall x y, x \in s => y \in s => has (mem (f x)) (f y) => x = y) 
  => uniq s 
  => uniq (flatten (map f s)).
proof.
elim: s => /= [|x s ih [uqf uqins] inj_f [ninsx uqs]].
+ by rewrite flatten_nil.
rewrite flatten_cons cat_uniq uqf ih //= 1:/#.
apply: negP => /List.hasP [a] [/flatten_mapP] [b] [sb] fba fxa.
have ->> //: x = b; apply/inj_f=> //; first by rewrite sb.
by rewrite hasP; exists a.
qed.

lemma map_flatten_map (f : 'a -> 'b) (s : 'a list list) :
  map f (flatten s) = flatten (map (map f) s).
proof.
elim: s => // x s ih.
by rewrite flatten_cons /= flatten_cons map_cat ih.
qed.

lemma uniq_flatten_map_in_rev (f : 'a -> 'b) (s : 'a list list) :
     all (uniq \o (map f)) s
  => (forall x y, x \in s => y \in s => has (mem (map f x)) (map f y) => x = y)
  => uniq s
  => uniq (map f (flatten s)).
proof.
move => alluqmfs inj_mf uqs. 
by rewrite map_flatten_map uniq_flatten_map_in 1:all_map. 
qed.

lemma nth_flatten (s : 'a list list) (i j : int) :
     0 <= i < size s 
  => 0 <= j < size (nth witness s i) 
  => nth witness (flatten s) (sumz (map size (take i s)) + j) 
     = 
     nth witness (nth witness s i) j.
proof.
elim: s i j => [| x s ih] i j /=.
+ by rewrite flatten_nil /#.
rewrite flatten_cons => rng_i.
case (i = 0) => [eq0_i | neq0_i].
+ by rewrite eq0_i /sumz /= nth_cat => rng_j /#.
have -> /=: ! (i <= 0) by smt().
rewrite /sumz /= nth_cat -/(sumz (map size (take (i - 1) s))) /= => rng_j.
have ge0_sumz : 0 <= sumz (map size (take (i - 1) s)) by apply /sumz_ge0 /map_size_ge0. 
rewrite (: ! (size x + sumz (map size (take (i - 1) s)) + j < size x)) 1:/# /=.
have ->: size x + sumz (map size (take (i - 1) s)) + j - size x = sumz (map size (take (i - 1) s)) + j by smt(). 
by apply (ih (i - 1)) => // /#.
qed.

lemma nth_flatten_flatten (s : 'a list list list) (i j k : int) :
     0 <= i < size s
  => 0 <= j < size (nth witness s i)
  => 0 <= k < size (nth witness (nth witness s i) j)
  => nth witness (flatten (map flatten s))
                 (sumz (map (fun x => sumz (map size x)) (take i s)) 
                  + sumz (map size (take j (nth witness s i))) 
                  + k) 
     =
     nth witness (nth witness (nth witness s i) j) k.
proof.
elim: s i j k => [/# | x s ih i j k /=].
case (i = 0) => [eq0_i | neq0_i rng_i rng_j rng_k].
+ rewrite eq0_i /sumz /= -/(sumz (map size (take j x))) => _ rng_j rng_k.
  rewrite -nth_flatten // flatten_cons nth_cat.
  rewrite (: sumz (map size (take j x)) + k < size (flatten x)) //.
  rewrite size_flatten ?sumzE ?big_mapT /(\o).
  rewrite -{2}(cat_take_drop j x) big_cat ler_lt_add //. 
  rewrite (drop_nth witness) // big_consT /= ltr_paddr 2:/#.
  by rewrite sumr_ge0 => ? _; apply size_ge0.
rewrite (: ! i <= 0) 1:/#  -ih 1:/# //= flatten_cons nth_cat.
pose susu := sumz (sumz _ :: _) + _ + _; rewrite (: ! susu < size (flatten x)) /= /susu.
+ rewrite -lezNgt size_flatten (sumzE (sumz _ :: _)) big_cons /predT /= -/predT.
  rewrite -2!addrA ler_addl -sumzE addrA addr_ge0 2:/# addr_ge0 sumz_ge0 2:map_size_ge0.
  by rewrite allP => l /mapP -[x' [xpin /= ->]]; rewrite sumz_ge0 map_size_ge0. 
by congr; rewrite sumzE big_cons /predT /= -/predT size_flatten -sumzE /#. 
qed.

lemma nth_flatten_map_flatten (s : 'a list) (f : 'a -> 'b list list) (i j k : int) :
     0 <= i < size s
  => 0 <= j < size (nth witness (map f s) i)
  => 0 <= k < size (nth witness (nth witness (map f s) i) j)
  => nth witness (flatten (map (fun x => flatten (f x)) s)) 
                 (sumz (map (fun x => sumz (map size x)) (take i (map f s))) 
                  + sumz (map size (take j (nth witness (map f s) i))) 
                  + k) 
     =
     nth witness (nth witness (nth witness (map f s) i) j) k.
proof. 
move=> rng_i rng_j rng_k; move: (nth_flatten_flatten (map f s) i j k _ rng_j rng_k).
+ by rewrite size_map rng_i.
by move=> <-; congr; rewrite map_comp.
qed.

lemma eq_from_flatten_nth (s s' : 'a list list):
     size s = size s'
  => (forall (i : int), 0 <= i < size s =>
        size (nth witness s i) = size (nth witness s' i))
  => flatten s = flatten s'
  => s = s'.
proof.
elim: s s' => [ | x s ih]; first by smt(size_eq0).
case => [| x' s' /= eqszs1_szsp1 eqsznth]; first by smt(size_eq0).
rewrite 2!flatten_cons eqseq_cat 1:(eqsznth 0 _) //; first by smt(size_ge0).
move=> [-> eqfls_flsp]; rewrite (ih s') 1:/# // => i rng_i.
by move: (eqsznth (i + 1) _) => /#.
qed.

lemma djl_parts (l s sp1 sp2 : 'a list) :
     all (fun (x : 'a) => x \in sp1 \/ x \in sp2) s
  => ! has (mem sp1) l
  => ! has (mem sp2) l
  => ! has (mem s) l.
proof.
move=> /allP xmem /hasPn djlsp1 /hasPn djlsp2.
rewrite hasPn => x xinl.
rewrite -negP => xins. 
move: (xmem x xins) => /=.
rewrite negb_or; split.
+ by move: (djlsp1 x xinl).
by move: (djlsp2 x xinl).  
qed.



(* --- Parameters --- *)
(* -- Overall -- *)
(* Length of addresses used in tweakable hash functions (including unspecified global/context part) *)
const adrs_len : { int | 2 <= adrs_len} as ge2_adrslen.


(* -- WOTS-TW specific -- *)
(* 
  Length (in bytes) of messages as well as the length of elements of 
  private keys, public keys, and signatures
*)
const n : { int | 1 <= n } as ge1_n.

(* Base 2 logarithm of the Winternitz parameter w *)
const log2_w : { int | log2_w = 2 \/ log2_w = 4 \/ log2_w = 8 } as val_log2w.

(* Winternitz parameter (base/radix) *)
const w = 2 ^ log2_w. 

(* Length of the message in base/radix w *)
const len1 : int = ceil ((8 * n)%r / log2 w%r).

(* Length of the checksum in base/radix w *)      
const len2 : int = floor (log2 ((len1 * (w - 1))%r) / log2 w%r) + 1.

(* Number of elements (of length n) in private keys, public keys, and signatures *)
const len : int = len1 + len2.


(* -- Notions -- *)
(*  Number of WOTS-TW instances to consider for M-EUF-GCMA notion *)
const d : { int | 1 <= d } as ge1_d.


(* -- Properties of parameters -- *)
(*
(* The different address types are distinct *)
axiom dist_adrstypes : chtype <> pkcotype /\ chtype <> trhtype /\ pkcotype <> trhtype.
*)
(* Winternitz parameter w is a power of 2 *)
lemma wpowof2: exists a, w = 2 ^ a.
proof. by exists log2_w. qed.

(* log2_w is the (base 2) logarithm of w *)
lemma log2_wP: log2 w%r = log2_w%r.
proof. by rewrite /w -fromintXn 2:-rpow_nat 1,2:#smt:(val_log2w) // /log2 logK. qed.

(* Winternitz parameter w equals either 4, 16, or 256 *)
lemma val_w : w = 4 \/ w = 16 \/ w = 256.
proof.
rewrite /w; case: val_log2w => [->|]; last case => ->.
+ by left; rewrite expr2.
+ by right; left; rewrite (: 4 = (2 + 2)) 2:exprD_nneg // expr2. 
+ by right; right; rewrite (: 8 = 2 * 2 * 2) // 2!exprM ?expr2.
qed.

(* Value of w equals 4 iff its (base 2) logarithm equals 2 *)
lemma val_w_log2 : log2_w = 2 <=> w = 4.
proof. 
rewrite /w (: 4 = 2 ^ 2) 1:expr2; split => [-> //| eq_pow2].
rewrite -eq_fromint &(inj_rexpr 2%r) // ?rpow_int //.
by rewrite ?fromintXn 1:#smt:(val_log2w) // eq_fromint.
qed.

(* Value of w equals 16 iff its (base 2) logarithm equals 4 *)
lemma val_w_log4 : log2_w = 4 <=> w = 16.
proof. 
rewrite /w (: 16 = 2 ^ 4); first by rewrite (: 4 = 2 * 2) // exprM ?expr2.
split => [-> //| eq_pow2].
rewrite -eq_fromint &(inj_rexpr 2%r) // ?rpow_int //.
by rewrite ?fromintXn 1:#smt:(val_log2w) // eq_fromint.
qed.

(* Value of w equals 256 iff its (base 2) logarithm equals 8 *)
lemma val_w_log8 : log2_w = 8 <=> w = 256.
proof. 
rewrite /w (: 256 = 2 ^ 8); first by rewrite (: 8 = 2 * 2 * 2) // ?exprM ?expr2.
split => [-> //| eq_pow2].
rewrite -eq_fromint &(inj_rexpr 2%r) // ?rpow_int //.
by rewrite ?fromintXn 1:#smt:(val_log2w) // eq_fromint.
qed.

(* Value of len1 equals either 4 * n, 2 * n, or n *)
lemma val_len1 : len1 = 4 * n \/ len1 = 2 * n \/ len1 = n.
proof.
rewrite /len1 log2_wP (: 8 = 2 * 2 * 2) // ?fromintM. 
case: val_log2w => [->|]; last case => ->. 
+ by left; rewrite mulrC ?mulrA mulVf //= -fromintM from_int_ceil. 
+ right; left.
  by rewrite mulrC (: 4 = 2 * 2) // 2!mulrA mulVf //= -fromintM from_int_ceil.
+ right; right.
  by rewrite mulrC (: 8 = 2 * 2 * 2) // mulrA mulVf //= from_int_ceil.
qed.

(* Value of len1 equals 4 * n if the (base 2) logarithm of w equals 2 *)
lemma val_len1_log2 : log2_w = 2 => len1 = 4 * n.
proof.
rewrite /len1 log2_wP (: 8 = 2 * 2 * 2) // ?fromintM => ->.
by rewrite mulrC ?mulrA mulVf //= -fromintM from_int_ceil.
qed.

(* Value of len1 equals 2 * n if the (base 2) logarithm of w equals 4 *)
lemma val_len1_log4 : log2_w = 4 => len1 = 2 * n.
proof.
rewrite /len1 log2_wP (: 8 = 2 * 2 * 2) 2:(: 4 = 2 * 2) // ?fromintM => ->.
by rewrite mulrC 2!mulrA mulVf //= -fromintM from_int_ceil.
qed.

(* Value of len1 equals n if the (base 2) logarithm of w equals 8 *)
lemma val_len1_log8 : log2_w = 8 => len1 = n.
proof.
rewrite /len1 log2_wP (: 8 = 2 * 2 * 2) // ?fromintM => ->.
by rewrite mulrC mulrA mulVf //= from_int_ceil.
qed.

(* len1 is greater than or equal to 1 *)
lemma ge1_len1 : 1 <= len1.
proof. smt(val_len1 IntOrder.ler_pmul ge1_n). qed.

(* len2 is greater than or equal to 1 *)
lemma ge1_len2 : 1 <= len2.
proof. smt(divr_ge0 ge1_len1 floor_gt val_w log_ge0). qed.

(* len is greater than or equal to 2 *)
lemma ge2_len : 2 <= len.
proof. smt(ge1_len1 ge1_len2). qed.



(* --- Types (1/2) --- *)
(* -- General -- *)
(* Base/radix w digits *)
clone import Subtype as BaseW with 
  type T   <- int,
    op P x <- 0 <= x < w
    
  proof *.
  realize inhabited by exists 0; smt(val_w).
  
type baseW = BaseW.sT.

(* Secret (PRF) seeds *)
type sseed.

(* Public seeds *)
type pseed.

(* 
  Digests, i.e., outputs of (tweakable) hash functions. 
  In fact, also type of input of tweakable hash functions in this case.
*)
type dgst = bool list.

(* Digests with length 1 (block of 8 * n bits) *)
clone import Subtype as DigestBlock with
  type T   <- dgst,
    op P x <- size x = 8 * n
    
  proof *.
  realize inhabited by exists (nseq (8 * n) witness); smt(size_nseq ge1_n).
  
type dgstblock = DigestBlock.sT.

clone import FinType as DigestBlockFT with
  type t <= dgstblock,
  
    op enum <= map DigestBlock.insubd (map (int2bs (8 * n)) (range 0 (2 ^ (8 * n))))
    
  proof *.
  realize enum_spec.
    move=> m; rewrite count_uniq_mem 1:map_inj_in_uniq => [x y | |].
    + rewrite 2!mapP => -[i [/mem_range rng_i ->]] -[j [/mem_range rng_j ->]] eqins. 
      rewrite -(DigestBlock.insubdK (int2bs (8 * n) i)) 1:size_int2bs; 1: smt(ge1_n).
      rewrite -(DigestBlock.insubdK (int2bs (8 * n) j)) 1:size_int2bs; 1: smt(ge1_n). 
      by rewrite eqins. 
    + rewrite map_inj_in_uniq => [x y /mem_range rng_x /mem_range rng_y|].
      rewrite -{2}(int2bsK (8 * n) x) 3:-{2}(int2bsK (8 * n) y) //; 1,2: smt(ge1_n).
      by move=> ->. 
    + by rewrite range_uniq.
    rewrite -b2i1; congr; rewrite eqT mapP. 
    exists (DigestBlock.val m).
    rewrite DigestBlock.valKd mapP /=. 
    exists (bs2int (DigestBlock.val m)).
    rewrite mem_range bs2int_ge0 /= (: 8 * n = size (DigestBlock.val m)) 1:DigestBlock.valP //. 
    by rewrite bs2intK bs2int_le2Xs.
  qed. 
  
(* Lists of length len of which each entry is a digest of length 1 (block of 8 * n bits) *)
clone import Subtype as DBLL with
  type T   <- dgstblock list,
    op P l <- size l = len
  
  proof *.
  realize inhabited by by exists (nseq len witness); smt(size_nseq ge2_len).

type dgstblocklenlist = DBLL.sT.


(* -- WOTS/WOTS-TW specific -- *)
(* - Regular (i.e., WOTS without tweaks and without secret key generation) - *)
(* Public keys *)
type pkWOTS = dgstblocklenlist.

(* Secret keys *)
type skWOTS = dgstblocklenlist.

(* Messages *)
type msgWOTS = dgstblock.

(* Signatures *)
type sigWOTS = dgstblocklenlist.

(* Encoded messages *)
clone import Word as EmsgWOTS with
  type Alphabet.t <- baseW,
    op Alphabet.enum <- map (oget \o BaseW.insub) (range 0 w),
    op n <- len
  
  proof Alphabet.enum_spec, ge0_n
    
  rename "word"    as "emsgWOTS"
         "dunifin" as "demsgWOTS".
  
  realize Alphabet.enum_spec.
    move=> b; rewrite count_map /preim /(\o) /=.
    rewrite (eq_in_count _ (pred1 (BaseW.val b))).
    + move=> x //=; rewrite mem_range=> x_in_0_Pw @/pred1; split=> <*>>.
      - by move: x_in_0_Pw=> /BaseW.insubT; case: (BaseW.insub x).
      by rewrite BaseW.valK.
    move: (range_uniq 0 w)=> /count_uniq_mem /(_ (BaseW.val b)) -> @/b2i.
    by rewrite mem_range BaseW.valP.
  qed.
  
  realize ge0_n by smt(ge2_len).



(* --- Distributions --- *)
(* Proper distribution over secret seeds *)
op [lossless] dsseed : sseed distr.

(* Proper distribution over public seeds *)
op [lossless] dpseed : pseed distr.

(* Proper distribution over digests of length 1 (block of 8 * n bits) *)
op [lossless] ddgstblock : dgstblock distr.

(* 
  Proper distribution that samples a length len list of dgstblock elements by
  independently sampling each element from ddgstblock
*)
op ddgstblockl : dgstblock list distr = dlist ddgstblock len.

(* Properness of ddgstblockl *)
lemma ddgstblockl_ll : is_lossless ddgstblockl.
proof. by apply/dlist_ll /ddgstblock_ll. qed.

(* 
  Proper distribution over digests of length 1 (block of 8 * n bits) lifted
  to the regular type of digests
*)
op ddgstblocklift : dgst distr = dmap ddgstblock DigestBlock.val.

(* Properness of ddgstblocklift *)
lemma ddgstblocklift_ll : is_lossless ddgstblocklift.
proof. by apply/dmap_ll /ddgstblock_ll. qed.



(* --- Operators (1/2) --- *)
(* -- Validity checks -- *)
(* Chain index validity check *)
op valid_chidx (chidx : int) : bool =
  0 <= chidx < len.

(* Hash index validity check *)
op valid_hidx (hidx : int) : bool = 
  0 <= hidx < w - 1.

(* Overall (generic) validity check for indices of addresses *)
op valid_idxvals : int list -> bool.

(* Overall (generic) validity check for indices of addresses, including the number of indices *)
op valid_adrsidxs (adidxs : int list) =
  size adidxs = adrs_len /\ valid_idxvals adidxs.

(* 
  Generic validity check for the global/context part of the indices 
  corresponding to a WOTS-TW address
*)
op valid_widxvalsgp : int list -> bool.
 
(* 
  Validity check for the local part of the indices (i.e., the chain and hash indices) 
  corresponding to a WOTS-TW address 
*)
op valid_widxvalslp (adidxs : int list) : bool =
  valid_hidx (nth witness adidxs 0) /\ valid_chidx (nth witness adidxs 1).

(* 
  Overall validity check for the indices corresponding to a WOTS-TW address
  (the first two indices must be valid local indices, and the remaining indices 
  must constitute valid global/context indices)
*)  
op valid_widxvals (adidxs : int list) =
  valid_widxvalsgp (drop 2 adidxs) /\ valid_widxvalslp (take 2 adidxs).

(* 
  Overall validity check for the indices corresponding to a WOTS-TW address,
  including the number of indices
*)    
op valid_wadrsidxs (adidxs : int list) =
  size adidxs = adrs_len /\ valid_widxvals adidxs.

(* 
  The set of (indices corresponding to) valid WOTS-TW addresses must be a subset
  of the full set of (indices corresonding to) addresses
*) 
axiom valid_widxvals_idxvals : 
  valid_widxvals <= valid_idxvals.

(* The set of valid WOTS-TW addresses is a subset of the full set of addresses *)
lemma valid_wadrsidxs_adrsidxs :
  valid_wadrsidxs <= valid_adrsidxs.
proof. 
rewrite /(<=) /valid_wadrsidxs /valid_adrsidxs => adidxs [-> /=].
by apply valid_widxvals_idxvals.
qed.



(* --- Types (2/2) --- *)
(* Addresses used in tweakable hash functions *)
clone import HashAddresses as HA with
  type index <- int,
    op l <- adrs_len,
    op valid_idxvals <- valid_idxvals,
    op valid_adrsidxs <- valid_adrsidxs
    
  proof ge1_l by smt(ge2_adrslen).

import Adrs.



(* --- Operators (2/2) --- *)
(* -- Setters and getters -- *)  
(* 
  Sets chain index in (WOTS-TW) address
  Assumes that the given address is a valid WOTS-TW address 
*)
op set_chidx (ad : adrs) (i : int) : adrs =
  set_idx ad 1 i.
  
(* 
  Sets hash index in (WOTS-TW) address
  Assumes that the given address is a valid WOTS-TW address
*)
op set_hidx (ad : adrs) (i : int) : adrs =
  set_idx ad 0 i.

(* 
  Gets (indices corresponding to) the global part of a WOTS-TW address
  Assumes that the given address is a valid WOTS-TW address
*)
op get_wgpidxs (ad : adrs) : int list =
  drop 2 (val ad).

  
(* -- Auxiliary checks -- *)
(* 
  Checks whether (indices corresponding to) global parts of WOTS-TW addresses are equal
  Assumes that the given addresses are valid WOTS-TW addresses
*)
op eq_gp (ad ad' : adrs) : bool =
  get_wgpidxs ad = get_wgpidxs ad'.

(* 
  Checks whether (indices corresponding to) global parts of WOTS-TW addresses in a list are distinct
  Assumes that the given lists exclusively contain valid WOTS-TW addresses
*)  
op uniq_wgpidxs (adl : adrs list) : bool =
  uniq (map get_wgpidxs adl).

(* 
  Checks whether the WOTS-TW addresses in the first given list do not have any
  global parts common with the WOTS-TW addresses in the second given list
  Assumes that the given lists exclusively contain valid WOTS-TW addresses

*)  
op disj_wgpidxs (adl adl' : adrs list) : bool =
  ! has (mem (map get_wgpidxs adl')) (map get_wgpidxs adl).

(* 
  Checks whether an address is a WOTS-TW addresses
*)  
op valid_wadrs (ad : adrs) : bool =
  valid_wadrsidxs (val ad).

lemma validwadrsidxs_puthidx (adidxs : int list) (i : int) :
     valid_wadrsidxs adidxs
  => valid_hidx i
  => valid_wadrsidxs (put adidxs 0 i).
proof.
rewrite /valid_wadrsidxs /valid_widxvals => [#] eqszadl valgp vallp vali.
rewrite size_put eqszadl /= drop_putK // valgp /=  take_put /=.
move: vallp => @/valid_widxvalslp.
by rewrite ?nth_put ?nth_take // ?size_take //; smt(ge2_adrslen).
qed.

lemma validwadrsidxs_putchidx (adidxs : int list) (i : int) :
     valid_wadrsidxs adidxs
  => valid_chidx i
  => valid_wadrsidxs (put adidxs 1 i).
proof.
rewrite /valid_wadrsidxs /valid_widxvals => [#] eqszadl valgp vallp vali.
rewrite size_put eqszadl /= drop_putK // valgp /=  take_put /=.
move: vallp => @/valid_widxvalslp.
by rewrite ?nth_put ?nth_take // ?size_take //; smt(ge2_adrslen).
qed.

lemma validwadrsidxs_putchhidx (adidxs : int list) (i j : int) :
     valid_wadrsidxs adidxs
  => valid_chidx i
  => valid_hidx j
  => valid_wadrsidxs (put (put adidxs 1 i) 0 j).
proof. smt(validwadrsidxs_puthidx validwadrsidxs_putchidx). qed.

lemma validwadrs_sethidx (ad : adrs) (i : int) :
     valid_wadrs ad
  => valid_hidx i
  => valid_wadrs (set_hidx ad i).
proof. 
rewrite /valid_wadrs /valid_wadrsidxs /valid_widxvals => [#] eqszadl valgp vallp vali.
rewrite /set_chidx /set_idx ?insubdK 1:&(valid_wadrsidxs_adrsidxs) 1:validwadrsidxs_puthidx //.
rewrite size_put take_put drop_putK //=; split; 1: smt(valP).
move: vallp => @/valid_widxvalslp. 
by rewrite ?nth_put ?nth_take // ?size_take; smt(valP ge2_adrslen).
qed. 

lemma validwadrs_setchidx (ad : adrs) (i : int) :
     valid_wadrs ad
  => valid_chidx i
  => valid_wadrs (set_chidx ad i).
proof. 
rewrite /valid_wadrs /valid_wadrsidxs /valid_widxvals => [#] eqszadl valgp vallp vali.
rewrite /set_chidx /set_idx insubdK 1:&(valid_wadrsidxs_adrsidxs) 1:validwadrsidxs_putchidx //.
rewrite size_put take_put drop_putK //=; split; 1: smt(valP).
move: vallp => @/valid_widxvalslp. 
by rewrite ?nth_put ?nth_take // ?size_take; smt(valP ge2_adrslen).
qed.
  
lemma validwadrs_setchhidx (ad : adrs) (i j : int) :
     valid_wadrs ad
  => valid_chidx i
  => valid_hidx j
  => valid_wadrs (set_hidx (set_chidx ad i) j).
proof. smt(validwadrs_setchidx validwadrs_sethidx). qed.


lemma neq_after_setchidx (ad ad' : adrs) (i i' : int) :
     valid_wadrs ad
  => valid_wadrs ad'
  => valid_chidx i
  => valid_chidx i'
  => i <> i'
  => set_chidx ad i <> set_chidx ad' i'.
proof.
move=> valad valadp vali valip neqip_i.
rewrite /set_chidx neq_after_setidx_sidv //; 1: smt(ge2_adrslen). 
+ by rewrite /valid_setidx valid_wadrsidxs_adrsidxs validwadrsidxs_putchidx 1:/#.
by rewrite /valid_setidx valid_wadrsidxs_adrsidxs validwadrsidxs_putchidx 1:/#.
qed.

lemma neq_after_sethidx (ad ad' : adrs) (i i' : int) :
     valid_wadrs ad
  => valid_wadrs ad'
  => valid_hidx i
  => valid_hidx i'
  => i <> i'
  => set_hidx ad i <> set_hidx ad' i'.
proof.
move=> valad valadp vali valip neqip_i.
rewrite /set_chidx neq_after_setidx_sidv //; 1: smt(ge2_adrslen). 
+ by rewrite /valid_setidx valid_wadrsidxs_adrsidxs validwadrsidxs_puthidx 1:/#.
by rewrite /valid_setidx valid_wadrsidxs_adrsidxs validwadrsidxs_puthidx 1:/#.
qed.

lemma neq_after_setchhidx (ad ad' : adrs) (i i' j j' : int) :
     valid_wadrs ad
  => valid_wadrs ad'
  => valid_chidx i
  => valid_chidx i'
  => valid_hidx j
  => valid_hidx j'
  => i <> i' \/ j <> j'
  => set_hidx (set_chidx ad i) j <> set_hidx (set_chidx ad' i') j'.
proof. 
move=> valdad valadp vali valip valj valjp -[neqip_i | neqjp_j].
+ rewrite /set_hidx &(neq_after_setidx_sida _ _ _ 1) //=; 1: smt(ge2_adrslen).
  - rewrite /eq_idx ?valin_getidx_setidx //; 1,3: smt(ge2_adrslen). 
    * by rewrite /valid_setidx valid_wadrsidxs_adrsidxs validwadrsidxs_putchidx /#.
    by rewrite /valid_setidx valid_wadrsidxs_adrsidxs validwadrsidxs_putchidx /#.
  - rewrite /valid_setidx valid_wadrsidxs_adrsidxs /set_chidx /set_idx insubdK.
    * by rewrite valid_wadrsidxs_adrsidxs validwadrsidxs_putchidx /#.
    by rewrite validwadrsidxs_putchhidx.
  rewrite /valid_setidx valid_wadrsidxs_adrsidxs /set_chidx /set_idx insubdK.
  * by rewrite valid_wadrsidxs_adrsidxs validwadrsidxs_putchidx /#.
  by rewrite validwadrsidxs_putchhidx.
rewrite neq_after_sethidx // /valid_wadrs /set_chidx /set_idx insubdK. 
+ by rewrite valid_wadrsidxs_adrsidxs validwadrsidxs_putchidx /#.
+ by rewrite validwadrsidxs_putchidx.
+ by rewrite valid_wadrsidxs_adrsidxs validwadrsidxs_putchidx /#.
by rewrite validwadrsidxs_putchidx.  
qed.

lemma neq_gp (ad ad' : adrs) :
  get_wgpidxs ad <> get_wgpidxs ad' => ad <> ad'.
proof. smt(). qed.

lemma eq_gp_sethidx (ad : adrs) (i : int) :
     valid_wadrs ad
  => valid_hidx i
  => get_wgpidxs (set_hidx ad i) = get_wgpidxs ad.
proof. 
move=> valad vali; rewrite /get_wgpidxs /set_hidx /set_idx insubdK 2:drop_putK //.
by rewrite valid_wadrsidxs_adrsidxs validwadrsidxs_puthidx.
qed.

lemma eq_gp_setchidx (ad : adrs) (i : int) :
     valid_wadrs ad
  => valid_chidx i
  => get_wgpidxs (set_chidx ad i) = get_wgpidxs ad.
proof. 
move=> valad vali; rewrite /get_wgpidxs /set_hidx /set_idx insubdK 2:drop_putK //.
by rewrite valid_wadrsidxs_adrsidxs validwadrsidxs_putchidx.
qed.

lemma eq_gp_setchhidx (ad : adrs) (i j : int) :
     valid_wadrs ad
  => valid_chidx i
  => valid_hidx j
  => get_wgpidxs (set_hidx (set_chidx ad i) j) = get_wgpidxs ad.
proof. 
move=> valad vali valj @/get_wgpidxs @/set_hidx @/set_chidx @/set_idx. 
rewrite ?insubdK ?valid_wadrsidxs_adrsidxs ?validwadrsidxs_putchidx ?validwadrsidxs_putchhidx //.
by rewrite ?drop_putK.
qed.


(* -- Keyed hash functions -- *)
(* Keyed hash function (PRF) used to generate WOTS-TW secret keys *)
op prf_sk : sseed -> (pseed * adrs) -> dgstblock.

(* Import relevant definitions/properties for keyed hash function (PRF) prf_sk *)
clone import KeyedHashFunctions as PRF_SK with
  type in_t <- (pseed * adrs),
  type out_t <- dgstblock,
  type key_t <- sseed,
  
    op f <- prf_sk
    
  proof *.
  
clone import PRF as PRF_SK_PRF with
  op dkey <- dsseed,
  op doutm <- fun x => ddgstblock
    
  proof *.
  realize dkey_ll by exact: dsseed_ll.
  realize doutm_ll by rewrite ddgstblock_ll.

    
(* -- Tweakable hash functions -- *)
(* 
  Tweakable hash function collection that contains all tweakable hash functions
  used in WOTS-TW, XMSS, and SPHINCS+
*)
op thfc : int -> pseed -> adrs -> dgst -> dgstblock.

(* Tweakable hash function used in WOTS-TW chains *)
op f : pseed -> adrs -> dgst -> dgstblock = thfc (8 * n).

(* Import relevant definitions/properties for tweakable hash function f *)
clone import TweakableHashFunctions as F with
  type pp_t <- pseed,
  type tw_t <- adrs,
  type in_t <- dgst,
  type out_t <- dgstblock,

  op f <- f,

  op dpp <- dpseed

  proof *.
  realize dpp_ll by exact: dpseed_ll.

clone import Collection as FC with
  type diff <- int,
  
    op get_diff <- size,
  
    op fc <- thfc
    
  proof *.
  realize in_collection by exists (8 * n).
  
clone import FC.SMDTUDC as FC_UD with
  op t_smdtud <- d * len,

  op din <- ddgstblocklift,
  op dout <- ddgstblock
  
  proof *.
  realize ge0_tsmdtud by smt(IntOrder.mulr_ge0 ge1_d ge2_len val_w).
  realize din_ll by exact: ddgstblocklift_ll.
  realize dout_ll by exact: ddgstblock_ll.
  
clone import FC.SMDTTCRC as FC_TCR with
  op t_smdttcr <- d * len * w

  proof *.
  realize ge0_tsmdttcr by smt(IntOrder.mulr_ge0 ge1_d ge2_len val_w).
    
clone import FC.SMDTPREC as FC_PRE with
  op t_smdtpre <- d * len,
  
  op din <- ddgstblocklift
  
  proof *.
  realize ge0_tsmdtpre by smt(IntOrder.mulr_ge0 ge1_d ge2_len).
  realize din_ll by exact: ddgstblocklift_ll.
  
  
(* - (Tweakable hash) Function chains - *)
(* 
  Chain function that chains (i.e., repeatedly applies) a given tweakable hash function 
  Interpretation of arguments is, respectively, as follows:
  - Tweakable hash function to chain
  - Public seed
  - Address (should be of chaining type (chtype))
  - Current position/index in chain
  - Number of times to chain the tweakable hash function
  - Input to apply the tweakable hash function on
*)
op ch : (pseed -> adrs -> dgst -> dgstblock) -> pseed -> adrs -> int -> int -> dgst -> dgstblock.

(* Chain specifically for tweakable hash function f *)
op cf : pseed -> adrs -> int -> int -> dgst -> dgstblock = ch f.

(* Chaining ('less than or equal to') 0 times returns input value *)
axiom ch0 (g : pseed -> adrs -> dgst -> dgstblock) (ps : pseed) (ad : adrs) (s i : int) (x : dgst) :
     valid_wadrs ad
  => size x = 8 * n
  => i <= 0 
  => ch g ps ad s i x = insubd x.

(* Recursive step of ch starting at the end of the chain *)
axiom chS (g : pseed -> adrs -> dgst -> dgstblock) (ps : pseed) (ad : adrs) (s i : int) (x : dgst) :
     valid_wadrs ad
  => size x = 8 * n
  => 0 <= s
  => 0 < i 
  => s + i <= w - 1 
  => ch g ps ad s i x = g ps (set_hidx ad (s + i - 1)) (val (ch g ps ad s (i - 1) x)).

(* Chaining a single time is equivalent to applying the function once *)
lemma ch1 (g : pseed -> adrs -> dgst -> dgstblock) (ps : pseed) (ad : adrs) (s : int) (x : dgst) : 
     valid_wadrs ad
  => size x = 8 * n
  => 0 <= s 
  => s + 1 <= w - 1 
  => ch g ps ad s 1 x = g ps (set_hidx ad s) x.
proof. by move=> *; rewrite chS 6:ch0 9:insubdK. qed.

(* 
  Chaining i + j times starting from position s (and valid chain adrs) is equivalent to 
  first chaining i times (starting from position s (and valid chain adrs) and 
  then chaining j times (starting from s + i and updated adrs with the updated input)
*)
lemma ch_comp (g : pseed -> adrs -> dgst -> dgstblock) (ps : pseed) (ad : adrs) (s i j : int) (x : dgst) :
     valid_wadrs ad
  => size x = 8 * n
  => 0 <= s 
  => 0 <= i 
  => 0 <= j 
  => s + i + j <= w - 1 
  => ch g ps ad s (i + j) x = ch g ps ad (s + i) j (val (ch g ps ad s i x)).  
proof.
move=> + + + + ge0_j +; elim: j ge0_j s i ad x => //=.
+ by move=> *; rewrite (ch0 _ _ _ _ 0) 2:valP 4:valKd.
move=> j ge0_j ih s i ad x adch eq8n_szx ge0_s ge0_i gesij1_w1.
case (j = 0) => [-> /= | neq0_j]; first by rewrite ch1 2:valP 5:chS // /#.
by rewrite chS 6:(chS _ _ _ _ (j + 1)) 7:valP //= 5:-ih // /#.
qed.

(* Recursive step of ch starting at the beginning of the chain *)
lemma chSA (g : pseed -> adrs -> dgst -> dgstblock) (ps : pseed) (ad : adrs) (s i : int) (x : dgst) :
     valid_wadrs ad
  => size x = 8 * n 
  => 0 <= s 
  => 0 < i 
  => s + i <= w - 1 
  => ch g ps ad s i x = ch g ps ad (s + 1) (i - 1) (val (g ps (set_hidx ad s) x)).
proof.
move=> adch eq8n_szx; case (0 <= i) => [ge0_i ge0_s gt0_i | /ltzNge /#].
elim: i ge0_i gt0_i => [// | i ge0_i].
case (i = 0) => [-> /= lew1_s1 | neq0_i].
+ by rewrite ch1 5:ch0 6:valP 8:valKd.
move=> + gt0_i1 lew1_si1; move=> /(_ _ _); first 2 by smt(). 
move=> ih /=; rewrite chS // addrA /= ih (: s + i = (s + 1 + i - 1)) 1:/#.
by rewrite -chS 2:valP // /#.
qed.


(* - Message encoding - *)
op encode_msgWOTS : msgWOTS -> emsgWOTS.

(* For any two different messages, the encodings differ in at least one digit *)
axiom two_encodings (m m' : msgWOTS) : 
     m <> m'
  => exists (i : int),
          0 <= i < len
       /\ BaseW.val (encode_msgWOTS m).[i] < BaseW.val (encode_msgWOTS m').[i].

(* Each encoded message contains at least one digit that is different from 0 *)  
lemma exenc_neq0 (m : msgWOTS) :
  exists (i : int), (0 <= i < len) /\ BaseW.val (encode_msgWOTS m).[i] <> 0.
proof.
move: (two_encodings (insubd ((put (val m) 0 (! (nth witness (val m) 0))))) m _).
+ pose pm := DigestBlock.insubd _. 
  have: val pm <> val m; last by apply contraLR => /= ->.
  rewrite /pm insubdK 1:size_put 1:valP //.
  apply (neq_from_nth witness _ _ 0).
  by rewrite nth_put 1:valP; smt(ge1_n).
elim=> i [rng_i ltvm_vpm].
by exists i; smt(BaseW.valP).
qed.
     

(* -- Proof-specific -- *)
(* - (Chain) Collisions - *)
(* Checks whether the i-th pair of chains contain a collision *)
op is_chwcoll (ps : pseed) (ad : adrs) (em em' : emsgWOTS) (sig sig' : sigWOTS) =
  fun (i : int) =>   
     BaseW.val em'.[i] < BaseW.val em.[i]
  /\ cf ps (set_chidx ad i) (BaseW.val em'.[i]) (BaseW.val em.[i] - BaseW.val em'.[i]) (val (nth witness (val sig') i))
     <> 
     nth witness (val sig) i.

(* Checks whether there is a pair of chains that contain a collision *)
op has_chwcoll (ps : pseed) (ad : adrs) (em em' : emsgWOTS) (sig sig' : sigWOTS) : bool =
  has (is_chwcoll ps ad em em' sig sig') (range 0 len).

(* Finds index of the first chain pair in which a collision occurs *)    
op find_chwcollidx (ps : pseed) (ad : adrs) (em em' : emsgWOTS) (sig sig' : sigWOTS) : int =
  find (is_chwcoll ps ad em em' sig sig') (range 0 len).

(* Checks whether the chain elements at index (i + em_ele) collide *)
op is_coll (ps : pseed) (ad : adrs) (em_ele em_ele' : int) (sig_ele sig_ele' : dgst) =
  fun (i : int) =>
    cf ps ad em_ele i sig_ele = cf ps ad em_ele' (i + em_ele - em_ele') sig_ele'.

(* Checks whether there is a pair of elements in the chains that collide *)
op has_coll (ps : pseed) (ad : adrs) (em_ele em_ele' : int) (sig_ele sig_ele' : dgst) : bool =
  has (is_coll ps ad em_ele em_ele' sig_ele sig_ele') (range 1 (w - em_ele)).

(* Finds number of iterations to apply on the original chain to obtain (one part of) the collision *)
op find_collidx_l (ps : pseed) (ad : adrs) (em_ele em_ele' : int) (sig_ele sig_ele' : dgst) : int = 
  (find (is_coll ps ad em_ele em_ele' sig_ele sig_ele') (range 1 (w - em_ele))).

(* Finds number of iterations to apply on the forgery chain to obtain (the remaining part of) the collision *)
op find_collidx_r (ps : pseed) (ad : adrs) (em_ele em_ele' : int) (sig_ele sig_ele' : dgst) : int = 
  find_collidx_l ps ad em_ele em_ele' sig_ele sig_ele' + em_ele - em_ele'.

(* Extracts (one part of) the collision from the original chain *)
op extr_coll_l (ps : pseed) (ad : adrs) (em_ele em_ele' : int) (sig_ele sig_ele' : dgst) : dgstblock =
  let i = find_collidx_l ps ad em_ele em_ele' sig_ele sig_ele' in 
    cf ps ad em_ele i sig_ele.

(* Extracts (the other part of) the collision from the forgery chain *)
op extr_coll_r (ps : pseed) (ad : adrs) (em_ele em_ele' : int) (sig_ele sig_ele' : dgst) : dgstblock =
  let i = find_collidx_r ps ad em_ele em_ele' sig_ele sig_ele' in 
    cf ps ad em_ele' i sig_ele'.

(* 
  If there is a pair of chains that contains a collision, then 
  find_chwcollidx is between 0 and len
*)
lemma hchwcoll_findchrng (ps : pseed) (ad : adrs) (em em' : emsgWOTS) (sig sig' : sigWOTS) :
     has_chwcoll ps ad em em' sig sig' 
  => 0 <= find_chwcollidx ps ad em em' sig sig' < len.
proof. 
move => *; split; first by smt(find_ge0 size_range ge2_len has_find). 
by move => *; rewrite /find_chwcollidx; smt(find_ge0 size_range ge2_len has_find).  
qed.

(* 
  If the final elements of the pair of chains at index find_chwcollidx are equal and there 
  exists a pair of chains that contain a collision, then the pair of chains at index 
  find_chwcollidx contain a collision
*)
lemma hchwcoll_hcoll (ps : pseed) (ad : adrs) (em em' : emsgWOTS) (sig sig' : sigWOTS) :
  let i = find_chwcollidx ps ad em em' sig sig' in
     cf ps (set_chidx ad i) (BaseW.val em.[i]) (w - 1 - BaseW.val em.[i]) (val (nth witness (val sig) i)) 
     = 
     cf ps (set_chidx ad i) (BaseW.val em'.[i]) (w - 1 - BaseW.val em'.[i]) (val (nth witness (val sig') i))
  => valid_wadrs ad 
  => has_chwcoll ps ad em em' sig sig' 
  => has_coll ps (set_chidx ad i) (BaseW.val em.[i]) (BaseW.val em'.[i]) (val (nth witness (val sig) i)) (val (nth witness (val sig') i)).
proof.
move=> i eq_cf adch hchwcoll. 
have := (hchwcoll_findchrng ps ad em em' sig sig' hchwcoll); rewrite -/i => rng_i.
move/(nth_find witness): hchwcoll. 
rewrite nth_range //= -/i /is_chwcoll; elim => ltem_emp neq_nthsig.
case (BaseW.val em.[i] = w - 1) => [eqw1_em | neqw1_em].
+  move: eq_cf neq_nthsig.
   rewrite eqw1_em /cf ch0 // 1:validwadrs_setchidx 3:valP 4:valKd // => -> //.
rewrite /has_coll hasP -negbK negb_exists /=; apply negP => nincoll.
by move: (nincoll (w - 1 - BaseW.val em.[i])); smt(mem_range BaseW.valP). 
qed.

(*
  If the final elements of the pair of chains at index find_chwcollidx are equal and there 
  exists a pair of chains that contain a collision, then find_collidx_l (i.e., the number of iterations
  needed to obtain (one part of) the collision from the original chain) is within 0 (including) and
  w - 1 - BaseW.val em.[i] (excluding)
*)
lemma hchwcoll_findlcollrng (ps : pseed) (ad : adrs) (em em' : emsgWOTS) (sig sig' : sigWOTS) :
  let i = find_chwcollidx ps ad em em' sig sig' in
     cf ps (set_chidx ad i) (BaseW.val em.[i]) (w - 1 - BaseW.val em.[i]) (val (nth witness (val sig) i)) 
     = 
     cf ps (set_chidx ad i) (BaseW.val em'.[i]) (w - 1 - BaseW.val em'.[i]) (val (nth witness (val sig') i))
  => valid_wadrs ad
  => has_chwcoll ps ad em em' sig sig' 
  => 0 
     <= 
     find_collidx_l ps (set_chidx ad i) (BaseW.val em.[i]) (BaseW.val em'.[i]) (val (nth witness (val sig) i)) (val (nth witness (val sig') i)) 
     < 
     w - 1 - BaseW.val em.[i].
proof.
move=> i eq_cf adch hchwcoll.
split => [|_]; first by apply find_ge0.  
have ->: w - 1 - BaseW.val em.[i] = size (range 1 (w - BaseW.val em.[i])) by smt(size_range BaseW.valP).
by apply /has_find /hchwcoll_hcoll.
qed.

(*
  If the final elements of the pair of chains at index find_chwcollidx are equal and there 
  exists a pair of chains that contain a collision, then find_collidx_r (i.e., the number of iterations
  needed to obtain (the other part of) the collision from the forgery chain) is within 
  BaseW.val em.[i] - BaseW.val em'.[i] (including) and w - 1 - BaseW.val em'.[i] (excluding)
*)
lemma hchwcoll_findrcollrng (ps : pseed) (ad : adrs) (em em' : emsgWOTS) (sig sig' : sigWOTS) :
  let i = find_chwcollidx ps ad em em' sig sig' in
     cf ps (set_chidx ad i) (BaseW.val em.[i]) (w - 1 - BaseW.val em.[i]) (val (nth witness (val sig) i)) 
     = 
     cf ps (set_chidx ad i) (BaseW.val em'.[i]) (w - 1 - BaseW.val em'.[i]) (val (nth witness (val sig') i)) 
  => valid_wadrs ad
  => has_chwcoll ps ad em em' sig sig' 
  => BaseW.val em.[i] - BaseW.val em'.[i] 
     <= 
     find_collidx_r ps (set_chidx ad i) (BaseW.val em.[i]) (BaseW.val em'.[i]) (val (nth witness (val sig) i)) (val (nth witness (val sig') i)) 
     < 
     w - 1 - BaseW.val em'.[i].
proof. by smt(hchwcoll_findlcollrng). qed.

(*
  If the final elements of the pair of chains at index find_chwcollidx are equal and there 
  exists a pair of chains that contain a collision, then we can extract the collision
  via extr_coll_l and extr_coll_r
*)
lemma collision_extraction (ps : pseed) (ad : adrs) (em em' : emsgWOTS) (sig sig' : sigWOTS) :
  let i = find_chwcollidx ps ad em em' sig sig' in
  let k = find_collidx_l ps (set_chidx ad i) (BaseW.val em.[i]) (BaseW.val em'.[i]) (val (nth witness (val sig) i)) (val (nth witness (val sig') i)) in
  let l = find_collidx_r ps (set_chidx ad i) (BaseW.val em.[i]) (BaseW.val em'.[i]) (val (nth witness (val sig) i)) (val (nth witness (val sig') i)) in
  let cl = extr_coll_l ps (set_chidx ad i) (BaseW.val em.[i]) (BaseW.val em'.[i]) (val (nth witness (val sig) i)) (val (nth witness (val sig') i)) in
  let cr = extr_coll_r ps (set_chidx ad i) (BaseW.val em.[i]) (BaseW.val em'.[i]) (val (nth witness (val sig) i)) (val (nth witness (val sig') i)) in
     cf ps (set_chidx ad i) (BaseW.val em.[i]) (w - 1 - BaseW.val em.[i]) (val (nth witness (val sig) i)) 
     = 
     cf ps (set_chidx ad i) (BaseW.val em'.[i]) (w - 1 - BaseW.val em'.[i]) (val (nth witness (val sig') i))
  => valid_wadrs ad
  => has_chwcoll ps ad em em' sig sig'
  => val cl <> val cr
     /\
     f ps (set_hidx (set_chidx ad i) (BaseW.val em.[i] + k)) (val cl)
     =
     f ps (set_hidx (set_chidx ad i) (BaseW.val em'.[i] + l)) (val cr).
proof.
move=> i k l cl cr eq_cf adch hchwcoll.
have rng_i: 0 <= i < len by apply hchwcoll_findchrng.
have hcoll: has_coll ps (set_chidx ad i) (BaseW.val em.[i]) (BaseW.val em'.[i]) (val (nth witness (val sig) i)) (val (nth witness (val sig') i)) by apply hchwcoll_hcoll.
have rng_k : 0 <= k < w - 1 - BaseW.val em.[i] by apply hchwcoll_findlcollrng.
have rng_l : BaseW.val em.[i] - BaseW.val em'.[i] <= l < w - 1 - BaseW.val em'.[i] by apply hchwcoll_findrcollrng.
move/(nth_find witness): hchwcoll; rewrite nth_range //= -/i /is_chwcoll; elim => ltem_emp neq_nthsig.
split.
+ rewrite /cl /cr /extr_coll_l /extr_coll_r /= -/cf /find_collidx_r /find_collidx_l.
  case (k = 0) => [@/k @/find_collidx_l -> /= | neq0_k].
  - rewrite /cf ch0 1:validwadrs_setchidx 3:valP 5:valKd // eq_sym.
    pose chn := ch _ _ _ _ _ _; move: DigestBlock.val_inj.
    by move => @/injective /(_ chn (nth witness (val sig) i)) /contra /#.
  have /(_ _) := 
    (before_find witness 
    (is_coll ps (set_chidx ad i) (BaseW.val em.[i]) (BaseW.val em'.[i]) 
                (val (nth witness (val sig) i)) (val (nth witness (val sig') i))) 
    (range 1 (w - BaseW.val em.[i]))
    (k - 1)).
  - by smt().
  by smt(DigestBlock.val_inj nth_range).
rewrite /cl /cr /extr_coll_l /extr_coll_r /= -/k -/l.
rewrite {1}(: BaseW.val em.[i] + k = BaseW.val em.[i] + (k + 1) - 1) 1:/# 
        {1}(: BaseW.val em'.[i] + l = BaseW.val em'.[i] + (l + 1) - 1) 1:/#.
do 2! (rewrite /cf -chS 1:validwadrs_setchidx 3:valP //; first 3 by smt(BaseW.valP)).
by move/(nth_find witness): hcoll; rewrite nth_range 1:/# {1}/is_coll -/cf /#.
qed.


(* - (Chain) Preimages - *)
(* Checks whether there is a preimage in the i-th chain *)
op is_chwpre (ps : pseed) (ad : adrs) (em em' : emsgWOTS) (sig sig' : sigWOTS) =
  fun (i : int),   
     BaseW.val em'.[i] < BaseW.val em.[i]
  /\ cf ps (set_chidx ad i) (BaseW.val em'.[i]) (BaseW.val em.[i] - BaseW.val em'.[i]) (val (nth witness (val sig') i))
     = 
     nth witness (val sig) i.  

(* Checks whether there is a chain that contains a preimage *)   
op has_chwpre (ps : pseed) (ad : adrs) (em em' : emsgWOTS) (sig sig' : sigWOTS) =
  has (is_chwpre ps ad em em' sig sig') (range 0 len).

(* Finds the index of first chain that contains a preimage *)
op find_chwpreidx (ps : pseed) (ad : adrs) (em em' : emsgWOTS) (sig sig' : sigWOTS) : int = 
  find (is_chwpre ps ad em em' sig sig') (range 0 len).

(* Extracts a preimage from the i-th chain *)
op extr_pre (ps : pseed) (ad : adrs) (em_ele em_ele' : int) (sig_ele' : dgst) : dgstblock =
  cf ps ad em_ele' (em_ele - em_ele' - 1) sig_ele'. 

(* 
  If there does not exists a chain collision for two different messages of the correct length, 
  then there exists a chain preimage
*)
lemma nhchwcoll_hchwpre (ps : pseed) (ad : adrs) (m m' : msgWOTS) (sig sig' : sigWOTS) :
     m <> m'
  => !has_chwcoll ps ad (encode_msgWOTS m) (encode_msgWOTS m') sig sig'
  => has_chwpre ps ad (encode_msgWOTS m) (encode_msgWOTS m') sig sig'.
proof.
rewrite eq_sym /has_chwcoll /has_chwpre /is_chwcoll /is_chwpre => neqm_mpeqlen_szmp.
move: (two_encodings m' m _) => // [i] [#] ge0_i ltlen_i ltem_emp.
rewrite hasPn hasP /= => nchwcoll.
exists i; rewrite mem_range ge0_i ltlen_i /=.
move: (nchwcoll i _); first by rewrite mem_range. 
by rewrite negb_and ltem_emp.
qed.

(* If there is chain that contains a preimage, then find_chwpreidx is between 0 and len *)
lemma hchwpre_findprerng (ps : pseed) (ad : adrs) (m m' : msgWOTS) (sig sig' : sigWOTS) :
     has_chwpre ps ad (encode_msgWOTS m) (encode_msgWOTS m') sig sig'
  => 0 <= find_chwpreidx ps ad (encode_msgWOTS m) (encode_msgWOTS m') sig sig' < len.
proof.
move=> hchwpre; rewrite find_ge0 /= /find_chwpreidx {2}(: len = size (range 0 len)).
+ by rewrite size_range; smt(ge2_len).
by rewrite -has_find; move: hchwpre => @/has_chwpre.
qed.
  
(* 
  If there is chain that contains a preimage, then the digit of the encoded message at 
  find_chwpreidx is not 0 
*)
lemma hchwpre_neq0_findchwpre (ps : pseed) (ad : adrs) (m m' : msgWOTS) (sig sig' : sigWOTS) :
     has_chwpre ps ad (encode_msgWOTS m) (encode_msgWOTS m') sig sig'
  => BaseW.val (encode_msgWOTS m).[find_chwpreidx ps ad (encode_msgWOTS m) (encode_msgWOTS m') sig sig'] <> 0.
proof.
move=> hchwpre; move/(nth_find witness): (hchwpre) => @/find_chwpreidx @/is_chwpre /=.
by rewrite nth_range /= => [| [ltm _]]; [apply hchwpre_findprerng | smt(BaseW.valP)].
qed.


(* - Relations between oracle queries in reductions - *)
(* Overall relation between addresses in signing oracle and challenge oracle queries in SM-DT-UD hybrid reduction *)
op relcqsad_udi (qs : (adrs * msgWOTS * pkWOTS * sigWOTS) list) (j : int) : adrs list =
  flatten (map (
            fun (admpksig : adrs * msgWOTS * pkWOTS * sigWOTS) =>
              flatten (mkseq (fun (i : int) => 
                                if j < BaseW.val (encode_msgWOTS admpksig.`2).[i] - 1
                                then [set_hidx (set_chidx admpksig.`1 i) j]
                                else []) len)) qs).

(* Intermediate relation (while-loop) between addresses in signing oracle and challenge oracle queries in SM-DT-UD hybrid reduction *)
op relcqsad_udi_outer (ad : adrs) (m : msgWOTS) (j l : int) : adrs list =
  flatten (mkseq (fun (i : int) => 
                    if j < BaseW.val (encode_msgWOTS m).[i] - 1
                    then [set_hidx (set_chidx ad i) j]
                    else []) l).

(* 
  The result of applying relcqsad_udi on a query list does not depend on the 
  public keys and signatures of the queries in the query list 
*)
lemma relcqsadudi_rcons_qs (qs : (adrs * msgWOTS * pkWOTS * sigWOTS) list) (j : int) (ad : adrs) (m : msgWOTS) (pk pk' : pkWOTS) (sig sig' : sigWOTS) :
  relcqsad_udi (rcons qs (ad, m, pk, sig)) j = relcqsad_udi (rcons qs (ad, m, pk', sig')) j.
proof. by rewrite /relcqsad_udi; congr; rewrite 2!map_rcons. qed.

(* Interaction between relcqsad_udi and relcqsad_udi_outer *)                   
lemma relcqsad_udi_outer_full (qs : (adrs * msgWOTS * pkWOTS * sigWOTS) list) (j : int) (ad : adrs) (m : msgWOTS) (pk : pkWOTS) (sig : sigWOTS) :
  relcqsad_udi qs j ++ relcqsad_udi_outer ad m j len
  =
  relcqsad_udi (rcons qs (ad, m, pk, sig)) j.
proof. by rewrite /relcqsad_udi -flatten_rcons; congr; rewrite map_rcons. qed.

(* Extension of relcqsad_udi_outer ad m j l to relcqsad_udi_outer ad m j (l + 1) *)
lemma relcqsad_udi_outer_cat (ad : adrs) (m : msgWOTS) (j l : int) :
     0 <= l
  => relcqsad_udi_outer ad m j l ++ (if j < BaseW.val (encode_msgWOTS m).[l] - 1
                                     then [set_hidx (set_chidx ad l) j]
                                     else [])
     =
     relcqsad_udi_outer ad m j (l + 1).
proof. smt(flatten_rcons mkseqS). qed.

(* Range in which relcqsad_udi qs j lies *)
lemma relcqsadudi_rng (qs : (adrs * msgWOTS * pkWOTS * sigWOTS) list) (j : int) :
  0 <= size (relcqsad_udi qs j) <= size qs * len.
proof.
rewrite /relcqsad_udi size_flatten sumzE 2!big_map /(\o) /= /predT -/predT.
split => [| _].
+ rewrite (: 0 = 0 * count predT qs) // -big_constz.
  rewrite ler_sum_seq => q qin @/predT /=.
  by rewrite size_flatten sumz_ge0 map_size_ge0.
rewrite -count_predT -(Ring.IntID.mul1r (count _ _)) -big_constz mulr_suml /=.
rewrite ler_sum_seq => q @/predT /= qin.
rewrite size_flatten sumzE 2!big_map /(\o) /= /predT -/predT. 
rewrite {2}(: len = size (iota_ 0 len)) 1:size_iota; first by smt(ge2_len).
rewrite -count_predT -(Ring.IntID.mul1r (count _ _)) -big_constz.
rewrite ler_sum_seq => i /mem_iota /= rng_i @/predT /=.
by case (j < BaseW.val (encode_msgWOTS q.`2).[i] - 1).
qed.

(* Overall (partial) relation between addresses in signing oracle and family oracle queries in SM-DT-UD hybrid reduction *)
op reltqsad_udi (qs : (adrs * msgWOTS * pkWOTS * sigWOTS) list) (j : int) : adrs list =
  flatten (map (
            fun (admpksig : adrs * msgWOTS * pkWOTS * sigWOTS) =>
              flatten (mkseq (fun (i : int) =>
                               let em_ele = BaseW.val (encode_msgWOTS admpksig.`2).[i] in
                                if j < em_ele - 1
                                then mkseq (fun (k : int) =>
                                      set_hidx (set_chidx admpksig.`1 i) (j + 1 + k)) (w - 2 - j)
                                else if em_ele <> 0
                                     then mkseq (fun (k : int) =>
                                            set_hidx (set_chidx admpksig.`1 i) (em_ele - 1 + k)) (w - em_ele)
                                     else mkseq (fun (k : int) =>
                                            set_hidx (set_chidx admpksig.`1 i) (em_ele + k)) (w - 1 - em_ele)) len)) qs).

(* 
  The result of applying reltqsad_udi on a query list does not depend on the 
  public keys and signatures of the queries in the query list 
*)                                          
lemma reltqsadudi_rcons_qs (qs : (adrs * msgWOTS * pkWOTS * sigWOTS) list) (j : int) (ad : adrs) (m : msgWOTS) (pk pk' : pkWOTS) (sig sig' : sigWOTS) :
  reltqsad_udi (rcons qs (ad, m, pk, sig)) j = reltqsad_udi (rcons qs (ad, m, pk', sig')) j.
proof. by rewrite /reltqsad_udi; congr; rewrite 2!map_rcons. qed.
                                                   
(* Overall relation between addresses in signing oracle and challenge oracle queries in SM-DT-TCR reduction *)
op relcqsad_tcr (qs : (adrs * msgWOTS * pkWOTS * sigWOTS) list) : adrs list =
  flatten (map (
            fun (admpksig : adrs * msgWOTS * pkWOTS * sigWOTS) =>
              flatten (mkseq (fun (i : int) =>
                               if BaseW.val (encode_msgWOTS admpksig.`2).[i] <> 0
                               then mkseq 
                                    (fun (j : int) => set_hidx (set_chidx admpksig.`1 i) (BaseW.val (encode_msgWOTS admpksig.`2).[i] - 1 + j))
                                    (w - (BaseW.val (encode_msgWOTS admpksig.`2).[i]))
                               else mkseq 
                                    (fun (j : int) => set_hidx (set_chidx admpksig.`1 i) (BaseW.val (encode_msgWOTS admpksig.`2).[i] + j)) 
                                    (w - 1 - (BaseW.val (encode_msgWOTS admpksig.`2).[i]))) len)) qs).

(* Intermediate relation (outer while-loop) between addresses in signing oracle and challenge oracle queries in SM-DT-TCR reduction *)
op relcqsad_tcr_outer (ad : adrs) (m : msgWOTS) (l : int) : adrs list =
  flatten (mkseq (fun (i : int) =>
                    if BaseW.val (encode_msgWOTS m).[i] <> 0
                    then mkseq 
                        (fun (j : int) => set_hidx (set_chidx ad i) (BaseW.val (encode_msgWOTS m).[i] - 1 + j))
                        (w - (BaseW.val (encode_msgWOTS m).[i]))
                    else mkseq 
                        (fun (j : int) => set_hidx (set_chidx ad i) (BaseW.val (encode_msgWOTS m).[i] + j)) 
                        (w - 1 - (BaseW.val (encode_msgWOTS m).[i]))) l).

(* Intermediate relation (inner while-loop) between addresses in signing oracle and challenge oracle queries in SM-DT-TCR reduction *)
op relcqsad_tcr_inner (ad : adrs) (em_ele : int) (k : int) : adrs list =
  if em_ele <> 0
  then mkseq 
      (fun (j : int) => set_hidx ad (em_ele - 1 + j)) (k + 1)
  else mkseq 
      (fun (j : int) => set_hidx ad (em_ele + j)) k.

(* Interaction between relcqsad_tcr and relcqsad_tcr_outer *)
lemma relcqsad_tcr_outer_full (qs : (adrs * msgWOTS * pkWOTS * sigWOTS) list) (ad : adrs) (m : msgWOTS) (pk : pkWOTS) (sig : sigWOTS) :
  relcqsad_tcr qs ++ relcqsad_tcr_outer ad m len
  =
  relcqsad_tcr (rcons qs (ad, m, pk, sig)).
proof. by rewrite /relcqsad_tcr -flatten_rcons; congr; rewrite map_rcons. qed.

(* Interaction between relcqsad_tcr_outer and relcqsad_tcr_inner *)
lemma relcqsad_tcr_outer_inner_full (ad : adrs) (m : msgWOTS) (i : int) :
     0 <= i 
  => relcqsad_tcr_outer ad m i 
     ++ 
     relcqsad_tcr_inner (set_chidx ad i) (BaseW.val (encode_msgWOTS m).[i]) (w - 1 - (BaseW.val (encode_msgWOTS m).[i]))
     =
     relcqsad_tcr_outer ad m (i + 1).
proof.
move=> ge0_i @/relcqsad_tcr_outer @/relcqsad_tcr_inner.
by rewrite -flatten_rcons; congr; rewrite eq_sym mkseqS //; congr; smt().
qed.

(* Extension of relcqsad_tcr_inner ad em_ele j to relcqsad_tcr_inner ad em_ele (j + 1) *)
lemma relcqsad_tcr_inner_rcons (ad : adrs) (em_ele : int) (j : int) :
     0 <= j 
  => rcons (relcqsad_tcr_inner ad em_ele j) (if em_ele <> 0 
                                             then set_hidx ad (em_ele - 1 + (j + 1))
                                             else set_hidx ad (em_ele + j))
     =
     relcqsad_tcr_inner ad em_ele (j + 1).
proof. by smt(mkseqS). qed.

(* Range in which relcqsad_tcr qs lies *)
lemma relcqsadtcr_rng (qs : (adrs * msgWOTS * pkWOTS * sigWOTS) list) :
  size qs <= size (relcqsad_tcr qs) <= size qs * len * w.
proof.
rewrite -count_predT -(Ring.IntID.mul1r (count _ _)) -big_constz.
rewrite /relcqsad_tcr size_flatten sumzE 2!big_map /(\o) /= /predT -/predT. 
split => [ | _].
+ rewrite ler_sum_seq => q @/predT /= qin.
  rewrite size_flatten sumzE 2!big_map /(\o) /= /predT -/predT.
  rewrite (: len = 1 + (len - 1)) 2:iota_add //= 2:big_cat; first by smt(ge2_len).
  rewrite ler_paddr 1:sumr_ge0 /=; first by smt(size_map size_ge0).
  rewrite iota1 /big filter_predT foldr_map /=.
  by case (BaseW.val (encode_msgWOTS q.`2).[0] <> 0); smt(size_map size_iota BaseW.valP val_w). 
rewrite 2!mulr_suml /= ler_sum_seq => q @/predT /= qin.
rewrite size_flatten sumzE 2!big_map /(\o) /= /predT -/predT /=.
rewrite {2}(: len = size (iota_ 0 len)) 2:-count_predT; first by smt(size_iota ge2_len).
rewrite -(Ring.IntID.mul1r (count _ _)) -big_constz mulr_suml ler_sum_seq => i /mem_iota /= rng_i _.
by case (BaseW.val (encode_msgWOTS q.`2).[i] <> 0); smt(size_map size_iota BaseW.valP).
qed.

(* Overall relation between digests in signing oracle and challenge oracle queries in SM-DT-TCR-C reduction *)
op relcqsdg_tcr (qs : (adrs * msgWOTS * pkWOTS * sigWOTS) list) (xll : dgstblock list list) (ps : pseed)  : dgst list =
  flatten (map (fun (admpksigxl : (adrs * msgWOTS * pkWOTS * sigWOTS) * dgstblock list) =>
                  let (admpksig, xl) = (admpksigxl.`1, admpksigxl.`2) in
                    flatten (mkseq (fun (i : int) =>
                                    if BaseW.val (encode_msgWOTS admpksig.`2).[i] <> 0
                                    then mkseq
                                         (fun (j : int) => val (cf ps (set_chidx admpksig.`1 i) (BaseW.val (encode_msgWOTS admpksig.`2).[i] - 1) j (val (nth witness xl i))))
                                         (w - (BaseW.val (encode_msgWOTS admpksig.`2).[i]))
                                    else mkseq 
                                         (fun (j : int) => val (cf ps (set_chidx admpksig.`1 i) (BaseW.val (encode_msgWOTS admpksig.`2).[i]) j (val (nth witness (val admpksig.`4) i))))
                                         (w - 1 - (BaseW.val (encode_msgWOTS admpksig.`2).[i]))) len)) (zip qs xll)).

(* Intermediate relation (outer while-loop) between digests in signing oracle and challenge oracle queries in SM-DT-TCR-C reduction *)
op relcqsdg_tcr_outer (ps : pseed) (ad : adrs) (m : msgWOTS) (sig : sigWOTS) (xl : dgstblock list) (l : int) : dgst list =
  flatten (mkseq (fun (i : int) =>
                  if BaseW.val (encode_msgWOTS m).[i] <> 0
                  then mkseq
                       (fun (j : int) => val (cf ps (set_chidx ad i) (BaseW.val (encode_msgWOTS m).[i] - 1) j (val (nth witness xl i))))
                       (w - (BaseW.val (encode_msgWOTS m).[i]))
                  else mkseq 
                       (fun (j : int) => val (cf ps (set_chidx ad i) (BaseW.val (encode_msgWOTS m).[i]) j (val (nth witness (val sig) i))))
                       (w - 1 - (BaseW.val (encode_msgWOTS m).[i]))) l).

(* Intermediate relation (inner while-loop) between digests in signing oracle and challenge oracle queries in SM-DT-TCR-C reduction *)
op relcqsdg_tcr_inner (ps : pseed) (ad : adrs) (em_ele : int) (sig_ele : dgstblock) (x : dgstblock) (k : int) : dgst list =
  if em_ele <> 0
  then mkseq
       (fun (j : int) => val (cf ps ad (em_ele - 1) j (val x))) (k + 1)
  else mkseq 
       (fun (j : int) => val (cf ps ad em_ele j (val sig_ele))) k.

(* Interaction between relcqsdg_tcr and relcqsdg_tcr_outer *)
lemma relcqsdg_tcr_outer_full (qs : (adrs * msgWOTS * pkWOTS * sigWOTS) list) (xll : dgstblock list list) 
                                    (ps : pseed) (ad : adrs) (m : msgWOTS) (pk : pkWOTS) (sig : sigWOTS) (xl : dgstblock list) :
     size qs = size xll 
  => relcqsdg_tcr qs xll ps ++ relcqsdg_tcr_outer ps ad m sig xl len
     =
     relcqsdg_tcr (rcons qs (ad, m, pk, sig)) (rcons xll xl) ps.
proof. 
move=> eq_sz @/relcqsdg_tcr.
by rewrite -flatten_rcons; congr; rewrite zip_rcons 2:map_rcons.
qed.

(* Interaction between relcqsdg_tcr_outer and relcqsdg_tcr_inner *)
lemma relcqsdg_tcr_outer_inner_full (ps : pseed) (ad : adrs) (m : msgWOTS) (sig : sigWOTS) (xl : dgstblock list) (i : int) :
     0 <= i 
  => relcqsdg_tcr_outer ps ad m sig xl i 
     ++ 
     relcqsdg_tcr_inner ps (set_chidx ad i) (BaseW.val (encode_msgWOTS m).[i]) (nth witness (val sig) i) (nth witness xl i) (w - 1 - (BaseW.val (encode_msgWOTS m).[i]))
     =
     relcqsdg_tcr_outer ps ad m sig xl (i + 1).
proof.
move=> ge0_i @/relcqsdg_tcr_outer @/relcqsdg_tcr_inner.
by rewrite -flatten_rcons; congr; rewrite eq_sym mkseqS //; congr => /#.
qed.

(* Extension of relcqsdg_tcr_inner ps ad em_ele sig_ele x j to relcqsdg_tcr_inner ps ad em_ele sig_ele x (j + 1) *)
lemma relcqsdg_tcr_inner_rcons (ps : pseed) (ad : adrs) (em_ele : int) (sig_ele : dgstblock) (x : dgstblock) (j : int) :
  0 <= j 
  => rcons (relcqsdg_tcr_inner ps ad em_ele sig_ele x j) 
           (if em_ele <> 0
            then val (cf ps ad (em_ele - 1) (j + 1) (val x))
            else val (cf ps ad em_ele j (val sig_ele)))
     =
     relcqsdg_tcr_inner ps ad em_ele sig_ele x (j + 1).
proof. by smt(mkseqS). qed.

(* Overall relation between addresses in signing oracle and challenge oracle queries in SM-DT-PRE-C reduction *)
op relcqsad_pre (qs : (adrs * msgWOTS * pkWOTS * sigWOTS) list) : adrs list =
  flatten (map (fun (admpksig : adrs * msgWOTS * pkWOTS * sigWOTS) =>
                 flatten (mkseq (fun (i : int) => if BaseW.val (encode_msgWOTS admpksig.`2).[i] <> 0
                                                  then [set_hidx (set_chidx admpksig.`1 i) (BaseW.val (encode_msgWOTS admpksig.`2).[i] - 1)]
                                                  else []) len)) qs).
                                                  
(* Intermediate relation (outer while-loop) between addresses in signing oracle and challenge oracle queries in SM-DT-PRE-C reduction *)
op relcqsad_pre_outer (ad : adrs) (m : msgWOTS) (l : int) : adrs list =
  flatten (mkseq (fun (i : int) => if BaseW.val (encode_msgWOTS m).[i] <> 0
                                   then [set_hidx (set_chidx ad i) (BaseW.val (encode_msgWOTS m).[i] - 1)]
                                   else []) l).


(* Interaction between relcqsad_pre and relcqsad_pre_outer *)                                   
lemma relcqsad_pre_outer_full (qs : (adrs * msgWOTS * pkWOTS * sigWOTS) list) (ad : adrs) (m : msgWOTS) (pk : pkWOTS) (sig : sigWOTS) :
  relcqsad_pre qs ++ relcqsad_pre_outer ad m len = relcqsad_pre (rcons qs (ad, m, pk, sig)).
proof. by rewrite /relcqsad_pre /relcqsad_pre_outer map_rcons /= flatten_rcons. qed.
                                 
(* Overall relation between digests in signing oracle and challenge oracle queries in SM-DT-PRE reduction *)
op relcqsdg_pre (qs : (adrs * msgWOTS * pkWOTS * sigWOTS) list) : dgstblock list =
  flatten (map (fun (admpksig : adrs * msgWOTS * pkWOTS * sigWOTS) =>
                 flatten (mkseq (fun (i : int) => if BaseW.val (encode_msgWOTS admpksig.`2).[i] <> 0
                                                  then [nth witness (val admpksig.`4) i]
                                                  else []) len)) qs).
                                                 
(* Intermediate relation (outer while-loop) between addresses in signing oracle and challenge oracle queries in SM-DT-PRE-C reduction *)
op relcqsdg_pre_outer (m : msgWOTS) (sig : dgstblock list) (l : int) : dgstblock list =
  flatten (mkseq (fun (i : int) => if BaseW.val (encode_msgWOTS m).[i] <> 0
                                   then [nth witness sig i]
                                   else []) l).

(* Interaction between relcqsdg_pre and relcqsdg_pre_outer *) 
lemma relcqsdg_pre_outer_full (qs : (adrs * msgWOTS * pkWOTS * sigWOTS) list) (ad : adrs) (m : msgWOTS) (pk : pkWOTS) (sig : sigWOTS) :
  relcqsdg_pre qs ++ relcqsdg_pre_outer m (val sig) len = relcqsdg_pre (rcons qs (ad, m, pk, sig)).
proof. by rewrite /relcqsdg_pre /relcqsdg_pre_outer map_rcons /= flatten_rcons. qed.

(* Range in which relcqsad_pre lies *)
lemma relcqsadpre_rng (qs : (adrs * msgWOTS * pkWOTS * sigWOTS) list) :
  size qs <= size (relcqsad_pre qs) <= size qs * len.
proof.
rewrite -count_predT -(Ring.IntID.mul1r (count _ _)) -big_constz.
rewrite /relcqsad_pre size_flatten sumzE 2!big_map /(\o) /= /predT -/predT.
split => [|_].
+ rewrite ler_sum_seq => q @/predT /= qin.
  rewrite size_flatten sumzE 2!big_map /(\o) /= /predT -/predT.
  move: (exenc_neq0 q.`2).
  elim => i [[ge0_i ltlen_i] neq0_em]; rewrite (: len = i + (len - i)) 1:/#. 
  rewrite iota_add //= 1:/# (: len - i = 1 + (len - i - 1)) // iota_add // 1:/#.
  rewrite 2!big_cat addrCA ler_paddr 1:addr_ge0 1,2:sumr_ge0; first 2 by smt(size_ge0).
  by rewrite iota1 /big filter_predT foldr_map /= neq0_em.
rewrite mulr_suml /= ler_sum_seq => q @/predT /= qin. 
rewrite size_flatten sumzE 2!big_map /(\o) /= /predT -/predT /=.
rewrite {2}(: len = size (iota_ 0 len)) 1:size_iota /=; first by smt(ge2_len).
rewrite -count_predT -(Ring.IntID.mul1r (count _ _)) -big_constz.
rewrite ler_sum_seq => i /mem_iota [ge0_i /= ltlen_i] @/predT /=.
by case (BaseW.val (encode_msgWOTS q.`2).[i] <> 0).
qed.

(* Overall relation between addresses in signing oracle and family oracle queries in SM-DT-PRE reduction *)
op reltqsad_pre (qs : (adrs * msgWOTS * pkWOTS * sigWOTS) list) : adrs list =
  flatten (map (fun (admpksig : adrs * msgWOTS * pkWOTS * sigWOTS) =>
                 flatten (mkseq (fun (i : int) => 
                            mkseq (fun (j : int) =>
                              set_hidx (set_chidx admpksig.`1 i) (BaseW.val (encode_msgWOTS admpksig.`2).[i] + j))
                                (w - 1 - (BaseW.val (encode_msgWOTS admpksig.`2).[i]))) len)) qs).
                                
(* Intermediate relation (outer while-loop) between addresses in signing oracle and family oracle queries in SM-DT-PRE reduction *)
op reltqsad_pre_outer (ad : adrs) (m : msgWOTS) (l : int) : adrs list =
  flatten (mkseq (fun (i : int) => 
            mkseq (fun (j : int) =>
              set_hidx (set_chidx ad i) (BaseW.val (encode_msgWOTS m).[i] + j))
                (w - 1 - (BaseW.val (encode_msgWOTS m).[i]))) l).

(* Intermediate relation (inner while-loop) between addresses in signing oracle and family oracle queries in SM-DT-PRE reduction *)
op reltqsad_pre_inner (ad : adrs) (em_ele : int) (k : int) : adrs list =
  mkseq (fun (j : int) => set_hidx ad (em_ele + j)) k.

(* Interaction between reltqsad_pre and reltqsad_pre_outer *)
lemma reltqsad_pre_outer_full (qs : (adrs * msgWOTS * pkWOTS * sigWOTS) list) (ad : adrs) (m : msgWOTS) (pk : pkWOTS) (sig : sigWOTS) :
  reltqsad_pre qs ++ reltqsad_pre_outer ad m len = reltqsad_pre (rcons qs (ad, m, pk, sig)).
proof. by rewrite /reltqsad_pre /reltqsad_pre_outer map_rcons /= flatten_rcons. qed.

(* Interaction between reltqsad_pre_outer and reltqsad_pre_inner *)
lemma reltqsad_pre_outer_inner_full (ad : adrs) (m : msgWOTS) (i : int) :
     0 <= i 
  => reltqsad_pre_outer ad m i 
     ++ 
     reltqsad_pre_inner (set_chidx ad i) (BaseW.val (encode_msgWOTS m).[i]) (w - 1 - BaseW.val (encode_msgWOTS m).[i])  
     = 
     reltqsad_pre_outer ad m (i + 1).
proof. 
move=> ge0_i @/reltqsad_pre_outer @/reltqsad_pre_inner.
by rewrite {2}/mkseq iota_add //= map_cat iota1 //= flatten_cat flatten_seq1.
qed.

(* Extension of reltqsad_pre_inner ad em_ele j to reltqsad_pre_inner ad em_ele (j + 1)  *)
lemma reltqsad_pre_inner_rcons (ad : adrs) (em_ele : int) (j : int) :
     0 <= j 
  => rcons (reltqsad_pre_inner ad em_ele j) (set_hidx ad (em_ele + j))  
     = 
     reltqsad_pre_inner ad em_ele (j + 1).
proof. 
move=> ge0_j @/reltqsad_pre_inner.
by rewrite /mkseq iota_add //= map_cat iota1 //= cats1.
qed.
                             
(* Computes index in query list of tweakable hash function oracles corresponding to extracted collision/preimage *)
op qs_idx (f : 'a -> 'b list list) (s : 'a list) (i j k : int) : int =
  sumz (map (fun x => sumz (map size x)) (take i (map f s))) + sumz (map size (take j (nth witness (map f s) i))) + k.

(* Computes index of address in query list of challenge oracle in SM-DT-TCR-C reduction corresponding to extracted collision *)
op qsadtcr_idx (qs : (adrs * msgWOTS * pkWOTS * sigWOTS) list) (i j k : int) : int =
  let f = (fun (admpksig : adrs * msgWOTS * pkWOTS * sigWOTS) =>
            (mkseq (fun (i : int) =>
                    if BaseW.val (encode_msgWOTS admpksig.`2).[i] <> 0
                    then mkseq 
                         (fun (j : int) => set_hidx (set_chidx admpksig.`1 i) (BaseW.val (encode_msgWOTS admpksig.`2).[i] - 1 + j))
                         (w - (BaseW.val (encode_msgWOTS admpksig.`2).[i]))
                    else mkseq 
                         (fun (j : int) => set_hidx (set_chidx admpksig.`1 i) (BaseW.val (encode_msgWOTS admpksig.`2).[i] + j))  
                         (w - 1 - (BaseW.val (encode_msgWOTS admpksig.`2).[i]))) len)) in
    qs_idx f qs i j k.

(* Computes index of digest in query list of challenge oracle in SM-DT-TCR-C reduction corresponding to extracted collision *)
op qsdgtcr_idx (qs : (adrs * msgWOTS * pkWOTS * sigWOTS) list) (xll : dgstblock list list) (ps : pseed) (i j k : int) : int =
  let f = (fun (admpksigxl : (adrs * msgWOTS * pkWOTS * sigWOTS) * dgstblock list) =>
                  let (admpksig, xl) = (admpksigxl.`1, admpksigxl.`2) in
                    (mkseq (fun (i : int) =>
                            if BaseW.val (encode_msgWOTS admpksig.`2).[i] <> 0
                            then mkseq
                                 (fun (j : int) => val (cf ps (set_chidx admpksig.`1 i) (BaseW.val (encode_msgWOTS admpksig.`2).[i] - 1) j (val (nth witness xl i))))
                                 (w - (BaseW.val (encode_msgWOTS admpksig.`2).[i]))
                            else mkseq 
                                 (fun (j : int) => val (cf ps (set_chidx admpksig.`1 i) (BaseW.val (encode_msgWOTS admpksig.`2).[i]) j (val (nth witness (val admpksig.`4) i))))
                                 (w - 1 - (BaseW.val (encode_msgWOTS admpksig.`2).[i]))) len)) in
    qs_idx f (zip qs xll) i j k.

(* Computes index of address in query list of challenge oracle in SM-DT-TCR-C reduction corresponding to extracted preimage *)
op qsadpre_idx (qs : (adrs * msgWOTS * pkWOTS * sigWOTS) list) (i j : int) : int =
  let f = (fun (admpksig : adrs * msgWOTS * pkWOTS * sigWOTS) =>
             (mkseq (fun (i : int) => if BaseW.val (encode_msgWOTS admpksig.`2).[i] <> 0
                                      then [set_hidx (set_chidx admpksig.`1 i) (BaseW.val (encode_msgWOTS admpksig.`2).[i] - 1)]
                                      else []) len)) in
    qs_idx f qs i j 0.

(* Computes index of digest in query list of challenge oracle in SM-DT-TCR-C reduction corresponding to extracted preimage *)
op qsdgpre_idx (qs : (adrs * msgWOTS * pkWOTS * sigWOTS) list) (i j : int) : int =
  let f = (fun (admpksig : adrs * msgWOTS * pkWOTS * sigWOTS) =>
             (mkseq (fun (i : int) => if BaseW.val (encode_msgWOTS admpksig.`2).[i] <> 0
                                      then [nth witness (val admpksig.`4) i]
                                      else []) len)) in
    qs_idx f qs i j 0.

(* Equality between qsadtcr_idx qs i j k and qsdgtcr_idx qs xll ps i j k *)
lemma eq_qsadtcridx_qsdgtcridx (qs : (adrs * msgWOTS * pkWOTS * sigWOTS) list) (xll : dgstblock list list) (ps : pseed) (i j k : int) :
     size qs = size xll
  => 0 <= i < size qs
  => qsadtcr_idx qs i j k = qsdgtcr_idx qs xll ps i j k.
proof.
move=> eq_sz rng_i.
rewrite /qsadtcr_idx /qsdgtcr_idx /qs_idx /=; do 2! congr; rewrite ?sumzE.
+ rewrite 2!big_mapT -2!map_take 2!big_mapT (big_nth witness) eq_sym (big_nth (witness, witness)).
  rewrite  /(\o) /predT -/predT ?size_take 3:(: i < size qs) 1..3:/#.
  rewrite (: i < size (zip qs xll)) 1:size_zip 1:/# /= &(eq_big_int) => m [ge0_m lti_m] /=.
  rewrite 2!sumzE 4!big_mapT /(\o) &(eq_big_seq) => x /mem_iota [ge0_x /= ltlen_x].
  rewrite ?nth_take // 1,2:/# nth_zip //=.
  by case (BaseW.val (encode_msgWOTS (nth witness qs m).`2).[x] <> 0) => _; rewrite 2!size_map.
rewrite 2!big_mapT (nth_map witness) // (nth_map (witness, witness)) /=; first by smt(size_zip).
rewrite -2!map_take 2!big_mapT /(\o) &(eq_big_seq) nth_zip // => x qin /=.
by case (BaseW.val (encode_msgWOTS (nth witness qs i).`2).[x] <> 0) => _; rewrite 2!size_map.
qed.

(* Equality between qsadpre_idx qs i j and qsdgpre_idx qs i j *)
lemma eq_qsadpreidx_qsdgpreidx (qs : (adrs * msgWOTS * pkWOTS * sigWOTS) list) (i j : int) :
     0 <= i < size qs 
  => qsadpre_idx qs i j = qsdgpre_idx qs i j.
proof.
move=> rng_i.
rewrite /qsadpre_idx /qsdgpre_idx /qs_idx /=; congr; rewrite ?sumzE.
+ rewrite 2!big_mapT -2!map_take 2!big_mapT /(\o) /= (big_nth witness) eq_sym (big_nth witness).
  rewrite /(\o) /predT -/predT ?size_take 2:(: i < size qs) 1..2:/# /=.
  apply eq_big_int => m [ge0_m lti_m] /=.
  rewrite 2!sumzE 4!big_mapT /(\o) &(eq_big_seq) => x /mem_iota [ge0_x /= ltlen_x].
  by rewrite ?nth_take // 1,2:/# nth_zip //=.
rewrite 2!big_mapT (nth_map witness) // (nth_map witness) /=; first by smt(size_zip).
rewrite -2!map_take 2!big_mapT /(\o) &(eq_big_seq) // => x qin /=.
by case (BaseW.val (encode_msgWOTS (nth witness qs i).`2).[x] <> 0) => _.
qed.

(* Range in which qsadtcr_idx lies *)
lemma qsadtcridx_rng (qs : (adrs * msgWOTS * pkWOTS * sigWOTS) list) (i j k : int) :
  let q = nth witness qs i in
     0 <= i < size qs
  => 0 <= j < len
  => 0 <= k < (if BaseW.val (encode_msgWOTS q.`2).[j] <> 0 
               then w - BaseW.val (encode_msgWOTS q.`2).[j]
               else w - 1 - BaseW.val (encode_msgWOTS q.`2).[j])
  => 0 <= qsadtcr_idx qs i j k < size (relcqsad_tcr qs).
proof.
move=> q rng_i rng_j rng_k.
split => [| _] @/qsadtcr_idx @/qs_idx /=. 
+ rewrite ?addr_ge0 3:/# sumz_ge0 allP => m /mapP [x' -> /=]; last by apply: size_ge0.
  by rewrite sumz_ge0 map_size_ge0.
rewrite /relcqsad_tcr /= size_flatten ?sumzE /=.
have {3}-> : qs = take i qs ++ drop i qs by rewrite cat_take_drop.
rewrite ?big_mapT /(\o) /= big_cat -addrA ler_lt_add. 
+ rewrite -map_take big_mapT /(\o) /= lez_eqVlt; left; congr. 
  by rewrite fun_ext /(==) => x; rewrite size_flatten.
rewrite (drop_nth witness) // big_consT (: k = k + 0) // addrA ltr_le_add; last first.
+ rewrite sumr_ge0 {1}/predT /= => admpksig.
  by rewrite size_flatten sumz_ge0 allP => m /mapP [x' -> /=]; apply: size_ge0.
rewrite (nth_map witness) //= -map_take big_mapT /(\o) /= -/q take_iota.
rewrite size_flatten sumzE 2!big_mapT /(\o) {2}(: len = j + (len - j)) 1:/# iota_add 1,2:/#.
rewrite big_cat /= ler_lt_add; first by rewrite lez_eqVlt; left; congr => /#.
rewrite (: len - j = 1 + (len - (j + 1))) 1:/# iota_add // 1:/# big_cat ltr_paddr.
+ rewrite sumr_ge0 {1}/predT /= => admpksig.
  by case (BaseW.val (encode_msgWOTS q.`2).[admpksig] <> 0); smt(size_map size_ge0).
rewrite iota1 big_cons big_nil {1}/predT /=. 
by case (BaseW.val (encode_msgWOTS q.`2).[j] <> 0); rewrite size_map size_iota /#.
qed.

(* Value of the element in relcqsad_tcr qs at index qsadtcr_idx qs i j k  *)
lemma nth_relcqsadtcr_qsadtcridx (qs : (adrs * msgWOTS * pkWOTS * sigWOTS) list) (i j k : int) :
  let q = nth witness qs i in
     0 <= i < size qs
  => 0 <= j < len
  => 0 <= k < (if BaseW.val (encode_msgWOTS q.`2).[j] <> 0 
              then w - BaseW.val (encode_msgWOTS q.`2).[j]
              else w - 1 - BaseW.val (encode_msgWOTS q.`2).[j])
  => nth witness (relcqsad_tcr qs) (qsadtcr_idx qs i j k) 
     = 
     if BaseW.val (encode_msgWOTS q.`2).[j] <> 0
     then set_hidx (set_chidx q.`1 j) (BaseW.val (encode_msgWOTS q.`2).[j] - 1 + k)
     else set_hidx (set_chidx q.`1 j) (BaseW.val (encode_msgWOTS q.`2).[j] + k).
proof.
move=> q rng_i rng_j rng_k.
pose f := (fun (admpksig : adrs * msgWOTS * pkWOTS * sigWOTS) =>
            (mkseq (fun (i : int) =>
                    if BaseW.val (encode_msgWOTS admpksig.`2).[i] <> 0
                    then mkseq 
                         (fun (j : int) => set_hidx (set_chidx admpksig.`1 i) (BaseW.val (encode_msgWOTS admpksig.`2).[i] - 1 + j))
                         (w - (BaseW.val (encode_msgWOTS admpksig.`2).[i]))
                    else mkseq 
                         (fun (j : int) => set_hidx (set_chidx admpksig.`1 i) (BaseW.val (encode_msgWOTS admpksig.`2).[i] + j))  
                         (w - 1 - (BaseW.val (encode_msgWOTS admpksig.`2).[i]))) len)).
have ->: 
  nth witness (relcqsad_tcr qs) (qsadtcr_idx qs i j k)
  =
  nth witness (flatten (map (fun (admpksig : adrs * msgWOTS * pkWOTS * sigWOTS) => 
                              flatten (f admpksig)) qs)) (qsadtcr_idx qs i j k).
+ by rewrite /relcqsdg_tcr /relcqsdgnf_tcr /f.
rewrite /qsadtcr_idx /= -/f nth_flatten_map_flatten //.
+ move: rng_j => [-> @/relcqsadnf_tcr]; rewrite ?(nth_map witness) // /f /=. 
  by rewrite size_map size_iota; smt(ge2_len).
+ rewrite ?(nth_map witness) // 1:size_iota /f /=; first by smt(ge2_len).
  by rewrite -/q nth_iota //=; smt(size_map size_iota BaseW.valP). 
rewrite /f (nth_map witness) //= (nth_map witness) //= -/q 2:nth_iota 1:size_iota //=; first by smt(ge2_len).
case (BaseW.val (encode_msgWOTS q.`2).[j] <> 0) => [eq0_em | neq0_em] /=. 
+ rewrite (nth_map witness) 1:size_iota /=; first by smt(BaseW.valP).
  by rewrite nth_iota; smt(BaseW.valP).
rewrite (nth_map witness) 1:size_iota /=; first by smt(BaseW.valP).
by rewrite nth_iota; smt(BaseW.valP).
qed.

(* Range in which qsdgtcr_idx qs xll ps i j k lies *)
lemma qsdgtcridx_rng (qs : (adrs * msgWOTS * pkWOTS * sigWOTS) list) (xll : dgstblock list list) (ps : pseed) (i j k : int) :
  let q = nth witness qs i in
     size qs = size xll
  => 0 <= i < size qs
  => 0 <= j < len
  => 0 <= k < (if BaseW.val (encode_msgWOTS q.`2).[j] <> 0 
               then w - BaseW.val (encode_msgWOTS q.`2).[j]
               else w - 1 - BaseW.val (encode_msgWOTS q.`2).[j])
  => 0 <= qsdgtcr_idx qs xll ps i j k < size (relcqsdg_tcr qs xll ps).
proof.
move=> q eq_sz rng_i rng_j rng_k; rewrite -eq_qsadtcridx_qsdgtcridx //.
have ->: size (relcqsdg_tcr qs xll ps) = size (relcqsad_tcr qs).
+ rewrite /relcqsdg_tcr /relcqsad_tcr 2!size_flatten 2!sumzE.
  rewrite 4!big_mapT (big_nth (witness, witness)) eq_sym (big_nth witness).
  rewrite /(\o) /predT -/predT /= (: size (zip qs xll) = size qs); first by smt(size_zip).
  apply eq_big_int => m rng_m /=; rewrite 2!size_flatten 2!sumzE.
  rewrite 4!big_mapT /(\o) &(eq_big_seq) /= -/q nth_zip //= => n rng_n.
  by case (BaseW.val (encode_msgWOTS (nth witness qs m).`2).[n] <> 0) => _; smt(size_map).
by apply qsadtcridx_rng.
qed.

(* Value of the element in relcqsdg_tcr qs xll ps at index qsdgtcr_idx qs xll ps i j k  *)
lemma nth_relcqsdgtcr_qsdgtcridx (qs : (adrs * msgWOTS * pkWOTS * sigWOTS) list) (xll : dgstblock list list) (ps : pseed) (i j k : int) :
  let q = nth witness qs i in
  let xl = nth witness xll i in
     size qs = size xll
  => 0 <= i < size qs
  => 0 <= j < len
  => 0 <= k < (if BaseW.val (encode_msgWOTS q.`2).[j] <> 0 
               then w - BaseW.val (encode_msgWOTS q.`2).[j]
               else w - 1 - BaseW.val (encode_msgWOTS q.`2).[j])
  => nth witness (relcqsdg_tcr qs xll ps) (qsdgtcr_idx qs xll ps i j k) 
     = 
     if BaseW.val (encode_msgWOTS q.`2).[j] <> 0
     then val (cf ps (set_chidx q.`1 j) (BaseW.val (encode_msgWOTS q.`2).[j] - 1) k (val (nth witness xl j)))
     else val (cf ps (set_chidx q.`1 j) (BaseW.val (encode_msgWOTS q.`2).[j]) k (val (nth witness (val q.`4) j))).
proof.
move=> q xl eq_sz rng_i rng_j rng_k.
pose f := (fun (admpksigxl : (adrs * msgWOTS * pkWOTS * sigWOTS) * dgstblock list) =>
            let (admpksig, xl) = (admpksigxl.`1, admpksigxl.`2) in
              (mkseq (fun (i : int) =>
                      if BaseW.val (encode_msgWOTS admpksig.`2).[i] <> 0
                      then mkseq
                           (fun (j : int) => val (cf ps (set_chidx admpksig.`1 i) (BaseW.val (encode_msgWOTS admpksig.`2).[i] - 1) j (val (nth witness xl i))))
                           (w - (BaseW.val (encode_msgWOTS admpksig.`2).[i]))
                      else mkseq 
                           (fun (j : int) => val (cf ps (set_chidx admpksig.`1 i) (BaseW.val (encode_msgWOTS admpksig.`2).[i]) j (val (nth witness (val admpksig.`4) i))))
                           (w - 1 - (BaseW.val (encode_msgWOTS admpksig.`2).[i]))) len)).
have ->: 
  nth witness (relcqsdg_tcr qs xll ps) (qsdgtcr_idx qs xll ps i j k)
  =
  nth witness (flatten (map (fun (admpksigxl : (adrs * msgWOTS * pkWOTS * sigWOTS) * dgstblock list) => 
                              flatten (f (admpksigxl.`1, admpksigxl.`2))) (zip qs xll))) (qsdgtcr_idx qs xll ps i j k).
+ by rewrite /relcqsdg_tcr /f.
have rngzip_i: 0 <= i < size (zip qs xll) by smt(size_zip).
rewrite /qsdgtcr_idx /= -/f nth_flatten_map_flatten //.
+ move: rng_j => [->]; rewrite ?(nth_map witness) // /f /=. 
  by rewrite size_map size_iota; smt(ge2_len).
+ rewrite (nth_map (witness, witness)) //= /f /= (nth_map witness) 1:size_iota /=; first by smt(ge2_len).
  by rewrite nth_zip //= -/q nth_iota //=; smt(size_map size_iota BaseW.valP).  
rewrite /f (nth_map (witness, witness)) //= (nth_map witness) //= -/q 2:nth_iota 1:size_iota //=; first by smt(ge2_len).
rewrite nth_zip //= -/q; case (BaseW.val (encode_msgWOTS q.`2).[j] <> 0) => [eq0_em | neq0_em] /=.
+ rewrite (nth_map witness) 1:size_iota /=; first by smt(BaseW.valP).
  by rewrite nth_iota; smt(BaseW.valP).
rewrite (nth_map witness) 1:size_iota /=; first by smt(BaseW.valP).
by rewrite nth_iota; smt(BaseW.valP).
qed.

(* Range in which qsadpre_idx qs xll ps i j k lies *)
lemma qsadpreidx_rng (qs : (adrs * msgWOTS * pkWOTS * sigWOTS) list) (i j : int) :
  let q = nth witness qs i in
     BaseW.val (encode_msgWOTS q.`2).[j] <> 0
  => 0 <= i < size qs 
  => 0 <= j < len
  => 0 <= qsadpre_idx qs i j < size (relcqsad_pre qs).
proof.
move=> q neq0_em rng_i rng_j.
split => [ | _] @/qsadpre_idx @/qs_idx /=.
+ rewrite addr_ge0 sumz_ge0 allP => m /mapP [x] [x' -> /=]; last by apply: size_ge0. 
  by rewrite sumz_ge0 map_size_ge0.
rewrite /relcqsad_pre size_flatten ?sumzE /=.
have {3}-> : qs = take i qs ++ drop i qs by rewrite cat_take_drop.
rewrite ?big_mapT /(\o) /= big_cat ler_lt_add. 
+ rewrite -map_take big_mapT /(\o) /= lez_eqVlt; left; congr. 
  by rewrite fun_ext /(==) => x; rewrite size_flatten.
rewrite (drop_nth witness) // big_consT /=.
rewrite (nth_map witness) //= -map_take big_mapT /(\o) /= -/q take_iota.
rewrite size_flatten sumzE 2!big_mapT /(\o) {2}(: len = j + (len - j)) 1:/# iota_add 1,2:/#.
rewrite big_cat /= ltr_paddr; first by rewrite sumr_ge0.
rewrite -(addz0 (big _ _ _)) ler_lt_add 1:(: min len j = j) 1:/# 1:lez_eqVlt //.
rewrite (: len - j = 1 + (len - (j + 1))) 1:/# iota_add // 1:/# big_cat ltr_paddr 1:sumr_ge0 //.
by rewrite iota1 big_cons big_nil /= neq0_em.
qed.

(* Value of the element in relcqsad_pre qs at index qsadpre_idx qs i j *)
lemma nth_relcqsadpre_qsadpreidx (qs : (adrs * msgWOTS * pkWOTS * sigWOTS) list) (i j : int) :
  let q = nth witness qs i in
     BaseW.val (encode_msgWOTS q.`2).[j] <> 0
  => 0 <= i < size qs 
  => 0 <= j < len 
  => nth witness (relcqsad_pre qs) (qsadpre_idx qs i j)   
     = 
     set_hidx (set_chidx q.`1 j) (BaseW.val (encode_msgWOTS q.`2).[j] - 1).
proof.
move=> q neq0_em rng_i rng_j.
pose f := (fun (admpksig : adrs * msgWOTS * pkWOTS * sigWOTS) =>
             (mkseq (fun (i : int) => if BaseW.val (encode_msgWOTS admpksig.`2).[i] <> 0
                                      then [set_hidx (set_chidx admpksig.`1 i) (BaseW.val (encode_msgWOTS admpksig.`2).[i] - 1)]
                                      else []) len)).
have ->: 
  nth witness (relcqsad_pre qs) (qsadpre_idx qs i j)
  =
  nth witness (flatten (map (fun (admpksig : adrs * msgWOTS * pkWOTS * sigWOTS) => 
                              flatten (f admpksig)) qs)) (qsadpre_idx qs i j).
+ by rewrite /relcqsad_pre /f.
rewrite /qsadpre_idx /= -/f nth_flatten_map_flatten //.
+ by rewrite (nth_map witness) /f //= size_map size_iota /#. 
+ by rewrite ?(nth_map witness) /f //= 1:size_iota 1:/# -/q nth_iota //= neq0_em.
rewrite /f (nth_map witness) //= (nth_map witness) //= 1:size_iota 1:/#.
by rewrite -/q nth_iota //= neq0_em /#.
qed.

(* Range in which qsdgpre_idx qs i j lies *)
lemma qsdgpreidx_rng (qs : (adrs * msgWOTS * pkWOTS * sigWOTS) list) (i j : int) :
  let q = nth witness qs i in
     BaseW.val (encode_msgWOTS q.`2).[j] <> 0
  => 0 <= i < size qs 
  => 0 <= j < len
  => 0 <= qsdgpre_idx qs i j < size (relcqsdg_pre qs).
proof.
move=> q neq0_em rng_i rng_j; rewrite -eq_qsadpreidx_qsdgpreidx //.
have ->: size (relcqsdg_pre qs) = size (relcqsad_pre qs).
+ rewrite /relcqsdg_pre /relcqsad_pre 2!size_flatten 2!sumzE.
  rewrite 4!big_mapT /(\o) /predT -/predT /=. 
  apply eq_bigr => q' @/predT /=; rewrite 2!size_flatten 2!sumzE.
  rewrite 4!big_mapT /(\o) &(eq_big_seq) //= => n rng_n.
  by case (BaseW.val (encode_msgWOTS q'.`2).[n] <> 0).
by apply qsadpreidx_rng.
qed.

(* Value of the element in relcqsdg_pre qs at index qsdgpre_idx qs i j *)
lemma nth_relcqsdgpre_qsdgpreidx (qs : (adrs * msgWOTS * pkWOTS * sigWOTS) list) (i j : int) :
  let q = nth witness qs i in
     BaseW.val (encode_msgWOTS q.`2).[j] <> 0
  => 0 <= i < size qs 
  => 0 <= j < len 
  => nth witness (relcqsdg_pre qs) (qsdgpre_idx qs i j)   
     = 
     nth witness (val q.`4) j.
proof.
move=> q neq0_em rng_i rng_j.
pose f := (fun (admpksig : adrs * msgWOTS * pkWOTS * sigWOTS) =>
             (mkseq (fun (i : int) => if BaseW.val (encode_msgWOTS admpksig.`2).[i] <> 0
                                      then [nth witness (val admpksig.`4) i]
                                      else []) len)).
have ->: 
  nth witness (relcqsdg_pre qs) (qsdgpre_idx qs i j)
  =
  nth witness (flatten (map (fun (admpksig : adrs * msgWOTS * pkWOTS * sigWOTS) => 
                              flatten (f admpksig)) qs)) (qsdgpre_idx qs i j).
+ by rewrite /relcqsdg_pre /f.
rewrite /qsdgpre_idx /= /f /qs_idx nth_flatten_map_flatten //.
+ by rewrite (nth_map witness) /f //= size_map size_iota /#. 
+ by rewrite (nth_map witness) //= /f (nth_map witness) 1:size_iota 1:/# -/q nth_iota //= neq0_em.
rewrite /f (nth_map witness) //= (nth_map witness) //= 1:size_iota 1:/#.
by rewrite -/q nth_iota //= neq0_em /#.
qed.


(* - Uniqueness and disjointness for query lists of tweakable hash function oracles  - *)
(* Uniqueness of relcqsad_udi qs j *)
lemma uniq_relcqsadudi (qs : (adrs * msgWOTS * pkWOTS * sigWOTS) list) (j : int) :
     valid_hidx j
  => all valid_wadrs (map (fun (admpksig : adrs * msgWOTS * pkWOTS * sigWOTS) => admpksig.`1) qs)
  => uniq_wgpidxs (map (fun (admpksig : adrs * msgWOTS * pkWOTS * sigWOTS) => admpksig.`1) qs) 
  => uniq (relcqsad_udi qs j).
proof.
move=> valj qsch uqpfqs @/relcqsad_udi.
pose f (q : adrs * msgWOTS * pkWOTS * sigWOTS) := get_wgpidxs q.`1.
rewrite uniq_flatten_map_in => [| q q' qin qpin |] /=; last first.
+ apply (uniq_map f); move: uqpfqs => @/uniq_wgpidxs.
  by rewrite -map_comp /(\o) /f.
+ rewrite allP => adl /mapP [q] [qin /= ->].
  rewrite uniq_flatten_map_in => [| k l /mem_iota /= rng_k /mem_iota /= rng_j |]; last by apply iota_uniq.
  - rewrite allP => adl' /mapP [k] [] /mem_iota /= rng_k ->.
    by case (j < BaseW.val (encode_msgWOTS q.`2).[k] - 1).
  apply contraLR => neql_k; rewrite hasPn => ad.
  case (j < BaseW.val (encode_msgWOTS q.`2).[l] - 1) => [lteml_j -> | /lezNgt geeml_j] //=.
  case (j < BaseW.val (encode_msgWOTS q.`2).[k] - 1) => //= ltemk_j.
  by rewrite neq_after_setchhidx //; smt(allP all_map).
apply contraLR => neqq_qp; rewrite hasPn => ad /flatten_mapP [k] [/mem_iota /= rng_k].
case (j < BaseW.val (encode_msgWOTS q'.`2).[k] - 1) => //= ltemk_j ->.
rewrite -flatten_mapP negb_exists => l /=; rewrite negb_and -implybE => /mem_iota /= rng_l.
case (j < BaseW.val (encode_msgWOTS q.`2).[l] - 1) => //= lteml_j.
rewrite neq_gp 1:2?eq_gp_setchhidx //; first 4 by smt(allP all_map).
apply (uniq_mapP f qs) => //; first by rewrite eq_sym.
by move: uqpfqs => @/uniq_wgpidxs; rewrite -map_comp /(\o).
qed.

(* Disjointness of relcqsad_udi qs j and arbitrary list *)
lemma disj_relcqsadudi (qs : (adrs * msgWOTS * pkWOTS * sigWOTS) list) (j : int) (adl : adrs list) :
     valid_hidx j
  => all valid_wadrs (map (fun (admpksig : adrs * msgWOTS * pkWOTS * sigWOTS) => admpksig.`1) qs)
  => disj_wgpidxs (map (fun (admpksig : adrs * msgWOTS * pkWOTS * sigWOTS) => admpksig.`1) qs) adl 
  => disj_lists (relcqsad_udi qs j) adl.
proof.
rewrite /disj_wgpidxs /disj_lists /= -map_comp /(\o) => valj qsch /hasPn djpf.
rewrite hasPn => ad adin.
have neqpref_qsadl: forall q, q \in qs => ad \in adl => ! eq_gp q.`1 ad.
+ move=> q qin adinp @/eq_gp.
  move: (djpf (get_wgpidxs q.`1) _).
  - by rewrite mapP; exists q.
  by apply contra => ->; rewrite mapP; exists ad.
have /#: exists q, q \in qs /\ eq_gp q.`1 ad.
move/flatten_mapP: adin => [q] [qin /= /flatten_mapP [k [/mem_iota /= rng_k]]].
case (j < BaseW.val (encode_msgWOTS q.`2).[k] - 1) => //= ltemk_j ->.
exists q; split => [// | @/eq_gp @/get_wgpidxs @/set_hidx @/set_chidx @/set_idx /=].
rewrite ?insubdK 4:?drop_putK // ?valid_wadrsidxs_adrsidxs ?validwadrsidxs_putchidx ?validwadrsidxs_putchhidx //; smt(allP all_map).
qed.

(* Disjointness of relcqsad_udi qs j and reltqsad_udi qs j *)
lemma disj_relcqsadudi_reltqsadudi (qs : (adrs * msgWOTS * pkWOTS * sigWOTS) list) (j : int) :
     valid_hidx j
  => all valid_wadrs (map (fun (admpksig : adrs * msgWOTS * pkWOTS * sigWOTS) => admpksig.`1) qs) 
  => uniq_wgpidxs (map (fun (q : adrs * msgWOTS * pkWOTS * sigWOTS) => q.`1) qs) 
  => disj_lists (relcqsad_udi qs j) (reltqsad_udi qs j).
proof.
move=> valj qsch uqpfqs @/disj_lists.
rewrite hasPn => ad @/relcqsad_udi @/reltqsad_udi.
move/flatten_mapP => -[q] [qin /= /flatten_mapP [k [] /mem_iota /=rng_k]].
case (j < BaseW.val (encode_msgWOTS q.`2).[k] - 1) => //= ltemk_j ->.
rewrite -flatten_mapP negb_exists => q' /=; rewrite negb_and -implybE => qpin.
rewrite -flatten_mapP negb_exists => l /=; rewrite negb_and -implybE => /mem_iota /= rng_l.
move/allP: qsch => qsch. 
move: (qsch q.`1 _); [by rewrite mapP; exists q | move=> q1ch].
move: (qsch q'.`1 _); [by rewrite mapP; exists q' | move=> qp1ch].
pose em_ele' := BaseW.val (encode_msgWOTS q'.`2).[l].
case (q = q') => [eqqp_q | neqqp_q]; last first.
+ move: uqpfqs; rewrite /uniq_wgpidxs -map_comp /(\o) /= => upqfqs.
  case (j < em_ele' - 1) => [ltem1_j| /lezNgt geem1_j].
  - rewrite mapP negb_exists => m /=; rewrite negb_and -implybE => /mem_iota /= rng_m.
    by rewrite neq_gp 1:2?eq_gp_setchhidx // => //; smt(uniq_mapP).
  case (em_ele' <> 0) => [neq0_em | eq0_em].
  - rewrite mapP negb_exists => m /=; rewrite negb_and -implybE => /mem_iota /= rng_m.
    by rewrite neq_gp 1:2?eq_gp_setchhidx // => //; smt(uniq_mapP BaseW.valP).
  rewrite mapP negb_exists => m /=; rewrite negb_and -implybE => /mem_iota /= rng_m.
  by rewrite neq_gp 1:2?eq_gp_setchhidx // => //; smt(uniq_mapP BaseW.valP).
move: ltemk_j; rewrite eqqp_q => ltemk_j.
case (k = l) => [eql_k | neql_k]; last first.
+ case (j < em_ele' - 1) => [ltem1_j| /lezNgt geem1_j].
  - rewrite mapP negb_exists => m /=; rewrite negb_and -implybE => /mem_iota /= rng_m.
    by apply neq_after_setchhidx => // /#.
  case (em_ele' <> 0) => [neq0_em | eq0_em].
  - rewrite mapP negb_exists => m /=; rewrite negb_and -implybE => /mem_iota /= rng_m.
    by apply neq_after_setchhidx => //; smt(BaseW.valP).
  rewrite mapP negb_exists => m /=; rewrite negb_and -implybE => /mem_iota /= rng_m.
  by apply neq_after_setchhidx => //; smt(BaseW.valP).
move: ltemk_j; rewrite eql_k => lteml_j.
case (j < em_ele' - 1) => [ltem1_j| /lezNgt geem1_j].
+ rewrite mapP negb_exists => m /=; rewrite negb_and -implybE => /mem_iota /= rng_m.
  by apply neq_after_sethidx => //; smt(validwadrs_setchidx).
case (em_ele' <> 0) => [neq0_em | eq0_em].
+ rewrite mapP negb_exists => m /=; rewrite negb_and -implybE => /mem_iota /= rng_m.
  by apply neq_after_sethidx => //; smt(validwadrs_setchidx BaseW.valP).
rewrite mapP negb_exists => m /=; rewrite negb_and -implybE => /mem_iota /= rng_m.
by apply neq_after_sethidx => //; smt(validwadrs_setchidx BaseW.valP).
qed.

(* Uniqueness of relcqsad_tcr qs *)
lemma uniq_relcqsadtcr (qs : (adrs * msgWOTS * pkWOTS * sigWOTS) list) :
     all valid_wadrs (map (fun (admpksig : adrs * msgWOTS * pkWOTS * sigWOTS) => admpksig.`1) qs)
  => uniq_wgpidxs (map (fun (admpksig : adrs * msgWOTS * pkWOTS * sigWOTS) => admpksig.`1) qs) 
  => uniq (relcqsad_tcr qs).
proof.
move=> qsch uqpfqs @/relcqsad_tcr.
pose f (q : adrs * msgWOTS * pkWOTS * sigWOTS) := get_wgpidxs q.`1.
rewrite uniq_flatten_map_in => [| q q' qin qpin |] /=; last first.
+ apply (uniq_map f); move: uqpfqs => @/uniq_wgpidxs.
  by rewrite -map_comp /(\o) /f.
+ rewrite allP => adl /mapP [q] [qin /= ->].
  rewrite uniq_flatten_map_in => [| i j /mem_iota /= + /mem_iota /= |]; last by apply: iota_uniq.
  - rewrite all_map /preim allP => i /mem_iota [ge0_i /= ltlen_i].
    case (BaseW.val (encode_msgWOTS q.`2).[i] <> 0) => ?.
    * rewrite map_inj_in_uniq 2:iota_uniq => j k /mem_iota /= rng_j /mem_iota /= rng_k.
      by apply: contraLR => neqk_j; apply: neq_after_sethidx; smt(validwadrs_setchidx allP all_map BaseW.valP).
    rewrite map_inj_in_uniq 2:iota_uniq => j k /mem_iota /= rng_j /mem_iota /= rng_k. 
    by apply: contraLR => neqk_j; apply: neq_after_sethidx => //=; smt(validwadrs_setchidx allP all_map BaseW.valP).
  move=> rng_i rng_j; apply: contraLR => neqj_i; rewrite hasPn => ad.
  case (BaseW.val (encode_msgWOTS q.`2).[j] <> 0) => ?; rewrite mapP => -[j'] [] /mem_iota /= ? ->.
  - case (BaseW.val (encode_msgWOTS q.`2).[i] <> 0) => ?; rewrite mapP negb_exists => i' /=.
    * rewrite negb_and -implybE mem_iota => ?.
      by rewrite neq_after_setchhidx //=; smt(allP all_map BaseW.valP).
    rewrite negb_and -implybE mem_iota => ?.
    by rewrite neq_after_setchhidx //=; smt(allP all_map BaseW.valP).
  case (BaseW.val (encode_msgWOTS q.`2).[i] <> 0) => ?; rewrite mapP negb_exists => i' /=. 
  - rewrite negb_and -implybE mem_iota => ?.
    by rewrite neq_after_setchhidx //=; smt(allP all_map BaseW.valP).
  rewrite negb_and -implybE mem_iota => ?.
  by rewrite neq_after_setchhidx //=; smt(allP all_map BaseW.valP).
apply contraLR => neqqp_q; rewrite hasPn => ad.
rewrite -2!flatten_mapP negb_exists => -[i'] [] /mem_iota /= rng_ip adin i.
rewrite negb_and -implybE => /mem_iota /= rng_i.
move: adin; have neqqpf_qppf: ! eq_gp q.`1 q'.`1.
+ rewrite /eq_gp; apply (uniq_mapP f qs) => //.
  by move: uqpfqs => @/uniq_wgpidxs; rewrite -map_comp /(\o).
case (BaseW.val (encode_msgWOTS q'.`2).[i'] <> 0) => ?; rewrite mapP => -[j'] [] /mem_iota rng_jp -> /=.
+ case (BaseW.val (encode_msgWOTS q.`2).[i] <> 0) => ?; rewrite mapP negb_exists /= => j.
  - rewrite negb_and -implybE => /mem_iota /= rng_j.
    by rewrite neq_gp 1:2?eq_gp_setchhidx // //=; smt(allP all_map BaseW.valP).
  rewrite negb_and -implybE => /mem_iota /= rng_j.
  by rewrite neq_gp 1:2?eq_gp_setchhidx // //=; smt(allP all_map BaseW.valP).
case (BaseW.val (encode_msgWOTS q.`2).[i] <> 0) => ?; rewrite mapP negb_exists /= => j.
+ rewrite negb_and -implybE => /mem_iota /= rng_j.
  by rewrite neq_gp 1:2?eq_gp_setchhidx // //=; smt(allP all_map BaseW.valP).
rewrite negb_and -implybE => /mem_iota /= rng_j.
by rewrite neq_gp 1:2?eq_gp_setchhidx // //=; smt(allP all_map BaseW.valP).
qed.

(* Disjointness of relcqsad_tcr qs and arbitrary list *)  
lemma disj_relcqsadtcr (qs : (adrs * msgWOTS * pkWOTS * sigWOTS) list) (adl : adrs list) :
     all valid_wadrs (map (fun (admpksig : adrs * msgWOTS * pkWOTS * sigWOTS) => admpksig.`1) qs)
  => disj_wgpidxs (map (fun (admpksig : adrs * msgWOTS * pkWOTS * sigWOTS) => admpksig.`1) qs) adl 
  => disj_lists (relcqsad_tcr qs) adl.
proof.
rewrite /disj_wgpidxs /disj_lists /= -map_comp /(\o) => qsch /hasPn djpf.
rewrite hasPn => ad adin.
have neqpref_qsadl: forall q, q \in qs => ad \in adl => ! eq_gp q.`1 ad.
+ move=> q qin adinp @/eq_gp.
  move: (djpf (get_wgpidxs q.`1) _).
  - by rewrite mapP; exists q.
  by apply contra => ->; rewrite mapP; exists ad.
have /#: exists q, q \in qs /\ eq_gp q.`1 ad.
+ move/flatten_mapP: adin => [q] [qin /= /flatten_mapP [i [/mem_iota /= rng_i]]].
  case (BaseW.val (encode_msgWOTS q.`2).[i] <> 0) => valem; rewrite mapP => -[j [/mem_iota /= rng_j ->]].
  - exists q; split => [// | @/eq_gp @/get_wgpidxs @/set_hidx @/set_chidx @/set_idx /=].  
    by rewrite ?insubdK 4:?drop_putK // ?valid_wadrsidxs_adrsidxs ?validwadrsidxs_putchidx ?validwadrsidxs_putchhidx //; smt(allP all_map BaseW.valP).
  exists q; split => [// | @/eq_gp @/get_wgpidxs @/set_hidx @/set_chidx @/set_idx /=].
  rewrite ?insubdK 4:?drop_putK // ?valid_wadrsidxs_adrsidxs ?validwadrsidxs_putchidx ?validwadrsidxs_putchhidx //; smt(allP all_map BaseW.valP).
qed.

(* Uniqueness of relcqsad_pre qs *)
lemma uniq_relcqsadpre (qs : (adrs * msgWOTS * pkWOTS * sigWOTS) list) :
  all valid_wadrs (map (fun (admpksig : adrs * msgWOTS * pkWOTS * sigWOTS) => admpksig.`1) qs) => 
  uniq_wgpidxs (map (fun (admpksig : adrs * msgWOTS * pkWOTS * sigWOTS) => admpksig.`1) qs) => 
  uniq (relcqsad_pre qs).
proof.
move=> qsch @/uniq_wgpidxs @/relcqsad_pre.
rewrite -map_comp /(\o) => uqpfqs.
pose f (x : adrs * msgWOTS * pkWOTS * sigWOTS) := get_wgpidxs x.`1.
rewrite uniq_flatten_map_in; last by apply (uniq_map f).
+ rewrite allP => adl; rewrite mapP => -[q] [qin /= ->].
  rewrite uniq_flatten_map_in => [| i j /mem_iota /= + /mem_iota /= |]; last by apply: iota_uniq.
  - rewrite allP => adl' /mapP [i] [] /mem_iota /= rng_i ->.
    by case (BaseW.val (encode_msgWOTS q.`2).[i] <> 0). 
  move=> rng_i rng_j; apply contraLR => neqj_i; rewrite hasPn => ad. 
  case (BaseW.val (encode_msgWOTS q.`2).[j] <> 0); case (BaseW.val (encode_msgWOTS q.`2).[i] <> 0) => //= ? ? ->.
  by rewrite neq_after_setchhidx //; smt(allP all_map BaseW.valP).
move=> q q' qin qpin.
apply contraLR => neqq_qp; rewrite hasPn /= => ad.
move/flatten_mapP => [i] [] /mem_iota /= rng_i.
case (BaseW.val (encode_msgWOTS q'.`2).[i] <> 0) => ? //= ->.
rewrite -flatten_mapP negb_exists => j /=; rewrite negb_and.
case (! (j \in iota_ 0 len) ) => //= /mem_iota /= rng_j.
case (BaseW.val (encode_msgWOTS q.`2).[j] <> 0) => ? //=.
by rewrite neq_gp 1:2?eq_gp_setchhidx //; smt(allP all_map BaseW.valP uniq_mapP).
qed.

(* Disjointness of relcqsad_pre qs and reltqsad_pre qs *)
lemma disj_relcqsadpre_reltqsadpre (qs : (adrs * msgWOTS * pkWOTS * sigWOTS) list) :
     all valid_wadrs (map (fun (admpksig : adrs * msgWOTS * pkWOTS * sigWOTS) => admpksig.`1) qs) 
  => uniq_wgpidxs (map (fun (q : adrs * msgWOTS * pkWOTS * sigWOTS) => q.`1) qs) 
  => disj_lists (relcqsad_pre qs) (reltqsad_pre qs).
proof.
move=> qsch uqpfqs @/disj_lists.
rewrite hasPn => ad @/relcqsad_pre @/reltqsad_pre.
move/flatten_mapP => -[q] [qin /= /flatten_mapP [i [] /mem_iota [ge0_i /= ltlen_i]]].
case (BaseW.val (encode_msgWOTS q.`2).[i] <> 0) => //= neq0_em adval.
rewrite -flatten_mapP negb_exists => q' /=; rewrite negb_and -implybE => qpin.
rewrite -flatten_mapP negb_exists => j /=; rewrite negb_and -implybE => /mem_iota /= rng_j.
rewrite mapP negb_exists => k /=; rewrite negb_and -implybE => /mem_iota [ge0_k /= ltw1em_k].
rewrite adval /=; move/allP: qsch => qsch. 
move: (qsch q.`1 _); [by rewrite mapP; exists q | move=> q1ch].
move: (qsch q'.`1 _); [by rewrite mapP; exists q' | move=> qp1ch].
case (q = q') => [eqq_qp /= | neqq_qp].
+ by rewrite neq_after_setchhidx //; smt(BaseW.valP).
rewrite neq_gp 1:2?eq_gp_setchhidx //; 1,2,3: smt(BaseW.valP). 
by move: uqpfqs; rewrite /uniq_wgpidxs -map_comp /(\o) /=; smt(uniq_mapP).
qed.



(* --- Types (3/3) -- *)
(* -- General -- *)
(*
  WOTS-TW addresses
  Introduced only for the purpose of the proof; specifically, to ensure that 
  the adversary provides us valid WOTS-TW addresses in the security notion. 
  Essentially, this excludes the "irrelevant"
  adversaries that provide invalid addresses from the considered class of
  adversaries. Equivalently, we could extend the behavioral check on the adversary
  at the end of the game (i.e., only let the adversary succeed if the
  provided addresses are valid WOTS-TW addresses). Furthermore, this approach
  would also be equivalent to having no subtype or extended behavioral check
  but instead have the considered scheme/oracle do input sanitization (i.e., have the scheme
  check whether the provided addresses are valid WOTS-TW addresses).   
*)
clone import Subtype as WAddress with
  type T <- adrs,
    op P <- valid_wadrs.
    
type wadrs = WAddress.sT.


(* -- WOTS/WOTS-TW specific -- *)
(* - WOTS-TW in encompassing structure with tweaks/addresses and with secret key generation - *)
(* Public keys *)
type pkWOTSTW = pkWOTS * pseed * adrs.

(* Secret keys *)
type skWOTSTW = sseed * pseed * adrs.



(* --- WOTS-TW scheme in encompassing structure --- *)
(* -- Specification of WOTS-TW in encompassing structure -- *)
module WOTS_TW_ES = {
  (* Generate secret key *)
  proc gen_skWOTS(ss : sseed, ps : pseed, ad : adrs) : skWOTS = {
    var skWOTS : dgstblock list;
    var skWOTS_ele : dgstblock;
    
    skWOTS <- [];
    while (size skWOTS < len) {
      skWOTS_ele <- prf_sk ss (ps, (set_hidx (set_chidx ad (size skWOTS))) 0);
      skWOTS <- rcons skWOTS skWOTS_ele;
    }
    
    return insubd skWOTS;
  }

  (* Compute public key from secret key *)  
  proc pkWOTS_from_skWOTS(skWOTS : skWOTS, ps : pseed, ad : adrs) : pkWOTS = {
    var pkWOTS : dgstblock list;
    var pkWOTS_ele : dgstblock;
    var skWOTS_ele : dgstblock;
    
    pkWOTS <- [];
    while (size pkWOTS < len) {
      (* Get element from sk *)
      skWOTS_ele <- nth witness (val skWOTS) (size pkWOTS);

      (* 
        Compute pk element corresponding to above-retrieved sk element 
        by applying full chain computation. Afterward, add pk element to pk.
      *)
      pkWOTS_ele <- cf ps (set_chidx ad (size pkWOTS)) 0 (w - 1) (val skWOTS_ele);
      pkWOTS <- rcons pkWOTS pkWOTS_ele; 
    }
    
    return insubd pkWOTS;
  }
  
  (* Generate key pair *)
  proc keygen(ss : sseed, ps : pseed, ad : adrs) : pkWOTSTW * skWOTSTW = {
    var pkWOTS : pkWOTS;
    var skWOTS : skWOTS;
    
    (* Generate secret key *)
    skWOTS <@ gen_skWOTS(ss, ps, ad);
    
    (* Compute public key corresponding to generated secret key *) 
    pkWOTS <@ pkWOTS_from_skWOTS(skWOTS, ps, ad);
    
    return ((pkWOTS, ps, ad), (ss, ps, ad));
  }
  
  (* Sign message with a secret key *)
  proc sign(sk : skWOTSTW, m : msgWOTS) : sigWOTS = {
    var ss : sseed;
    var ps : pseed;
    var ad : adrs;
    var skWOTS : skWOTS;
    var em : emsgWOTS;
    var sig : dgstblock list;
    var em_ele : int;
    var sk_ele : dgstblock;
    var sig_ele : dgstblock;
    
    (* Extract secret seed, public seed, and address *)
    ss <- sk.`1;
    ps <- sk.`2;
    ad <- sk.`3;
    
    (* Encode given message *)
    em <- encode_msgWOTS m;
    
    (* Compute secret key *)
    skWOTS <@ gen_skWOTS(ss, ps, ad);
    
    sig <- [];
    while (size sig < len) {
      (* Get element from secret key and (integer value of) element from encoded message *)
      sk_ele <- nth witness (val skWOTS) (size sig);
      em_ele <- BaseW.val em.[size sig];
      
      (* 
        Compute signature element from the considered secret key element
        and add it to the signature
      *)
      sig_ele <- cf ps (set_chidx ad (size sig)) 0 em_ele (val sk_ele);
      sig <- rcons sig sig_ele;
    }
    
    return insubd sig;
  }
  
  (* Compute a public key from a signature (and corresponding signed message) *)
  proc pkWOTS_from_sigWOTS(m : msgWOTS, sig : sigWOTS, ps : pseed, ad : adrs) : pkWOTS = {
    var pkWOTS : dgstblock list;
    var em_ele : int;
    var pkWOTS_ele : dgstblock;
    var sig_ele : dgstblock;
    var em : emsgWOTS;
    
    (* Encode given message *)
    em <- encode_msgWOTS m;
    
    pkWOTS <- [];
    while (size pkWOTS < len) {
      (* Get element from signature and (integer value of) element from encoded message *)
      sig_ele <- nth witness (val sig) (size pkWOTS);
      em_ele <- BaseW.val em.[size pkWOTS];
      
      (* 
        Compute public key element from the considered signature element
        and add it to the public key
      *)
      pkWOTS_ele <- cf ps (set_chidx ad (size pkWOTS)) em_ele (w - 1 - em_ele) (val sig_ele);
      pkWOTS <- rcons pkWOTS pkWOTS_ele;
    }
     
    return insubd pkWOTS;
  }
  
  (* Verify signature for a message using public key *)
  proc verify(pk : pkWOTSTW, m : msgWOTS, sig : sigWOTS) : bool = {
    var ps : pseed;
    var ad : adrs;
    var pkWOTS, pkWOTS' : pkWOTS;
    
    (* Extract public key, public seed, and address *)
    pkWOTS <- pk.`1;
    ps <- pk.`2;
    ad <- pk.`3;
    
    (* Compute public key from signature *)
    pkWOTS' <@ pkWOTS_from_sigWOTS(m, sig, ps, ad);
    
    return pkWOTS' = pkWOTS;
  }
}.


(* -- Adversary classes and oracle interfaces -- *)
(* Type of oracle given to adversaries in M-EUF-GCMA game for WOTS-TW in encompassing structure *)
module type Oracle_MEUFGCMA_WOTSTWES  = {
  proc init(ss_init : sseed, ps_init : pseed) : unit
  proc query(wad : wadrs, m : msgWOTS) : pkWOTS * sigWOTS
  proc get(i : int) : adrs * msgWOTS * pkWOTS * sigWOTS
  proc get_addresses() : adrs list
  proc nr_queries() : int
  proc dist_addresses() : bool
}.

(* Class of adversaries against M-EUF-GCMA game for WOTS-TW in encompassing structure *)
module type Adv_MEUFGCMA_WOTSTWES(O : Oracle_MEUFGCMA_WOTSTWES, OC : Oracle_THFC) = {
  proc choose() : unit { O.query, OC.query }
  proc forge(ps : pseed) : int * msgWOTS * sigWOTS {}
}.


(* -- Notions -- *)
(* M-EUF-GCMA game for WOTS-TW in encompassing structure *) 
module M_EUF_GCMA_WOTSTWES(A : Adv_MEUFGCMA_WOTSTWES, O : Oracle_MEUFGCMA_WOTSTWES, OC : Oracle_THFC) = {
  module A = A(O, OC)
  
  proc main() : bool = {
    var ss : sseed;
    var ps : pseed; 
    var ad : adrs;
    var pkWOTS : pkWOTS;
    var i : int;
    var m, m' : msgWOTS;
    var sig, sig': sigWOTS;
    var adlO, adlOC : adrs list;
    var nrqs : int;
    var is_valid, is_fresh, dist_wgpidxs : bool;

    (* Sample secret seed and public seed *)
    ss <$ dsseed;
    ps <$ dpseed;
    
    (* Initialize oracles *)
    O.init(ss, ps);
    OC.init(ps);
    
    (* 
      Ask adversary to choose messages and tweaks for which to receive a public key and 
      corresponding signature
    *)
    A.choose();

    (*
      Ask the adversary to forge a signature for any message (and provide both
      the message and the signature) for any of the (address, message, public key) pairs
      determined previously (in A.choose())
    *)
    (i, m', sig') <@ A.forge(ps);
    
    (* Get the (address, message, public key, signature) pair at index i in the query list *)
    (ad, m, pkWOTS, sig) <@ O.get(i);
    
    (* 
      Verify (w.r.t. message m', pkWOTS, ps, and ad) the signature sig' provided by the adversary 
    *)
    is_valid <@ WOTS_TW_ES.verify((pkWOTS, ps, ad), m', sig');

    (* 
      Check whether message for which the adversary forged a signature is fresh 
      (i.e., check whether message is not equal to the message for which the adversary
      received a signature under the same public key/address)
    *)
    is_fresh <- m' <> m;
    
    (* Get the number of queries the adversary issued to the signing oracle *)
    nrqs <@ O.nr_queries();
    
    (* 
      Check whether the four-element prefixes of the indices corresponding to the addresses
      queried by the adversary (to the signing oracle) are distinct 
    *)
    dist_wgpidxs <@ O.dist_addresses();
    
    (* Get the list of addresses from the signing oracle and family oracle, respectively *)
    adlO <@ O.get_addresses();
    adlOC <@ OC.get_tweaks();
    
    (* 
      Success iff
      (1) "0 <= nrqs <= d": the number of signing/target queries made by the adversary is 
                            between 0 and d (the number of WOTS-TW instances to consider), and
      (2) "0 <= i < nrqs": the query index provided by the adversary is valid, and
      (3) "is_valid": the forged signature provided by the adversary is valid, and 
      (4) "is_fresh": the message for which the adversary forged a signature is fresh, and
      (5) "dist_wgpidxs": the four-element prefixes of the indices corresponding to the addresses queried by the adversary
                           to the signing oracle are distinct, and
      (6) "disj_wgpidxs adlO adlOC": the adversary did not query the oracles O and OC with 
                                      addresses of which the corresponding indices share four-element prefixes.
    *)
    return 0 <= nrqs <= d /\ 0 <= i < nrqs /\ 
           is_valid /\ is_fresh /\ dist_wgpidxs /\ disj_wgpidxs adlO adlOC;     
  }
}.


(* -- Oracle implementations -- *)
(* Implementation of signing oracle given to adversary in M-EUF-GCMA game for WOTS-TW in encompassing structure *)
module O_MEUFGCMA_WOTSTWES : Oracle_MEUFGCMA_WOTSTWES = {
  var ss : sseed
  var ps : pseed
  var qs : (adrs * msgWOTS * pkWOTS * sigWOTS) list
  
  proc init(ss_init : sseed, ps_init : pseed) : unit = {
    ss <- ss_init;
    ps <- ps_init;
    qs <- [];
  }
  
  proc query(wad : wadrs, m : msgWOTS) : pkWOTS * sigWOTS = {
    var pk : pkWOTSTW;
    var sk : skWOTSTW;
    var sig : sigWOTS;
    var pksig : pkWOTS * sigWOTS;
    var admpksig : adrs * msgWOTS * pkWOTS * sigWOTS;
    
    (pk, sk) <@ WOTS_TW_ES.keygen(ss, ps, val wad); 

    sig <@ WOTS_TW_ES.sign(sk, m);
        
    admpksig <- (val wad, m, pk.`1, sig);
    qs <- rcons qs admpksig;
      
    pksig <- (pk.`1, sig);
    
    return pksig;
  } 

  proc get(i : int) : adrs * msgWOTS * pkWOTS * sigWOTS = {
    return nth witness qs i;
  }
  
  proc get_addresses() : adrs list = {
    return map (fun (admpksig : adrs * msgWOTS * pkWOTS * sigWOTS) => admpksig.`1) qs;
  }
  
  proc nr_queries() : int = {
    return size qs;
  }
  
  proc dist_addresses() : bool = {
    return uniq_wgpidxs (map (fun (admpksig : adrs * msgWOTS * pkWOTS * sigWOTS) => admpksig.`1) qs);
  }
}.

(* Implementation of oracle given to adversary in the second game of the game sequence. *)
module O_MEUFGCMA_WOTSTWES_NOPRF : Oracle_MEUFGCMA_WOTSTWES = {
  include var O_MEUFGCMA_WOTSTWES [-query]
  
  proc query(wad : wadrs, m : msgWOTS) : pkWOTS * sigWOTS = {
    var ad : adrs;
    var pk : dgstblock list;
    var sk : dgstblock list;
    var sig : dgstblock list;
    var em : emsgWOTS;
    var pk_ele, sk_ele, sig_ele : dgstblock;
    var em_ele : int;
    var pksig : pkWOTS * sigWOTS;
    var admpksig : adrs * msgWOTS * pkWOTS * sigWOTS;
    
    ad <- val wad;
    
    sk <$ ddgstblockl;

    pk <- [];
    while (size pk < len){
      sk_ele <- nth witness sk (size pk);
      pk_ele <- cf ps (set_chidx ad (size pk)) 0 (w - 1) (val sk_ele);
      pk <- rcons pk pk_ele;
    }

    em <- encode_msgWOTS m;
    sig <- [];
    while (size sig < len){
      sk_ele <- nth witness sk (size sig);
      em_ele <- BaseW.val em.[size sig];
      sig_ele <- cf ps (set_chidx ad (size sig)) 0 em_ele (val sk_ele);
      sig <- rcons sig sig_ele;
    }

    admpksig <- (ad, m, insubd pk, insubd sig);
    qs <- rcons qs admpksig;

    pksig <- (insubd pk, insubd sig);
        
    return pksig;
  }
}.


(* -- Reduction Adversaries -- *)
(* 
  Reduction adversary that reduces from PRF for prf_sk to distinguishing between
  Game0_WOTSTWES and MEUFGCMA_WOTSTWES without PRF
*)
module (R_PRF_Game0NOPRFWOTSTWES (A : Adv_MEUFGCMA_WOTSTWES) : Adv_PRF) (O : Oracle_PRF) = {
  module O_R_PRF_Game0NOPRFWOTSTWES : Oracle_MEUFGCMA_WOTSTWES = {
    include var O_MEUFGCMA_WOTSTWES [-query]
    
    proc query(wad : wadrs, m : msgWOTS) : pkWOTS * sigWOTS = {
      var ad : adrs;
      var pk : dgstblock list;
      var sk : dgstblock list;
      var sig : dgstblock list;
      var em : emsgWOTS;
      var pk_ele, sk_ele, sig_ele : dgstblock;
      var em_ele : int;
      var pksig : pkWOTS * sigWOTS;
      var admpksig : adrs * msgWOTS * pkWOTS * sigWOTS;

      ad <- val wad;
      
      sk <- [];

      while (size sk < len) {
        sk_ele <@ O.query((ps, set_hidx (set_chidx ad (size sk)) 0));
        sk <- rcons sk sk_ele;
      }

      pk <- [];
      while (size pk < len) {
        sk_ele <- nth witness sk (size pk);
        pk_ele <- cf ps (set_chidx ad (size pk)) 0 (w - 1) (val sk_ele);
        pk <- rcons pk pk_ele;
      }

      em <- encode_msgWOTS m;

      sig <- [];
      while (size sig < len) {
        sk_ele <- nth witness sk (size sig);
        em_ele <- BaseW.val em.[size sig];
        sig_ele <- cf ps (set_chidx ad (size sig)) 0 em_ele (val sk_ele);
        sig <- rcons sig sig_ele;
      }

      admpksig <- (ad, m, insubd pk, insubd sig);
      qs <- rcons qs admpksig;
      pksig <- (insubd pk, insubd sig);

      return pksig;
    }
  }
  
  module A = A(O_R_PRF_Game0NOPRFWOTSTWES, O_THFC_Default)
  
  proc distinguish() : bool = {
    var ps : pseed;
    var i : int;
    var ad : adrs;
    var m, m' : msgWOTS;
    var pk : pkWOTS;
    var sig, sig' : sigWOTS;
    var is_valid, is_fresh, dist_wgpidxs : bool;
    var adlO, adlOC : adrs list;
    var nrqs : int;
    
    ps <$ dpseed;
    
    O_R_PRF_Game0NOPRFWOTSTWES.init(witness, ps);
    O_THFC_Default.init(ps);
    
    A.choose();
    
    (i, m', sig') <@ A.forge(ps);
    
    (ad, m, pk, sig) <@ O_R_PRF_Game0NOPRFWOTSTWES.get(i);
    
    is_valid <@ WOTS_TW_ES.verify((pk, ps, ad), m', sig');

    is_fresh <- m' <> m;
    
    nrqs <@ O_R_PRF_Game0NOPRFWOTSTWES.nr_queries();
    
    dist_wgpidxs <@ O_R_PRF_Game0NOPRFWOTSTWES.dist_addresses();
       
    adlO <@ O_R_PRF_Game0NOPRFWOTSTWES.get_addresses();
        
    adlOC <@ O_THFC_Default.get_tweaks();  
        
    return 0 <= nrqs <= d /\ 0 <= i < nrqs /\ 
           is_valid /\ is_fresh /\ dist_wgpidxs /\ disj_wgpidxs adlO adlOC;
  }
}.

(* 
  Reduction adversary that reduces from SM_DT_UD_C to distinguishing between 
  Game2_WOTSTWES and Game3_WOTSTWES (by, as an intermediate step, reducing to 
  distinguishing between the relevant distributions)
*)
module (R_SMDTUDC_Game23WOTSTWES (A : Adv_MEUFGCMA_WOTSTWES) : Adv_SMDTUDC) (O : Oracle_SMDTUD) (OC : Oracle_THFC) = {
  module O_DistRCH = {
    var b : bool
    var ps : pseed
    var i : int
  
    proc init(b_init : bool, ps_init : pseed) : unit = {
      b <- b_init;
      ps <- ps_init;
    }
  
    proc query(wad : wadrs, m : msgWOTS) : dgstblock list = {
      var ad : adrs;
      var em : emsgWOTS;
      var chal, chal' : dgstblock list;
      var em_ele : int;
      var chal_ele, chal_ele' : dgstblock;
      var j : int;
  
      ad <- val wad;
  
      em <- encode_msgWOTS m;
  
      chal' <- [];
      while (size chal' < len) {
        em_ele <- BaseW.val em.[size chal'];
  
        if (i < em_ele - 1) {
          chal_ele' <@ O.query(set_hidx (set_chidx ad (size chal')) i);
        } else {
          chal_ele' <$ ddgstblock;
        } 
  
        chal' <- rcons chal' chal_ele';
      }
  
      chal <- [];
      while (size chal < len) {
        em_ele <- BaseW.val em.[size chal];
  
        if (i < em_ele - 1) {
          chal_ele <- nth witness chal' (size chal);
  
          j <- 1;
          while (j < em_ele - 1 - i) {
            chal_ele <@ OC.query(set_hidx (set_chidx ad (size chal)) (i + j), val chal_ele);
            j <- j + 1;
          }
        } else {
          chal_ele <- nth witness chal' (size chal);
        }
  
        chal <- rcons chal chal_ele;
      }
  
      return chal;
    }
  }

  module O_R_DistRCH_Game23WOTSTW : Oracle_MEUFGCMA_WOTSTWES = {
    include var O_MEUFGCMA_WOTSTWES [-query]

    proc query(wad : wadrs, m : msgWOTS) : pkWOTS * sigWOTS = {
      var ad : adrs;
      var chal : dgstblock list;
      var em : emsgWOTS;
      var pk : dgstblock list;
      var sig : dgstblock list;
      var em_ele : int;
      var pk_ele, sig_ele, chal_ele : dgstblock;
      var pksig : pkWOTS * sigWOTS;
      var admpksig : adrs * msgWOTS * pkWOTS * sigWOTS;
      var j : int;
      
      ad <- val wad;
      
      chal <@ O_DistRCH.query(wad, m);

      em <- encode_msgWOTS m;
      pk <- [];
      sig <- [];
      while (size pk < len) {
        chal_ele <- nth witness chal (size pk);
        em_ele <- BaseW.val em.[size pk];
        if (em_ele = 0) {
          sig_ele <- chal_ele;
        } else {
          sig_ele <@ OC.query(set_hidx (set_chidx ad (size pk)) (em_ele - 1), val chal_ele);
        }

        (* pk_ele <- cf ps (set_chidx ad (size pk)) em_ele (w - 1 - em_ele) sig_ele *)
        pk_ele <- sig_ele;
        j <- 0;
        while (j < w - 1 - em_ele) {
          pk_ele <@ OC.query(set_hidx (set_chidx ad (size pk)) (em_ele + j), val pk_ele);
          j <- j + 1;
        }

        pk <- rcons pk pk_ele;
        sig <- rcons sig sig_ele;
      }

      admpksig <- (ad, m, insubd pk, insubd sig);
      qs <- rcons qs admpksig;

      pksig <- (insubd pk, insubd sig);
      
      return pksig;
    }
  }

  module O_R_DistRCH_Game23WOTSTW_THFC : Oracle_THFC = {
    var ps : pseed
    var adl : adrs list
    
    proc init(ps_init : pseed) : unit = {
      ps <- ps_init;
      adl <- [];
    }

    proc query(ad : adrs, x : dgst) : dgstblock = {
      var df : int;
      var y : dgstblock;

      y <@ OC.query(ad, x);
      adl <- rcons adl ad;

      return y;
    }

    proc get_tweaks() : adrs list = {
      return adl;
    }
  }

  module A = A(O_R_DistRCH_Game23WOTSTW, O_R_DistRCH_Game23WOTSTW_THFC)
  
  proc choose'() : unit = { 
    O_R_DistRCH_Game23WOTSTW.init(witness, witness);
    O_R_DistRCH_Game23WOTSTW_THFC.init(witness);
    
    A.choose();  
  }

  proc distinguish'(ps : pseed) : bool = {
    var i : int;
    var ad : adrs;
    var m, m' : msgWOTS;
    var pk : pkWOTS;
    var sig, sig' : sigWOTS;
    var is_valid, is_fresh, dist_wgpidxs : bool;
    var adlO, adlOC : adrs list;
    var nrqs : int;
        
    (i, m', sig') <@ A.forge(ps);
    
    (ad, m, pk, sig) <@ O_R_DistRCH_Game23WOTSTW.get(i);
    
    is_valid <@ WOTS_TW_ES.verify((pk, ps, ad), m', sig');

    is_fresh <- m' <> m;
    
    nrqs <@ O_R_DistRCH_Game23WOTSTW.nr_queries();
    
    dist_wgpidxs <@ O_R_DistRCH_Game23WOTSTW.dist_addresses();
       
    adlO <@ O_R_DistRCH_Game23WOTSTW.get_addresses();
        
    adlOC <@ O_R_DistRCH_Game23WOTSTW_THFC.get_tweaks();  
    
    return 0 <= nrqs <= d /\ 0 <= i < nrqs /\ 
           is_valid /\ is_fresh /\ dist_wgpidxs /\ disj_wgpidxs adlO adlOC;
  }

  proc pick() : unit = {
    O_DistRCH.i <$ [0..(w - 3)];
    O_DistRCH.init(witness, witness);
    
    choose'();
  }
  
  proc distinguish(ps : pseed) : bool = {
    var b' : bool;
    
    b' <@ distinguish'(ps);
    
    return b';
  }
}.

(* 
  Reduction adversary that reduces from SM_DT_TCR_C (for f and thfc) to distinguishing between 
  Game3_WOTSTWES and Game4_WOTSTWES 
*)
module (R_SMDTTCRC_Game34WOTSTWES (A : Adv_MEUFGCMA_WOTSTWES) : Adv_SMDTTCRC) (O : Oracle_SMDTTCR, OC : Oracle_THFC) = {
  module O_R_SMDTTCRC_Game34WOTSTWES : Oracle_MEUFGCMA_WOTSTWES = {
    include var O_MEUFGCMA_WOTSTWES [-init, query]
    var xll : dgstblock list list
    
    proc init(ss_init : sseed, ps_init : pseed) = {
      qs <- [];
      xll <- [];
    }
    
    proc query(wad : wadrs, m : msgWOTS) : pkWOTS * sigWOTS = {
      var ad : adrs;
      var x : dgstblock;
      var em : emsgWOTS;
      var pk : dgstblock list;
      var sig : dgstblock list;
      var em_ele : int;
      var pk_ele, sig_ele : dgstblock;
      var xl : dgstblock list;      
      var j : int;
      var pksig : pkWOTS * sigWOTS;
      var admpksig : adrs * msgWOTS * pkWOTS * sigWOTS;
      
      ad <- val wad;
      
      xl <$ ddgstblockl;

      em <- encode_msgWOTS m;

      pk <- [];
      sig <- [];
      while (size pk < len) {
        x <- nth witness xl (size pk);

        em_ele <- BaseW.val em.[size pk];  
        if (em_ele = 0) {
          sig_ele <- x; 
        } else {
          sig_ele <@ O.query(set_hidx (set_chidx ad (size pk)) (em_ele - 1), val x);
        }

        (* pk_ele <- cf ps ad' em_ele (w - 1 - em_ele) sig_ele; *)
        pk_ele <- sig_ele;
        j <- 0;
        while (j < w - 1 - em_ele) {
          pk_ele <@ O.query(set_hidx (set_chidx ad (size pk)) (em_ele + j), val pk_ele);
          j <- j + 1;
        }

        sig <- rcons sig sig_ele;
        pk <- rcons pk pk_ele;
      }

      xll <- rcons xll xl;

      admpksig <- (ad, m, insubd pk, insubd sig);
      qs <- rcons qs admpksig; 

      pksig <- (insubd pk, insubd sig);
      
      return pksig;
    }
    
    proc get_queries() : (adrs * msgWOTS * pkWOTS * sigWOTS) list = {
      return qs;
    }
  }
  
  module A = A(O_R_SMDTTCRC_Game34WOTSTWES, OC)
  
  proc pick() : unit = {
    O_R_SMDTTCRC_Game34WOTSTWES.init(witness, witness);
    
    A.choose();
  }
  
  proc find(ps : pseed) : int * dgst = {
    var ad : adrs;
    var m, m' : msgWOTS;
    var pk : pkWOTS;
    var sig, sig' : sigWOTS;
    var em, em' : emsgWOTS;
    var qs : (adrs * msgWOTS * pkWOTS * sigWOTS) list;
    var em_ele : int;
    var pk_ele, sig_ele : dgst;
    var i, j, k : int;
    var x_idx : int;
    var x' : dgst;
    
    (i, m', sig') <@ A.forge(ps);
    
    (ad, m, pk, sig) <@ O_R_SMDTTCRC_Game34WOTSTWES.get(i);
    qs <@ O_R_SMDTTCRC_Game34WOTSTWES.get_queries();
    
    em <- encode_msgWOTS m;
    em' <- encode_msgWOTS m';
    
    j <- find_chwcollidx ps ad em em' sig sig';
    
    k <- find_collidx_l ps (set_chidx ad j) (BaseW.val em.[j]) (BaseW.val em'.[j]) (val (nth witness (val sig) j)) (val (nth witness (val sig') j)) + 1;
    
    x_idx <- qsdgtcr_idx qs O_R_SMDTTCRC_Game34WOTSTWES.xll ps i j k;
    
    x' <- val (extr_coll_r ps (set_chidx ad j) (BaseW.val em.[j]) (BaseW.val em'.[j]) (val (nth witness (val sig) j)) (val (nth witness (val sig') j)));
    
    return (x_idx, x');
  }
}.

(* Reduction adversary that reduces from SM_DT_PRE_C (for f and thfc) to Game4_WOTSTWES *)
module (R_SMDTPREC_Game4WOTSTWES (A : Adv_MEUFGCMA_WOTSTWES) : Adv_SMDTPREC) (O : Oracle_SMDTPRE, OC : Oracle_THFC) = {
  module O_R_SMDTPREC_Game4WOTSTWES : Oracle_MEUFGCMA_WOTSTWES = {
    include var O_MEUFGCMA_WOTSTWES [-query, init]
    var adl : adrs list
    
    proc init(ss_init : sseed, ps_init : pseed) = {
      qs <- [];
      adl <- [];
    }
    
    proc query(wad : wadrs, m : msgWOTS) : pkWOTS * sigWOTS = {
      var ad : adrs;
      var y : dgst;
      var em : emsgWOTS;
      var pk : dgstblock list;
      var sig : dgstblock list;
      var em_ele : int;
      var pk_ele, sig_ele : dgstblock;
      var yl : dgst list;      
      var j : int;
      var pksig : pkWOTS * sigWOTS;
      var admpksig : adrs * msgWOTS * pkWOTS * sigWOTS;
      
      ad <- val wad;
      
      em <- encode_msgWOTS m;
      
      pk <- [];
      sig <- [];
      while (size pk < len) {
        em_ele <- BaseW.val em.[size pk];
        if (em_ele = 0) {
          sig_ele <$ ddgstblock;
        } else {
          sig_ele <@ O.query(set_hidx (set_chidx ad (size pk)) (em_ele - 1));
        }

        (* pk_ele <- cf ps ad' em_ele (w - 1 - em_ele) sig_ele; *)
        pk_ele <- sig_ele;
        j <- 0;
        while (j < w - 1 - em_ele) {
          pk_ele <@ OC.query(set_hidx (set_chidx ad (size pk)) (em_ele + j), val pk_ele);
          adl <- rcons adl (set_hidx (set_chidx ad (size pk)) (em_ele + j));
          j <- j + 1;
        }

        sig <- rcons sig sig_ele;
        pk <- rcons pk pk_ele;
      }

      admpksig <- (ad, m, insubd pk, insubd sig);
      qs <- rcons qs admpksig; 

      pksig <- (insubd pk, insubd sig);
      
      return pksig;
    }
    
    proc get_queries() : (adrs * msgWOTS * pkWOTS * sigWOTS) list = {
      return qs;
    }
  }

  module A = A(O_R_SMDTPREC_Game4WOTSTWES, OC)
  
  proc pick() : unit = {
    O_R_SMDTPREC_Game4WOTSTWES.init(witness, witness);
    
    A.choose();
  }
  
  proc find(ps : pseed) : int * dgst = {
    var ad : adrs;
    var m, m' : msgWOTS;
    var pk : pkWOTS;
    var sig, sig' : sigWOTS;
    var em, em' : emsgWOTS;
    var qs : (adrs * msgWOTS * pkWOTS * sigWOTS) list;
    var em_ele : int;
    var pk_ele, sig_ele : dgst;
    var i, j : int;
    var x_idx : int;
    var x : dgst;
    
    (i, m', sig') <@ A.forge(ps);
    
    (ad, m, pk, sig) <@ O_R_SMDTPREC_Game4WOTSTWES.get(i);
    qs <@ O_R_SMDTPREC_Game4WOTSTWES.get_queries();
    
    em <- encode_msgWOTS m;
    em' <- encode_msgWOTS m';
    
    j <- find_chwpreidx ps ad em em' sig sig';
    
    x_idx <- qsdgpre_idx qs i j;
    
    x <- val (extr_pre ps (set_chidx ad j) (BaseW.val em.[j]) (BaseW.val em'.[j]) (val (nth witness (val sig') j))); 
    
    return (x_idx, x);
  }
}.


(* -- Proof of M-EUF-GCMA for WOTS-TW (in an encompassing structure) -- *)
section Proof_M_EUF_GCMA_WOTSTWES.
(* - (Auxiliary) Imports - *)
(* 
  Import necessary definitions/properties to reason about programs sampling from
  dlist distributions
*)  
local clone import DList.Program as DListSample with
  type t <- dgstblock,
    op d <- ddgstblock
    
    proof *.


(* - (Auxiliary) Adversary classes and oracle interfaces - *)
(* Type of oracle given to adversaries in DistRCH game *)
local module type Oracle_DistRCH  = {
  proc init(b_init : bool, ps_init : pseed) : unit
  proc query(wad : wadrs, m : msgWOTS) : dgstblock list
}.

(* Class of adversaries against DistRCH game *)
local module type Adv_DistRCH(O : Oracle_DistRCH, OC : Oracle_THFC) = {
  proc choose() : unit { O.query, OC.query }
  proc distinguish(ps : pseed) : bool {}
}.


(* - Module declarations - *)
(* Adversary against M-EUF-GCMA of WOTW-TW (in an encompassing structure) *)
declare module A <: Adv_MEUFGCMA_WOTSTWES {
  -O_MEUFGCMA_WOTSTWES, -O_PRF_Default, -O_SMDTUD_Default, -O_SMDTTCR_Default, -O_SMDTPRE_Default, -O_THFC_Default,
  -R_SMDTUDC_Game23WOTSTWES, -R_SMDTTCRC_Game34WOTSTWES, -R_SMDTPREC_Game4WOTSTWES, -R_PRF_Game0NOPRFWOTSTWES
}.

(* 
  The adversary's choose procedure always terminates if the oracle procedures it can 
  call during its execution terminate 
*)
declare axiom A_choose_ll (O <: Oracle_MEUFGCMA_WOTSTWES {-A} ) (OC <: Oracle_THFC {-A} ) :
  islossless O.query => islossless OC.query => islossless A(O, OC).choose.

(* The adversary's forge procedure always terminates *)
declare axiom A_forge_ll (O <: Oracle_MEUFGCMA_WOTSTWES {-A} ) (OC <: Oracle_THFC {-A} ) :
  islossless A(O, OC).forge.


(* - Oracle implementations - *)
(* Implementation of oracle given to adversary in Game0_WOTSTWES. *)
local module O_Game0_WOTSTWES : Oracle_MEUFGCMA_WOTSTWES = {
  include var O_MEUFGCMA_WOTSTWES [-query]
  
  proc query(wad : wadrs, m : msgWOTS) : pkWOTS * sigWOTS = {
    var ad : adrs;
    var pk : dgstblock list;
    var sk : dgstblock list;
    var sig : dgstblock list;
    var em : emsgWOTS;
    var pk_ele, sk_ele, sig_ele : dgstblock;
    var em_ele : int;
    var pksig : pkWOTS * sigWOTS;
    var admpksig : adrs * msgWOTS * pkWOTS * sigWOTS;
    
    ad <- val wad;
    
    sk <- [];
    while (size sk < len) {
      sk_ele <- prf_sk ss (ps, (set_hidx (set_chidx ad (size sk)) 0));
      sk <- rcons sk sk_ele;
    }

    pk <- [];
    while (size pk < len){
      sk_ele <- nth witness sk (size pk);
      pk_ele <- cf ps (set_chidx ad (size pk)) 0 (w - 1) (val sk_ele);
      pk <- rcons pk pk_ele;
    }

    em <- encode_msgWOTS m;
    sig <- [];
    while (size sig < len){
      sk_ele <- nth witness sk (size sig);
      em_ele <- BaseW.val em.[size sig];
      sig_ele <- cf ps (set_chidx ad (size sig)) 0 em_ele (val sk_ele);
      sig <- rcons sig sig_ele;
    }

    admpksig <- (ad, m, insubd pk, insubd sig);
    qs <- rcons qs admpksig;

    pksig <- (insubd pk, insubd sig);
        
    return pksig;
  }
}.

(* 
  Implementation of oracle given to adversary in Game2_WOTSTWES.
  Swaps signing and public key generation.
*)
local module O_Game2_WOTSTWES : Oracle_MEUFGCMA_WOTSTWES = {
  include var O_MEUFGCMA_WOTSTWES [-query]
  
  proc query(wad : wadrs, m : msgWOTS) : pkWOTS * sigWOTS = {
    var ad : adrs;
    var pk : dgstblock list;
    var sk : dgstblock list;
    var sig : dgstblock list;
    var em : emsgWOTS;
    var pk_ele, sk_ele, sig_ele : dgstblock;
    var em_ele : int;
    var pksig : pkWOTS * sigWOTS; 
    var admpksig : adrs * msgWOTS * pkWOTS * sigWOTS;
    
    ad <- val wad;
    
    sk <$ ddgstblockl;

    em <- encode_msgWOTS m;
    sig <- [];
    while (size sig < len) {
      sk_ele <- nth witness sk (size sig);
      em_ele <- BaseW.val em.[size sig];
      sig_ele <- cf ps (set_chidx ad (size sig)) 0 em_ele (val sk_ele);
      sig <- rcons sig sig_ele;
    }

    pk <- [];
    while (size pk < len) {
      sk_ele <- nth witness sk (size pk);
      pk_ele <- cf ps (set_chidx ad (size pk)) 0 (w - 1) (val sk_ele);
      pk <- rcons pk pk_ele;
    }

    admpksig <- (ad, m, insubd pk, insubd sig);
    qs <- rcons qs admpksig;

    pksig <- (insubd pk, insubd sig);

    return pksig;
  }
}.

(* 
  Implementation of oracle given to adversary in Game3_WOTSTWES and Game4_WOTSTWES.
  Chains random element once just before the index indicated by the encoded message
  to get signature (instead of chaining from 0 to this index). Afterward, public key
  is computed by finishing the chains of the signature.
*)
local module O_Game34_WOTSTWES : Oracle_MEUFGCMA_WOTSTWES = {
  include var O_MEUFGCMA_WOTSTWES [-query]
  
  proc query(wad : wadrs, m : msgWOTS) : pkWOTS * sigWOTS = {
    var ad : adrs;
    var pk : dgstblock list;
    var sk : dgstblock list;
    var sig : dgstblock list;
    var em : emsgWOTS;
    var pk_ele, sk_ele, sig_ele : dgstblock;
    var em_ele : int;
    var pksig : pkWOTS * sigWOTS;
    var admpksig : adrs * msgWOTS * pkWOTS * sigWOTS;
    
    ad <- val wad;
    
    sk <$ ddgstblockl;

    em <- encode_msgWOTS m;
    sig <- [];
    while (size sig < len) {
      sk_ele <- nth witness sk (size sig);

      em_ele <- BaseW.val em.[size sig];
      if (em_ele = 0) { 
        sig_ele <- sk_ele;
      } else {
        sig_ele <- cf ps (set_chidx ad (size sig)) (em_ele - 1) 1 (val sk_ele);
      }

      sig <- rcons sig sig_ele;
    }

    pk <- [];
    while (size pk < len){
      sig_ele <- nth witness sig (size pk);
      em_ele <- BaseW.val em.[size pk];
      pk_ele <- cf ps (set_chidx ad (size pk)) em_ele (w - 1 - em_ele) (val sig_ele);
      pk <- rcons pk pk_ele;
    }

    admpksig <- (ad, m, insubd pk, insubd sig);
    qs <- rcons qs admpksig;

    pksig <- (insubd pk, insubd sig);
    
    return pksig;
  }
}.

(* Implementation of oracle given to adversary in DistRCH *)
local module O_DistRCH : Oracle_DistRCH = {
  var b : bool
  var ps : pseed
  
  proc init(b_init : bool, ps_init : pseed) : unit = {
    b <- b_init;
    ps <- ps_init;
  }
  
  proc query(wad : wadrs, m : msgWOTS) : dgstblock list = {
    var ad : adrs;
    var em : emsgWOTS;
    var chal, chal' : dgstblock list;
    var chal_ele, chal_ele' : dgstblock;
    var em_ele : int;
    
    ad <- val wad;
    
    chal' <$ ddgstblockl;
    
    if (b) {
      chal <- chal';
    } else {
      em <- encode_msgWOTS m;
      chal <- [];
      while (size chal < len) {
        chal_ele' <- nth witness chal' (size chal);
        em_ele <- BaseW.val em.[size chal];
        chal_ele <- cf ps (set_chidx ad (size chal)) 0 (em_ele - 1) (val chal_ele');
        chal <- rcons chal chal_ele;
      }
    }
    
    return chal;
  }
}.

(* 
  Auxiliary implementations for O_MEUFGCMA_WOTSTWES_NOPRF, used to obtain the desired form
  for the proof of the PRF reduction 
*)  
local module O_MEUFGCMA_WOTSTWES_NOPRF_SampleSample : Oracle_MEUFGCMA_WOTSTWES = {
  include var O_MEUFGCMA_WOTSTWES [-query]
  
  proc query(wad : wadrs, m : msgWOTS) : pkWOTS * sigWOTS = {
    var ad : adrs;
    var pk : dgstblock list;
    var sk : dgstblock list;
    var sig : dgstblock list;
    var em : emsgWOTS;
    var pk_ele, sk_ele, sig_ele : dgstblock;
    var em_ele : int;
    var pksig : pkWOTS * sigWOTS;
    var admpksig : adrs * msgWOTS * pkWOTS * sigWOTS;
    
    ad <- val wad;
    
    sk <@ Sample.sample(len);

    pk <- [];
    while (size pk < len){
      sk_ele <- nth witness sk (size pk);
      pk_ele <- cf ps (set_chidx ad (size pk)) 0 (w - 1) (val sk_ele);
      pk <- rcons pk pk_ele;
    }

    em <- encode_msgWOTS m;
    sig <- [];
    while (size sig < len){
      sk_ele <- nth witness sk (size sig);
      em_ele <- BaseW.val em.[size sig];
      sig_ele <- cf ps (set_chidx ad (size sig)) 0 em_ele (val sk_ele);
      sig <- rcons sig sig_ele;
    }

    admpksig <- (ad, m, insubd pk, insubd sig);
    qs <- rcons qs admpksig;

    pksig <- (insubd pk, insubd sig);
        
    return pksig;
  }
}.

local module O_MEUFGCMA_WOTSTWES_NOPRF_LoopSnocSample : Oracle_MEUFGCMA_WOTSTWES = {
  include var O_MEUFGCMA_WOTSTWES [-query]
  
  proc query(wad : wadrs, m : msgWOTS) : pkWOTS * sigWOTS = {
    var ad : adrs;
    var pk : dgstblock list;
    var sk : dgstblock list;
    var sig : dgstblock list;
    var em : emsgWOTS;
    var pk_ele, sk_ele, sig_ele : dgstblock;
    var em_ele : int;
    var pksig : pkWOTS * sigWOTS;
    var admpksig : adrs * msgWOTS * pkWOTS * sigWOTS;
    
    ad <- val wad;
    
    sk <@ LoopSnoc.sample(len);

    pk <- [];
    while (size pk < len){
      sk_ele <- nth witness sk (size pk);
      pk_ele <- cf ps (set_chidx ad (size pk)) 0 (w - 1) (val sk_ele);
      pk <- rcons pk pk_ele;
    }

    em <- encode_msgWOTS m;
    sig <- [];
    while (size sig < len){
      sk_ele <- nth witness sk (size sig);
      em_ele <- BaseW.val em.[size sig];
      sig_ele <- cf ps (set_chidx ad (size sig)) 0 em_ele (val sk_ele);
      sig <- rcons sig sig_ele;
    }

    admpksig <- (ad, m, insubd pk, insubd sig);
    qs <- rcons qs admpksig;

    pksig <- (insubd pk, insubd sig);
        
    return pksig;
  }
}.

local module O_MEUFGCMA_WOTSTWES_NOPRF_Alt : Oracle_MEUFGCMA_WOTSTWES = {
  include var O_MEUFGCMA_WOTSTWES [-query]
  
  proc query(wad : wadrs, m : msgWOTS) : pkWOTS * sigWOTS = {
    var ad : adrs;
    var pk : dgstblock list;
    var sk : dgstblock list;
    var sig : dgstblock list;
    var em : emsgWOTS;
    var pk_ele, sk_ele, sig_ele : dgstblock;
    var em_ele : int;
    var pksig : pkWOTS * sigWOTS;
    var admpksig : adrs * msgWOTS * pkWOTS * sigWOTS;

    ad <- val wad;

    sk <- [];
    while (size sk < len) {
      sk_ele <$ ddgstblock;
      sk <- rcons sk sk_ele;
    }

    pk <- [];
    while (size pk < len){
      sk_ele <- nth witness sk (size pk);
      pk_ele <- cf ps (set_chidx ad (size pk)) 0 (w - 1) (val sk_ele);
      pk <- rcons pk pk_ele;
    }

    em <- encode_msgWOTS m;
    sig <- [];
    while (size sig < len){
      sk_ele <- nth witness sk (size sig);
      em_ele <- BaseW.val em.[size sig];
      sig_ele <- cf ps (set_chidx ad (size sig)) 0 em_ele (val sk_ele);
      sig <- rcons sig sig_ele;
    }

    admpksig <- (ad, m, insubd pk, insubd sig);
    qs <- rcons qs admpksig;

    pksig <- (insubd pk, insubd sig);
        
    return pksig;
  }
}.

(* Equivalences between original and auxiliary implementations of O_MEUFGCMA_WOTSTWES_NOPRF *)
local equiv O_MEUFGCMA_WOTSTWES_NOPRF_Orig_SampleSample : 
  O_MEUFGCMA_WOTSTWES_NOPRF.query ~ O_MEUFGCMA_WOTSTWES_NOPRF_SampleSample.query : 
    ={O_MEUFGCMA_WOTSTWES.ps, O_MEUFGCMA_WOTSTWES.qs, wad, m} ==> ={O_MEUFGCMA_WOTSTWES.ps, O_MEUFGCMA_WOTSTWES.qs, res}.
proof.
proc; inline *.
by sim; auto.
qed.

local equiv O_MEUFGCMA_WOTSTWES_NOPRF_SampleSample_LoopSnocSample : 
  O_MEUFGCMA_WOTSTWES_NOPRF_SampleSample.query ~ O_MEUFGCMA_WOTSTWES_NOPRF_LoopSnocSample.query : 
    ={O_MEUFGCMA_WOTSTWES.ps, O_MEUFGCMA_WOTSTWES.qs, wad, m} ==> ={O_MEUFGCMA_WOTSTWES.ps, O_MEUFGCMA_WOTSTWES.qs, res}.
proof.
proc.
seq 2 2 : (#pre /\ ={ad, sk}) => /=; last by sim.
by sp; call Sample_LoopSnoc_eq; skip.
qed.

local equiv O_MEUFGCMA_WOTSTWES_NOPRF_LoopSnocSample_Alt : 
  O_MEUFGCMA_WOTSTWES_NOPRF_LoopSnocSample.query ~ O_MEUFGCMA_WOTSTWES_NOPRF_Alt.query : 
    ={O_MEUFGCMA_WOTSTWES.ps, O_MEUFGCMA_WOTSTWES.qs, wad, m} ==> ={O_MEUFGCMA_WOTSTWES.ps, O_MEUFGCMA_WOTSTWES.qs, res}.
proof.
proc; inline *.
seq 5 3 : (={O_MEUFGCMA_WOTSTWES.ps, O_MEUFGCMA_WOTSTWES.qs, ad, m} /\ l{1} = sk{2}); last by sim => /#.
while (   #post
       /\ n{1} = len
       /\ i{1} = size sk{2} 
       /\ 0 <= i{1} <= len); last by auto; smt(ge2_len).
by wp; rnd; skip => />; smt(size_rcons cats1).
qed.

local equiv O_MEUFGCMA_WOTSTWES_NOPRF_Orig_Alt : 
  O_MEUFGCMA_WOTSTWES_NOPRF.query ~ O_MEUFGCMA_WOTSTWES_NOPRF_Alt.query : 
    ={O_MEUFGCMA_WOTSTWES.ps, O_MEUFGCMA_WOTSTWES.qs, wad, m} ==> ={O_MEUFGCMA_WOTSTWES.ps, O_MEUFGCMA_WOTSTWES.qs, res}.
proof.
transitivity O_MEUFGCMA_WOTSTWES_NOPRF_SampleSample.query 
             (={O_MEUFGCMA_WOTSTWES.ps, O_MEUFGCMA_WOTSTWES.qs, wad, m} ==> ={O_MEUFGCMA_WOTSTWES.ps, O_MEUFGCMA_WOTSTWES.qs, res}) 
             (={O_MEUFGCMA_WOTSTWES.ps, O_MEUFGCMA_WOTSTWES.qs, wad, m} ==> ={O_MEUFGCMA_WOTSTWES.ps, O_MEUFGCMA_WOTSTWES.qs, res}) => [/# | // | |].
+ by apply O_MEUFGCMA_WOTSTWES_NOPRF_Orig_SampleSample.
transitivity O_MEUFGCMA_WOTSTWES_NOPRF_LoopSnocSample.query 
             (={O_MEUFGCMA_WOTSTWES.ps, O_MEUFGCMA_WOTSTWES.qs, wad, m} ==> ={O_MEUFGCMA_WOTSTWES.ps, O_MEUFGCMA_WOTSTWES.qs, res}) 
             (={O_MEUFGCMA_WOTSTWES.ps, O_MEUFGCMA_WOTSTWES.qs, wad, m} ==> ={O_MEUFGCMA_WOTSTWES.ps, O_MEUFGCMA_WOTSTWES.qs, res}) => [/# | // | |].
+ by apply O_MEUFGCMA_WOTSTWES_NOPRF_SampleSample_LoopSnocSample.
by apply O_MEUFGCMA_WOTSTWES_NOPRF_LoopSnocSample_Alt.
qed.

(* 
  Auxiliary implementations for O_Game34_WOTSTWES, used to obtain the desired form
  for the proof of the SM_DT_PRE_C reduction 
*)  
local module O_Game34_WOTSTWES_SampleSample : Oracle_MEUFGCMA_WOTSTWES = {
  include var O_MEUFGCMA_WOTSTWES [-query]
  
  proc query(wad : wadrs, m : msgWOTS) : pkWOTS * sigWOTS = {
    var ad : adrs;
    var pk : dgstblock list;
    var sk : dgstblock list;
    var sig : dgstblock list;
    var em : emsgWOTS;
    var pk_ele, sk_ele, sig_ele : dgstblock;
    var em_ele : int;
    var pksig : pkWOTS * sigWOTS;
    var admpksig : adrs * msgWOTS * pkWOTS * sigWOTS;

    ad <- val wad;
    
    sk <@ Sample.sample(len);

    em <- encode_msgWOTS m;
    sig <- [];
    while (size sig < len) {
      sk_ele <- nth witness sk (size sig);

      em_ele <- BaseW.val em.[size sig];
      if (em_ele = 0) { 
        sig_ele <- sk_ele;
      } else {
        sig_ele <- cf ps (set_chidx ad (size sig)) (em_ele - 1) 1 (val sk_ele);
      }

      sig <- rcons sig sig_ele;
    }

    pk <- [];
    while (size pk < len){
      sig_ele <- nth witness sig (size pk);
      em_ele <- BaseW.val em.[size pk];
      pk_ele <- cf ps (set_chidx ad (size pk)) em_ele (w - 1 - em_ele) (val sig_ele);
      pk <- rcons pk pk_ele;
    }

    admpksig <- (ad, m, insubd pk, insubd sig);
    qs <- rcons qs admpksig;

    pksig <- (insubd pk, insubd sig);
    
    return pksig;
  }
}.

local module O_Game34_WOTSTWES_LoopSnocSample : Oracle_MEUFGCMA_WOTSTWES = {
  include var O_MEUFGCMA_WOTSTWES [-query]
  
  proc query(wad : wadrs, m : msgWOTS) : pkWOTS * sigWOTS = {
    var ad : adrs;
    var pk : dgstblock list;
    var sk : dgstblock list;
    var sig : dgstblock list;
    var em : emsgWOTS;
    var pk_ele, sk_ele, sig_ele : dgstblock;
    var em_ele : int;
    var pksig : pkWOTS * sigWOTS;
    var admpksig : adrs * msgWOTS * pkWOTS * sigWOTS;
    var i : int;
    
    ad <- val wad;

    sk <@ LoopSnoc.sample(len);

    em <- encode_msgWOTS m;
    sig <- [];
    i <- 0;
    while (i < len) {
      sk_ele <- nth witness sk i;

      em_ele <- BaseW.val em.[i];
      if (em_ele = 0) { 
        sig_ele <- sk_ele;
      } else {
        sig_ele <- cf ps (set_chidx ad i) (em_ele - 1) 1 (val sk_ele);
      }

      sig <- rcons sig sig_ele;
      i <- i + 1;
    }

    pk <- [];
    while (size pk < len){
      sig_ele <- nth witness sig (size pk);
      em_ele <- BaseW.val em.[size pk];
      pk_ele <- cf ps (set_chidx ad (size pk)) em_ele (w - 1 - em_ele) (val sig_ele);
      pk <- rcons pk pk_ele;
    }

    admpksig <- (ad, m, insubd pk, insubd sig);
    qs <- rcons qs admpksig;

    pksig <- (insubd pk, insubd sig);
    
    return pksig;
  }
}.

local module O_Game34_WOTSTWES_LoopSnocSampleAlt : Oracle_MEUFGCMA_WOTSTWES = {
  include var O_MEUFGCMA_WOTSTWES [-query]
  
  proc query(wad : wadrs, m : msgWOTS) : pkWOTS * sigWOTS = {
    var ad : adrs;
    var pk : dgstblock list;
    var sk : dgstblock list;
    var sig : dgstblock list;
    var em : emsgWOTS;
    var pk_ele, sk_ele, sig_ele : dgstblock;
    var em_ele : int;
    var pksig : pkWOTS * sigWOTS;
    var admpksig : adrs * msgWOTS * pkWOTS * sigWOTS;
    
    ad <- val wad;

    sk <- [];
    while (size sk < len) {
      sk_ele <$ ddgstblock;
      sk <- rcons sk sk_ele;
    }

    em <- encode_msgWOTS m;
    sig <- [];
    while (size sig < len) {
      sk_ele <- nth witness sk (size sig);

      em_ele <- BaseW.val em.[size sig];
      if (em_ele = 0) { 
        sig_ele <- sk_ele;
      } else {
        sig_ele <- cf ps (set_chidx ad (size sig)) (em_ele - 1) 1 (val sk_ele);
      }

      sig <- rcons sig sig_ele;
    }

    pk <- [];
    while (size pk < len){
      sig_ele <- nth witness sig (size pk);
      em_ele <- BaseW.val em.[size pk];
      pk_ele <- cf ps (set_chidx ad (size pk)) em_ele (w - 1 - em_ele) (val sig_ele);
      pk <- rcons pk pk_ele;
    }

    admpksig <- (ad, m, insubd pk, insubd sig);
    qs <- rcons qs admpksig;

    pksig <- (insubd pk, insubd sig);
    
    return pksig;
  }
}.

local module O_Game34_WOTSTWES_Alt : Oracle_MEUFGCMA_WOTSTWES = {
  include var O_MEUFGCMA_WOTSTWES [-query]
  
  proc query(wad : wadrs, m : msgWOTS) : pkWOTS * sigWOTS = {
    var ad : adrs;
    var pk : dgstblock list;
    var sk : dgstblock list;
    var sig : dgstblock list;
    var em : emsgWOTS;
    var pk_ele, sk_ele, sig_ele : dgstblock;
    var em_ele : int;
    var pksig : pkWOTS * sigWOTS;
    var admpksig : adrs * msgWOTS * pkWOTS * sigWOTS;
    
    ad <- val wad;
    
    em <- encode_msgWOTS m;
    sk <- [];
    sig <- [];
    while (size sig < len) {
      sk_ele <$ ddgstblock;
      
      em_ele <- BaseW.val em.[size sig];
      if (em_ele = 0) { 
        sig_ele <- sk_ele;
      } else {
        sig_ele <- cf ps (set_chidx ad (size sig)) (em_ele - 1) 1 (val sk_ele);
      }

      sk <- rcons sk sk_ele;
      sig <- rcons sig sig_ele;
    }

    pk <- [];
    while (size pk < len){
      sig_ele <- nth witness sig (size pk);
      em_ele <- BaseW.val em.[size pk];
      pk_ele <- cf ps (set_chidx ad (size pk)) em_ele (w - 1 - em_ele) (val sig_ele);
      pk <- rcons pk pk_ele;
    }

    admpksig <- (ad, m, insubd pk, insubd sig);
    qs <- rcons qs admpksig;

    pksig <- (insubd pk, insubd sig);
    
    return pksig;
  }
}.

(* Equivalences between original and auxiliary implementations of O_Game34_WOTSTWES *)
local equiv O_Game34_WOTSTWES_Orig_SampleSample : 
  O_Game34_WOTSTWES.query ~ O_Game34_WOTSTWES_SampleSample.query : 
    ={glob O_MEUFGCMA_WOTSTWES, wad, m} ==> ={glob O_MEUFGCMA_WOTSTWES, res}.
proof.
proc; inline *.
by sim; auto.
qed.

local equiv O_Game34_WOTSTWES_SampleSample_LoopSnocSample : 
  O_Game34_WOTSTWES_SampleSample.query ~ O_Game34_WOTSTWES_LoopSnocSample.query : 
    ={glob O_MEUFGCMA_WOTSTWES, wad, m} ==> ={glob O_MEUFGCMA_WOTSTWES, res}.
proof.
proc.
seq 2 2 : (#pre /\ ={ad, sk}) => /=.
+ by sp; call Sample_LoopSnoc_eq; skip.
sp; sim.
while (   ={O_MEUFGCMA_WOTSTWES.ps, ad, m, sk, sig, em}
       /\ size sig{1} = i{2}
       /\ 0 <= i{2} <= len
       /\ 0 <= size sig{1} <= len).
+ auto => |>; smt(size_rcons).
by auto => |>; smt(ge2_len).  
qed.

local equiv O_Game34_WOTSTWES_LoopSnocSample_LoopSnocSampleAlt : 
  O_Game34_WOTSTWES_LoopSnocSample.query ~ O_Game34_WOTSTWES_LoopSnocSampleAlt.query : 
    ={glob O_MEUFGCMA_WOTSTWES, wad, m} ==> ={glob O_MEUFGCMA_WOTSTWES, res}.
proof.
proc; inline *.
seq 9 5 : (#pre /\ ={ad, sk, em, sig} /\  i{1} = 0 /\ sig{1} = [] /\ sig{2} = []) => /=.
+ sp; wp => /=.
  while (   ={O_MEUFGCMA_WOTSTWES.ps, ad, m}
         /\ n{1} = len
         /\ l{1} = sk{2}
         /\ i0{1} = size sk{2}
         /\ 0 <= i0{1} <= len
         /\ 0 <= size sk{2} <= len).
  - by auto => |>; smt(cats1 size_rcons).
  by auto => |>; smt(ge2_len).
sim => /=.
while (   ={O_MEUFGCMA_WOTSTWES.ps, ad, m, sk, em, sig}
       /\ i{1} = size sig{2}
       /\ 0 <= i{1} <= len
       /\ 0 <= size sig{2} <= len).
+ by auto => |>; smt(size_rcons).
by auto => |>; smt(ge2_len).
qed.

local equiv O_Game34_WOTSTWES_LoopSnocSampleAlt_Alt : 
  O_Game34_WOTSTWES_LoopSnocSampleAlt.query ~ O_Game34_WOTSTWES_Alt.query : 
    ={glob O_MEUFGCMA_WOTSTWES, wad, m} ==> ={glob O_MEUFGCMA_WOTSTWES, res}.
proof.
proc; inline *.
seq 5 5 : (   #pre 
           /\ ={ad, sk, em} 
           /\ sig{1} = []
           /\ (forall (i : int), 0 <= i < len =>
                 nth witness sig{2} i =
                 if BaseW.val em{2}.[i] <> 0
                 then cf O_MEUFGCMA_WOTSTWES.ps{2} (set_chidx ad{2} i) (BaseW.val em{2}.[i] - 1) 1 (val (nth witness sk{2} i))
                 else nth witness sk{2} i)
           /\ size sig{2} = len) => /=.
+ swap{1} [4..5] -1; swap{2} 3 -1; sp; wp => /=.
  while (   ={O_MEUFGCMA_WOTSTWES.ps, ad, m, sk, em}
         /\ valid_wadrs ad{1}
         /\ sig{1} = [] 
         /\ (forall (i : int), 0 <= i < size sig{2} =>
               nth witness sig{2} i =
               if BaseW.val em{2}.[i] <> 0
               then cf O_MEUFGCMA_WOTSTWES.ps{2} (set_chidx ad{2} i) (BaseW.val em{2}.[i] - 1) 1 (val (nth witness sk{2} i))
               else nth witness sk{2} i)
         /\ size sk{1} = size sig{2}
         /\ 0 <= size sk{1} <= len
         /\ 0 <= size sig{2} <= len).
  - auto => |> &1 adch valsig eq_sz ge0_szsk lelen_szsk ge0_szsig lelen_szsig ltlen_szsk ltlen_szsig sk_ele skelein. 
    split => [eq0_em | neq0_em]; first by smt(nth_rcons size_rcons DigestBlock.valKd).
    rewrite -andbA; split; last by smt(nth_rcons size_rcons DigestBlock.valKd).
    move=> i ge0_i; rewrite size_rcons => ltszsig1_i. 
    rewrite 2!nth_rcons (: size sk{1} = size sig{1}) 1:/#.
    case (i < size sig{1}) => [ltszsig_i | /lezNgt geszsig_i]; first by rewrite valsig.
    by rewrite (: i = size sig{1}) 1:/# neq0_em.
  by skip => |>; smt(ge2_len WAddress.valP).
sim => /=.
while{1} (   ={O_MEUFGCMA_WOTSTWES.ps, ad, m, sk, em}
          /\ (forall (i : int),
               0 <= i && i < len =>
               nth witness sig{2} i =
               if BaseW.val em{2}.[i] <> 0
               then cf O_MEUFGCMA_WOTSTWES.ps{2} (set_chidx ad{2} i) (BaseW.val em{2}.[i] - 1) 1 (val (nth witness sk{2} i))
               else nth witness sk{2} i)
          /\ (forall (i : int), 0 <= i < size sig{1} =>
                nth witness sig{1} i = nth witness sig{2} i)
          /\ size sig{2} = len
          /\ 0 <= size sig{1} <= len)
         (len - size sig{1}).
+ move=> &m z.
  by auto => |>; smt(nth_rcons size_rcons DigestBlock.valKd).
auto => |> &1 valsig1 eqlen_szsig. 
split => [| sigl]; first by smt(ge2_len).
split => [/#| *].
by apply (eq_from_nth witness) => [/#|].
qed.

local equiv O_Game34_WOTSTWES_Orig_Alt : 
  O_Game34_WOTSTWES.query ~ O_Game34_WOTSTWES_Alt.query : 
    ={glob O_MEUFGCMA_WOTSTWES, wad, m} ==> ={glob O_MEUFGCMA_WOTSTWES, res}.
proof.
transitivity O_Game34_WOTSTWES_SampleSample.query 
             (={glob O_MEUFGCMA_WOTSTWES, wad, m} ==> ={glob O_MEUFGCMA_WOTSTWES, res}) 
             (={glob O_MEUFGCMA_WOTSTWES, wad, m} ==> ={glob O_MEUFGCMA_WOTSTWES, res}) => [/# | // | |].
+ by apply O_Game34_WOTSTWES_Orig_SampleSample.
transitivity O_Game34_WOTSTWES_LoopSnocSample.query 
             (={glob O_MEUFGCMA_WOTSTWES, wad, m} ==> ={glob O_MEUFGCMA_WOTSTWES, res}) 
             (={glob O_MEUFGCMA_WOTSTWES, wad, m} ==> ={glob O_MEUFGCMA_WOTSTWES, res}) => [/# | // | |].
+ by apply O_Game34_WOTSTWES_SampleSample_LoopSnocSample.
transitivity O_Game34_WOTSTWES_LoopSnocSampleAlt.query 
             (={glob O_MEUFGCMA_WOTSTWES, wad, m} ==> ={glob O_MEUFGCMA_WOTSTWES, res}) 
             (={glob O_MEUFGCMA_WOTSTWES, wad, m} ==> ={glob O_MEUFGCMA_WOTSTWES, res}) => [/# | // | |].
+ by apply O_Game34_WOTSTWES_LoopSnocSample_LoopSnocSampleAlt.
by apply O_Game34_WOTSTWES_LoopSnocSampleAlt_Alt.
qed.


(* - Games in game sequence - *)
(* 
  Game0_WOTSTWES; first game in game sequence.
  Identical to M_EUF_GCMA_WOTSTWES, only differing in the query procedure of the 
  provided Oracle_MEUFGCMA_WOTSTWES (see above for the different oracle implementations). 
*)
local module Game0_WOTSTWES = {
  include M_EUF_GCMA_WOTSTWES(A, O_Game0_WOTSTWES, O_THFC_Default)
}.
 
(* 
  Game2_WOTSTWES; third game in game sequence.
  Identical to M_EUF_GCMA_WOTSTWES, only differing in the 
  query procedure of the provided Oracle_MEUFGCMA_WOTSTWES (see above for the 
  different oracle implementations).
*)
local module Game2_WOTSTWES = {
  include M_EUF_GCMA_WOTSTWES(A, O_Game2_WOTSTWES, O_THFC_Default)
}.

(* 
  Game3_WOTSTWES; fourth game in game sequence.
  Identical to M_EUF_GCMA_WOTSTWES (and hence to Game2_WOTSTWES), only differing in the 
  query procedure of the provided Oracle_MEUFGCMA_WOTSTWES (see above for the 
  different oracle implementations).
*)
local module Game3_WOTSTWES = {
  include M_EUF_GCMA_WOTSTWES(A, O_Game34_WOTSTWES, O_THFC_Default)
}.

(* 
  Game4_WOTSTWES; Fifth and final game in game sequence.
  Identical to Game3_WOTSTWES, except that the game is now lost if the provided forgery
  allows for the extraction of a chain collision
*)
local module Game4_WOTSTWES = {
  module A = A(O_Game34_WOTSTWES, O_THFC_Default)
  
  proc main() : bool = {
    var ps : pseed;
    var ad : adrs;
    var pk : pkWOTS;
    var i : int;
    var m, m' : msgWOTS;
    var em, em' : emsgWOTS;
    var sig, sig': sigWOTS;
    var adlO, adlOC : adrs list;
    var nrqs : int;
    var is_valid, is_fresh, dist_wgpidxs, hchwcoll : bool;

    ps <$ dpseed;
    
    O_Game34_WOTSTWES.init(witness, ps);
    O_THFC_Default.init(ps);
    
    A.choose();

    (i, m', sig') <@ A.forge(ps);
    
    (ad, m, pk, sig) <@ O_Game34_WOTSTWES.get(i);
    
    is_valid <@ WOTS_TW_ES.verify((pk, ps, ad), m', sig');

    is_fresh <- m' <> m;
    
    nrqs <@ O_Game34_WOTSTWES.nr_queries();
    
    dist_wgpidxs <@ O_Game34_WOTSTWES.dist_addresses();
    
    adlO <@ O_Game34_WOTSTWES.get_addresses();
    adlOC <@ O_THFC_Default.get_tweaks();

    em <- encode_msgWOTS m;
    em' <- encode_msgWOTS m';
    hchwcoll <- has_chwcoll ps ad em em' sig sig';

    return 0 <= nrqs <= d /\ 0 <= i < nrqs /\ 
           is_valid /\ is_fresh /\ dist_wgpidxs /\ disj_wgpidxs adlO adlOC /\ !hchwcoll;
  }
}.

(* 
  Game3_WOTSTWES_Chcoll; alternative to the second-to-last game in game sequence.
  Identical to Game3_WOTSTWES (also gets same oracles), but stores whether the provided 
  forgery allows for the extraction of a chain collision in a module variable. 
*)
local module Game3_WOTSTWES_Hchwcoll = {
  var hchwcoll : bool
  
  module A = A(O_Game34_WOTSTWES, O_THFC_Default)
  
  proc main() : bool = {
    var ps : pseed;
    var ad : adrs;
    var pk : pkWOTS;
    var i : int;
    var m, m' : msgWOTS;
    var em, em' : emsgWOTS;
    var sig, sig': sigWOTS;
    var adlO, adlOC : adrs list;
    var nrqs : int;
    var is_valid, is_fresh, dist_wgpidxs : bool;

    ps <$ dpseed;
    
    O_Game34_WOTSTWES.init(witness, ps);
    O_THFC_Default.init(ps);
    
    A.choose();

    (i, m', sig') <@ A.forge(ps);
    
    (ad, m, pk, sig) <@ O_Game34_WOTSTWES.get(i);
    
    is_valid <@ WOTS_TW_ES.verify((pk, ps, ad), m', sig');

    is_fresh <- m' <> m;
    
    dist_wgpidxs <@ O_Game34_WOTSTWES.dist_addresses();
    
    nrqs <@ O_Game34_WOTSTWES.nr_queries();
       
    adlO <@ O_Game34_WOTSTWES.get_addresses();
    adlOC <@ O_THFC_Default.get_tweaks();

    em <- encode_msgWOTS m;
    em' <- encode_msgWOTS m';
    hchwcoll <- has_chwcoll ps ad em em' sig sig';
    
    return 0 <= nrqs <= d /\ 0 <= i < nrqs /\ 
           is_valid /\ is_fresh /\ dist_wgpidxs /\ disj_wgpidxs adlO adlOC;   
  }
}.

(* 
  Game4_WOTSTWES_Alt; alternative to the last game in the game sequence.
  Identical to Game4_WOTSTWES, except that it uses oracle O_Game34_WOTSTWES_Alt instead of
  oracle O_Game34_WOTSTWES
*)
local module Game4_WOTSTWES_Alt = {
  module A = A(O_Game34_WOTSTWES_Alt, O_THFC_Default)
  
  proc main() : bool = {
    var ps : pseed;
    var ad : adrs;
    var pk : pkWOTS;
    var i : int;
    var m, m' : msgWOTS;
    var em, em' : emsgWOTS;
    var sig, sig': sigWOTS;
    var adlO, adlOC : adrs list;
    var nrqs : int;
    var is_valid, is_fresh, dist_wgpidxs, hchwcoll : bool;

    ps <$ dpseed;
    
    O_Game34_WOTSTWES.init(witness, ps);
    O_THFC_Default.init(ps);
    
    A.choose();

    (i, m', sig') <@ A.forge(ps);
    
    (ad, m, pk, sig) <@ O_Game34_WOTSTWES.get(i);
    
    is_valid <@ WOTS_TW_ES.verify((pk, ps, ad), m', sig');

    is_fresh <- m' <> m;
    
    nrqs <@ O_Game34_WOTSTWES.nr_queries();
    
    dist_wgpidxs <@ O_Game34_WOTSTWES.dist_addresses();
    
    adlO <@ O_Game34_WOTSTWES.get_addresses();
    adlOC <@ O_THFC_Default.get_tweaks();

    em <- encode_msgWOTS m;
    em' <- encode_msgWOTS m';
    hchwcoll <- has_chwcoll ps ad em em' sig sig';

    return 0 <= nrqs <= d /\ 0 <= i < nrqs /\ 
           is_valid /\ is_fresh /\ dist_wgpidxs /\ disj_wgpidxs adlO adlOC /\ !hchwcoll;
  }
}.

(* Equivalence between Game4_WOTSTWES and Game4_WOTSTWES_Alt *)
local equiv Game4_WOTSTWES_Orig_Alt :
  Game4_WOTSTWES.main ~ Game4_WOTSTWES_Alt.main : ={glob A} ==> ={res}.
proof.
proc; inline *.
seq 1 1 : (#pre /\ ={ps}); first by rnd.
seq 9 9 : (={glob A, glob O_MEUFGCMA_WOTSTWES, glob O_THFC_Default, ps}); last by sim.
sp => /=.
call (: ={glob O_MEUFGCMA_WOTSTWES, glob O_THFC_Default}); last by auto.
+ conseq (: ={glob O_MEUFGCMA_WOTSTWES, wad, m} ==> ={glob O_MEUFGCMA_WOTSTWES, res}) => //.
  by apply O_Game34_WOTSTWES_Orig_Alt.
by sim.
qed.


(* - Reduction adversaries - *)
(* 
  Reduction adverary that reduces from distinguishing between the relevant distributions
  to distinguishing between Game2_WOTSTWES and Game3_WOTSTWES.
*)
local module (R_DistRCH_Game23WOTSTW : Adv_DistRCH) (O : Oracle_DistRCH, OC : Oracle_THFC) = {
  module O_R_DistRCH_Game23WOTSTW : Oracle_MEUFGCMA_WOTSTWES = {
    include var O_MEUFGCMA_WOTSTWES [-query]

    proc query(wad : wadrs, m : msgWOTS) : pkWOTS * sigWOTS = {
      var ad : adrs;
      var chal : dgstblock list;
      var em : emsgWOTS;
      var pk : dgstblock list;
      var sig : dgstblock list;
      var em_ele : int;
      var pk_ele, sig_ele, chal_ele : dgstblock;
      var pksig : pkWOTS * sigWOTS;
      var admpksig : adrs * msgWOTS * pkWOTS * sigWOTS;
      var j : int;
      
      ad <- val wad;
      
      chal <@ O.query(wad, m);

      em <- encode_msgWOTS m;
      pk <- [];
      sig <- [];
      while (size pk < len) {
        chal_ele <- nth witness chal (size pk);
        em_ele <- BaseW.val em.[size pk];
        if (em_ele = 0) {
          sig_ele <- chal_ele;
        } else {
          sig_ele <@ OC.query(set_hidx (set_chidx ad (size pk)) (em_ele - 1), val chal_ele);
        }

        (* pk_ele <- cf ps (set_chidx ad (size pk)) em_ele (w - 1 - em_ele) sig_ele *)
        pk_ele <- sig_ele;
        j <- 0;
        while (j < w - 1 - em_ele) {
          pk_ele <@ OC.query(set_hidx (set_chidx ad (size pk)) (em_ele + j), val pk_ele);
          j <- j + 1;
        }

        pk <- rcons pk pk_ele;
        sig <- rcons sig sig_ele;
      }

      admpksig <- (ad, m, insubd pk, insubd sig);
      qs <- rcons qs admpksig;

      pksig <- (insubd pk, insubd sig);
      
      return pksig;
    }
  }
 
  module O_R_DistRCH_Game23WOTSTW_THFC : Oracle_THFC = {
    var ps : pseed
    var adl : adrs list
    
    proc init(ps_init : pseed) : unit = {
      ps <- ps_init;
      adl <- [];
    }

    proc query(ad : adrs, x : dgst) : dgstblock = {
      var df : int;
      var y : dgstblock;

      y <@ OC.query(ad, x);
      adl <- rcons adl ad;

      return y;
    }

    proc get_tweaks() : adrs list = {
      return adl;
    }
  }
  
  module A = A(O_R_DistRCH_Game23WOTSTW, O_R_DistRCH_Game23WOTSTW_THFC)
  
  proc choose() : unit = { 
    O_R_DistRCH_Game23WOTSTW.init(witness, witness);
    O_R_DistRCH_Game23WOTSTW_THFC.init(witness);
    
    A.choose();  
  }

  proc distinguish(ps : pseed) : bool = {
    var i : int;
    var ad : adrs;
    var m, m' : msgWOTS;
    var pk : pkWOTS;
    var sig, sig' : sigWOTS;
    var is_valid, is_fresh, dist_wgpidxs : bool;
    var adlO, adlOC : adrs list;
    var nrqs : int;
        
    (i, m', sig') <@ A.forge(ps);
    
    (ad, m, pk, sig) <@ O_R_DistRCH_Game23WOTSTW.get(i);
    
    is_valid <@ WOTS_TW_ES.verify((pk, ps, ad), m', sig');

    is_fresh <- m' <> m;
    
    nrqs <@ O_R_DistRCH_Game23WOTSTW.nr_queries();
    
    dist_wgpidxs <@ O_R_DistRCH_Game23WOTSTW.dist_addresses();
       
    adlO <@ O_R_DistRCH_Game23WOTSTW.get_addresses();
        
    adlOC <@ O_R_DistRCH_Game23WOTSTW_THFC.get_tweaks();  
    
    return 0 <= nrqs <= d /\ 0 <= i < nrqs /\ 
           is_valid /\ is_fresh /\ dist_wgpidxs /\ disj_wgpidxs adlO adlOC;
  }
}.

(* 
  Reduction adversary that reduces from SM_DT_UD_C to distinguishing between 
  the relevant distributions (using the above-defined reduction adversary that
  reduces distinguishing between the relevant distributions to distinguishing
  between Game2_WOTSTW and Game3_WOTSTW)
*)
local module (R_SMDTUDC_DistRCH : Adv_SMDTUDC) (O : Oracle_SMDTUD, OC : Oracle_THFC) = {
  module O_R_SMDTUDC_DistRCH : Oracle_DistRCH = {
    include var O_DistRCH [-query]
    var i : int
    
    proc query(wad : wadrs, m : msgWOTS) : dgstblock list = {
      var ad : adrs;
      var em : emsgWOTS;
      var chal, chal' : dgstblock list;
      var em_ele : int;
      var chal_ele, chal_ele' : dgstblock;
      var j : int;
      
      ad <- val wad;
      
      em <- encode_msgWOTS m;
      
      chal' <- [];
      while (size chal' < len) {
        em_ele <- BaseW.val em.[size chal'];
        
        if (i < em_ele - 1) {
          chal_ele' <@ O.query(set_hidx (set_chidx ad (size chal')) i);
        } else {
          chal_ele' <$ ddgstblock;
        } 
         
        chal' <- rcons chal' chal_ele';
      }
      
      chal <- [];
      while (size chal < len) {
        em_ele <- BaseW.val em.[size chal];
        
        if (i < em_ele - 1) {
          chal_ele <- nth witness chal' (size chal);
          
          j <- 1;
          while (j < em_ele - 1 - i) {
            chal_ele <@ OC.query(set_hidx (set_chidx ad (size chal)) (i + j), val chal_ele);
            j <- j + 1;
          }
        } else {
          chal_ele <- nth witness chal' (size chal);
        }
        
        chal <- rcons chal chal_ele;
      }
      
      return chal;
    }
  }
  
  module R = R_DistRCH_Game23WOTSTW(O_R_SMDTUDC_DistRCH, OC)
  
  proc pick() : unit = {
    O_R_SMDTUDC_DistRCH.i <$ [0..(w - 3)];
    O_R_SMDTUDC_DistRCH.init(witness, witness);
    
    R.choose();
  }
  
  proc distinguish(ps : pseed) : bool = {
    var b' : bool;
    
    b' <@ R.distinguish(ps);
    
    return b';
  }
}.

(* 
  Auxiliary implementation of reduction adversary R_SMDTUDC_DistRCH, used to obtain the desired
  form for the proof of the SM_DT_UD_C reduction
*)
local module R_SMDTUDC_DistRCHil = {
  module O_R_SMDTUDC_DistRCHil : Oracle_DistRCH = {
    include var O_DistRCH [-query]
    var i : int

    proc query(wad : wadrs, m : msgWOTS) : dgstblock list = {
      var ad : adrs;
      var em : emsgWOTS;
      var chal, chal' : dgstblock list;
      var em_ele : int;
      var chal_ele, chal_ele' : dgstblock;
      var j : int;
      
      ad <- val wad;
      
      em <- encode_msgWOTS m;
      
      chal' <- [];
      while (size chal' < len) {
        em_ele <- BaseW.val em.[size chal'];
        
        if (i < em_ele - 1) {
          chal_ele' <@ O_SMDTUD_Default.query(set_hidx (set_chidx ad (size chal')) i);
        } else {
          chal_ele' <$ ddgstblock;
        } 
         
        chal' <- rcons chal' chal_ele';
      }
      
      chal <- [];
      while (size chal < len) {
        em_ele <- BaseW.val em.[size chal];
        
        if (i < em_ele - 1) {
          chal_ele <- nth witness chal' (size chal);
          
          j <- 1;
          while (j < em_ele - 1 - i) {
            chal_ele <@ O_THFC_Default.query(set_hidx (set_chidx ad (size chal)) (i + j), val chal_ele);
            j <- j + 1;
          }
        } else {
          chal_ele <- nth witness chal' (size chal);
        }
        
        chal <- rcons chal chal_ele;
      }
      
      return chal;
    }
  }
  
  module R = R_DistRCH_Game23WOTSTW(O_R_SMDTUDC_DistRCHil, O_THFC_Default)
  
  proc pick(i : int) = {
    O_R_SMDTUDC_DistRCHil.i <- i;
    O_R_SMDTUDC_DistRCHil.init(witness, witness);
    
    R.choose();
  }
  
  proc distinguish(ps : pseed) : bool = {
    var b' : bool;

    b' <@ R.distinguish(ps);
    
    return b';
  }
}.


(* - (Auxiliary) Games - *)
(*
  Game in which the adversary is tasked with distinguishing between random values
  and elements from WOTS chains selected based on an adversarially chosen message.
*)
local module DistRCH = {
  module R = R_DistRCH_Game23WOTSTW(O_DistRCH, O_THFC_Default)

  proc main(b : bool) = {
    var ps : pseed;
    var b' : bool;

    ps <$ dpseed;

    O_DistRCH.init(b, ps);
    O_THFC_Default.init(ps);

    R.choose();

    b' <@ R.distinguish(ps);

    return b';
  }
}.

(* 
  Auxiliary implementations for DistRCH, used to obtain the desired form
  for the proof of the SM_DT_UD_C reduction 
*)
local module DistRCHi = {
  module O_DistRCHi : Oracle_DistRCH = {
    include var O_DistRCH [-query]
    var i : int
    
    proc query(wad : wadrs, m : msgWOTS) : dgstblock list = {
      var ad : adrs;
      var em : emsgWOTS;
      var chal, chal' : dgstblock list;
      var em_ele : int;
      var chal_ele, chal_ele' : dgstblock;

      ad <- val wad;
      
      chal' <$ ddgstblockl;
      
      em <- encode_msgWOTS m;
      chal <- [];
      while (size chal < len){
        chal_ele' <- nth witness chal' (size chal);
        em_ele <- BaseW.val em.[size chal];
        chal_ele <- cf ps (set_chidx ad (size chal)) i (em_ele - 1 - i) (val chal_ele');
        chal <- rcons chal chal_ele;
      }
      
      return chal;
    }
  }
  
  module R = R_DistRCH_Game23WOTSTW(O_DistRCHi, O_THFC_Default)

  proc main(i : int) : bool = {
    var ps : pseed;
    var b' : bool;

    ps <$ dpseed;
    O_DistRCHi.i <- i;
    O_DistRCHi.init(witness, ps);
    O_THFC_Default.init(ps);
    R.choose();
    b' <@ R.distinguish(ps);

    return b';
  }
}.

local module DistRCHi_SampleSample = {
  module O_DistRCHi : Oracle_DistRCH = {
    include var O_DistRCH [-query]
    var i : int
    
    proc query(wad : wadrs, m : msgWOTS) : dgstblock list = {
      var ad : adrs;
      var em : emsgWOTS;
      var chal, chal' : dgstblock list;
      var em_ele : int;
      var chal_ele, chal_ele' : dgstblock;

      ad <- val wad;
      
      chal' <@ Sample.sample(len);
      
      em <- encode_msgWOTS m;
      chal <- [];
      while (size chal < len){
        chal_ele' <- nth witness chal' (size chal);
        em_ele <- BaseW.val em.[size chal];
        chal_ele <- cf ps (set_chidx ad (size chal)) i (em_ele - 1 - i) (val chal_ele');
        chal <- rcons chal chal_ele;
      }
      
      return chal;
    }
  }
  
  module R = R_DistRCH_Game23WOTSTW(O_DistRCHi, O_THFC_Default)

  proc main(i : int) : bool = {
    var ps : pseed;
    var b' : bool;

    ps <$ dpseed;
    O_DistRCHi.i <- i;
    O_DistRCHi.init(witness, ps);
    O_THFC_Default.init(ps);
    R.choose();
    b' <@ R.distinguish(ps);

    return b';
  }
}.

local module DistRCHi_LoopSnocSample = {
  module O_DistRCHi : Oracle_DistRCH = {
    include var O_DistRCH [-query]
    var i : int
    
    proc query(wad : wadrs, m : msgWOTS) : dgstblock list = {
      var ad : adrs;
      var em : emsgWOTS;
      var chal, chal' : dgstblock list;
      var em_ele : int;
      var chal_ele, chal_ele' : dgstblock;

      ad <- val wad;
      
      chal' <@ LoopSnoc.sample(len);
      
      em <- encode_msgWOTS m;
      chal <- [];
      while (size chal < len){
        chal_ele' <- nth witness chal' (size chal);
        em_ele <- BaseW.val em.[size chal];
        chal_ele <- cf ps (set_chidx ad (size chal)) i (em_ele - 1 - i) (val chal_ele');
        chal <- rcons chal chal_ele;
      }
      
      return chal;
    }
  }
  
  module R = R_DistRCH_Game23WOTSTW(O_DistRCHi, O_THFC_Default)

  proc main(i : int) : bool = {
    var ps : pseed;
    var b' : bool;

    ps <$ dpseed;
    O_DistRCHi.i <- i;
    O_DistRCHi.init(witness, ps);
    O_THFC_Default.init(ps);
    R.choose();
    b' <@ R.distinguish(ps);

    return b';
  }
}.

local module DistRCHil = {
  module O_DistRCHi : Oracle_DistRCH = {
    include var O_DistRCH [-query]
    var i : int
    
    proc query(wad : wadrs, m : msgWOTS) : dgstblock list = {
      var ad : adrs;
      var em : emsgWOTS;
      var chal, chal' : dgstblock list;
      var em_ele : int;
      var chal_ele, chal_ele' : dgstblock;

      ad <- val wad;
      
      chal' <- [];
      while (size chal' < len) {
        chal_ele' <$ ddgstblock;
        chal' <- rcons chal' chal_ele';
      }
      
      em <- encode_msgWOTS m;
      chal <- [];
      while (size chal < len){
        chal_ele' <- nth witness chal' (size chal);
        em_ele <- BaseW.val em.[size chal];
        chal_ele <- cf ps (set_chidx ad (size chal)) i (em_ele - 1 - i) (val chal_ele');
        chal <- rcons chal chal_ele;
      }
      
      return chal;
    }
  }
  
  module R = R_DistRCH_Game23WOTSTW(O_DistRCHi, O_THFC_Default)

  proc main(i : int) : bool = {
    var ps : pseed;
    var b' : bool;

    ps <$ dpseed;
    O_DistRCHi.i <- i;
    O_DistRCHi.init(witness, ps);
    O_THFC_Default.init(ps);
    R.choose();
    b' <@ R.distinguish(ps);

    return b';
  }
}.

(* 
  Equivalences between auxiliary implementations of DistRCHi 
  (Desired equivalence betweeen DistRCH and DistRCHi is proved in 
  in proof of reduction for SM_DT_UD_C)  
*)
local equiv DistRCHi_Orig_SampleSample : 
  DistRCHi.main ~ DistRCHi_SampleSample.main : 
    ={glob A, i} ==> ={res}.
proof.
proc; inline *.
seq 18 18 : (={glob A, glob O_MEUFGCMA_WOTSTWES, R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl, ps}); last by sim.
call (:   ={glob O_THFC_Default, glob O_MEUFGCMA_WOTSTWES, glob O_DistRCH, R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl} 
       /\ DistRCHi.O_DistRCHi.i{1} = DistRCHi_SampleSample.O_DistRCHi.i{2}) => //=.
+ proc; inline *.
  by sim; rnd; wp; skip.
+ by sim. 
by wp; rnd; skip.
qed.

local equiv DistRCHi_SampleSample_LoopSnocSample : 
  DistRCHi_SampleSample.main ~ DistRCHi_LoopSnocSample.main : 
    ={glob A, i} ==> ={ res}.
proof.
proc; inline *.
seq 18 18 : (={glob A, glob O_MEUFGCMA_WOTSTWES, R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl, ps}); last by sim.
call (:   ={glob O_THFC_Default, glob O_MEUFGCMA_WOTSTWES, glob O_DistRCH, R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl} 
       /\ DistRCHi_SampleSample.O_DistRCHi.i{1} = DistRCHi_LoopSnocSample.O_DistRCHi.i{2}) => //=.
+ proc.
  inline{1} 2; inline{2} 2.
  seq 5 5 : (#pre /\ ={ad, ad0, m0, chal'}) => /=.
  - by call Sample_LoopSnoc_eq; wp; skip.
  by sim.
+ by sim. 
by wp; rnd; skip.
qed.

local equiv DistRCHi_LoopSnocSample_Alt : 
  DistRCHi_LoopSnocSample.main ~ DistRCHil.main : 
    ={glob A, i} ==> ={ res}.
proof.
proc; inline *.
seq 18 18 : (={glob A, glob O_MEUFGCMA_WOTSTWES, R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl, ps}); last by sim.
call (:   ={glob O_THFC_Default, glob O_MEUFGCMA_WOTSTWES, glob O_DistRCH, R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl} 
       /\ DistRCHi_LoopSnocSample.O_DistRCHi.i{1} = DistRCHil.O_DistRCHi.i{2}) => //=.
+ proc.
  inline{1} 2; inline{1} 5; inline{2} 2.
  seq 9 6 : (#pre /\ = {ad, ad0, m0, chal'}).
  - wp.
    while (   n{1} = len
           /\ i{1} = size chal'{2}
           /\ l{1} = chal'{2}).
    * by wp; rnd; skip => |>; smt(size_rcons cats1). 
    by wp; skip.
  by sim. 
+ by sim.
by wp; rnd; skip.
qed.

local equiv DistRCHi_Orig_Alt : 
  DistRCHi.main ~ DistRCHil.main : 
    ={glob A, i} ==> ={res}.
proof.
transitivity DistRCHi_SampleSample.main 
             (={glob A, i} ==> ={res}) 
             (={glob A, i} ==> ={res}) => [/# | // | |].
+ by apply DistRCHi_Orig_SampleSample.
transitivity DistRCHi_LoopSnocSample.main 
             (={glob A, i} ==> ={res}) 
             (={glob A, i} ==> ={res}) => [/# | // | |].
+ by apply DistRCHi_SampleSample_LoopSnocSample.
by apply DistRCHi_LoopSnocSample_Alt.
qed.


(* - (Auxiliary) Security Notions - *)
(*
  Specific, auxiliary instantiations/variations of the SM_DT_UD_C notion, used to obtain 
  the desired form for the proof of the SM_DT_UD_C reduction
*)
local module SM_DT_UD_Ci = {
  proc main(i : int, b : bool) = {
    var pp : pseed;
    var tw : adrs;
    var x : dgst;
    var b' : bool;
    var nrts : int;
    var dist : bool;
    var twsO, twsOC : adrs list;    
    
    pp <$ dpseed;
    O_THFC_Default.init(pp);
    O_SMDTUD_Default.init(b, pp);
    
    R_SMDTUDC_DistRCHil.pick(i);
    
    b' <@ R_SMDTUDC_DistRCHil.distinguish(pp);    
    
    nrts <@ O_SMDTUD_Default.nr_targets();
    dist <@ O_SMDTUD_Default.dist_tweaks();
    twsO <@ O_SMDTUD_Default.get_tweaks();
    twsOC <@ O_THFC_Default.get_tweaks();
    
    return 0 <= nrts <= d * len /\ dist /\ b' /\ disj_lists twsO twsOC;
  }
}.

local module SM_DT_UD_Cir = {
  proc main(b : bool) = {
    var i : int;
    var b' : bool;
    
    i <$ [0..w - 3];    
    b' <@ SM_DT_UD_Ci.main(i, b);
    
    return (i, b');
  }
}.


(* - Game-playing proof - *)
(* Zeroeth step: Show equivalence between M_EUF_GCMA_WOTSTWES and Game0_WOTSTWES *)
local equiv MEUFGCMA_Game0_WOTSTWES :
  M_EUF_GCMA_WOTSTWES(A, O_MEUFGCMA_WOTSTWES, O_THFC_Default).main ~ Game0_WOTSTWES.main : 
    ={glob A} ==> ={res}.
proof.
proc; inline *.
seq 11 11 : (={glob A, O_MEUFGCMA_WOTSTWES.qs, O_THFC_Default.tws, ps}); last by sim.
call (: ={glob O_MEUFGCMA_WOTSTWES, glob O_THFC_Default}); [|by proc; inline *; sim | by auto]. 
proc; inline *.
wp => /=.
while (   ={glob O_MEUFGCMA_WOTSTWES, em}
       /\ ad0{1} = ad{2}
       /\ sig0{1} = sig{2} 
       /\ size sig0{1} <= len 
       /\ size sig{2} <= len
       /\ skWOTS0{1} = insubd sk{2}
       /\ size sk{2} = len
       /\ ps0{1} = O_MEUFGCMA_WOTSTWES.ps{1}).
+ by wp; skip => |> &1 lelen_szsig ltlen_szsig; smt(size_rcons DBLL.insubdK).
wp => /=.
while{1} (   0 <= size skWOTS3{1} <= len
          /\ (forall i, 0 <= i < len => 
                nth witness skWOTS1{1} i = prf_sk ss2{1} (ps3{1}, (set_hidx (set_chidx ad3{1} i) 0)))
          /\ (forall i, 0 <= i < size skWOTS3{1} => nth witness skWOTS3{1} i = nth witness skWOTS1{1} i))
         (len - size skWOTS3{1}).
+ move => _ z.
  by wp; skip => |> *; smt(size_rcons nth_rcons).
wp => /=.
while (   ={glob O_MEUFGCMA_WOTSTWES}
       /\ pkWOTS0{1} = pk{2} 
       /\ size pkWOTS0{1} <= len 
       /\ size pk{2} <= len
       /\ size sk{2} = len
       /\ skWOTS2{1} = insubd sk{2}
       /\ ps2{1} = O_MEUFGCMA_WOTSTWES.ps{1}
       /\ ad2{1} = ad{2}).
+ by wp; skip => |> &1 lelen_szpk ltlen_szpk; smt(size_rcons DBLL.insubdK).
wp => /=.
while (   ={glob O_MEUFGCMA_WOTSTWES}
       /\ 0 <= size skWOTS1{1} <= len
       /\ ss1{1} = O_MEUFGCMA_WOTSTWES.ss{2}
       /\ ps1{1} = O_MEUFGCMA_WOTSTWES.ps{1}
       /\ skWOTS1{1} = sk{2}
       /\ ad1{1} = ad{2}
       /\ (forall i, 0 <= i < size skWOTS1{1} =>
             nth witness skWOTS1{1} i = prf_sk ss1{1} (ps1{1}, (set_hidx (set_chidx ad1{1} i) 0)))).
+ by wp; skip => |>; smt(nth_rcons size_rcons).
wp; skip => |> &1. 
split => [| *]; [by smt(ge2_len) | split => [| *]; first by smt(ge2_len)].
split => [| *]; [by smt(ge2_len) | split => [/# | *]; rewrite andbA; split; first by smt(ge2_len)].
by congr; apply (eq_from_nth witness) => /#.
qed.

(* First step: Reduce PRF of prf_sk to distinguishing between Game0_WOTSTWES and- M_EUF_GCMA_WOTSTWES without PRF *)
local lemma Step_Game0_MEUFGCMA_WOTSTWES_NOPRF_PRF &m :
  `|Pr[Game0_WOTSTWES.main() @ &m : res] - Pr[M_EUF_GCMA_WOTSTWES(A, O_MEUFGCMA_WOTSTWES_NOPRF, O_THFC_Default).main() @ &m : res]|
  =
  `|Pr[PRF(R_PRF_Game0NOPRFWOTSTWES(A), O_PRF_Default).main(false) @ &m : res] - Pr[PRF(R_PRF_Game0NOPRFWOTSTWES(A), O_PRF_Default).main(true) @ &m : res]|.
proof.
do 2! congr; last congr.
+ byequiv => //=.
  proc; inline *.
  wp => /=.
  seq 11 14 : (={glob A, O_MEUFGCMA_WOTSTWES.qs, O_THFC_Default.tws, ps}); last by sim.
  call (:   ={glob O_THFC_Default, O_MEUFGCMA_WOTSTWES.ps, O_MEUFGCMA_WOTSTWES.qs} 
         /\ O_PRF_Default.b{2} = false
         /\ O_MEUFGCMA_WOTSTWES.ss{1} = O_PRF_Default.k{2}); conseq => |>.
  - proc. 
    inline O_PRF_Default.query.
    seq 3 3 : (={O_MEUFGCMA_WOTSTWES.ps, O_MEUFGCMA_WOTSTWES.qs, ad, m, sk}); last by sim.
    while (   #post 
           /\ O_PRF_Default.b{2} = false
           /\ O_MEUFGCMA_WOTSTWES.ss{1} = O_PRF_Default.k{2}); last by auto.
    rcondf{2} 2; first by auto.     
    by wp; skip.
  - by sim. 
  by wp; rnd; wp; rnd; wp; skip.
byequiv => //=.
transitivity M_EUF_GCMA_WOTSTWES(A, O_MEUFGCMA_WOTSTWES_NOPRF_Alt, O_THFC_Default).main
             (={glob A} ==> ={res})
             (arg{2} = true /\ ={glob A} ==> ={res}) => [/# | // | |].             
+ proc.
  seq 5 5 : (={glob A, O_MEUFGCMA_WOTSTWES.qs, O_THFC_Default.tws, ps}); last by sim.
  call (: ={O_MEUFGCMA_WOTSTWES.ps, O_MEUFGCMA_WOTSTWES.qs, O_THFC_Default.pp, O_THFC_Default.tws}) => |>.
  - conseq (: ={O_MEUFGCMA_WOTSTWES.ps, O_MEUFGCMA_WOTSTWES.qs, wad, m} 
              ==> 
              ={O_MEUFGCMA_WOTSTWES.ps, O_MEUFGCMA_WOTSTWES.qs, res}) => //.
    * by apply O_MEUFGCMA_WOTSTWES_NOPRF_Orig_Alt.  
  - by proc; sim.
  by inline *; wp; do 2! rnd; skip.
proc.
inline{2} 2.
wp 13 13 => /=.
conseq (: _ 
          ==>
             ={dist_wgpidxs} 
          /\ (dist_wgpidxs{2}
             =>
             (   (0 <= nrqs{1} <= d /\ 0 <= i{1} < nrqs{1}
              /\ is_valid{1} /\ is_fresh{1} /\ disj_wgpidxs adlO{1} adlOC{1})
              =
                 (0 <= nrqs{2} <= d /\ 0 <= i{2} < nrqs{2}
              /\ is_valid{2} /\ is_fresh{2} /\ disj_wgpidxs adlO{2} adlOC{2})))) => [/#|].
inline{1} 13; inline{1} 12; inline{1} 11; inline{1} 10; inline{1} 7.
inline{2} 13; inline{2} 12; inline{2} 11; inline{2} 10; inline{2} 7.
seq 5 5 : ((uniq_wgpidxs (map (fun (q : _ * _ * _ *_) => q.`1) O_MEUFGCMA_WOTSTWES.qs{1})
           =
           uniq_wgpidxs (map (fun (q : _ * _ * _ *_) => q.`1) O_MEUFGCMA_WOTSTWES.qs{2}))
           /\
           (uniq_wgpidxs (map (fun (q : _ * _ * _ *_) => q.`1) O_MEUFGCMA_WOTSTWES.qs{2})
            =>
            ={glob A, O_MEUFGCMA_WOTSTWES.qs, O_THFC_Default.tws, ps})).
+ call (: (! (uniq_wgpidxs (map (fun (q : _ * _ * _ *_) => q.`1) O_MEUFGCMA_WOTSTWES.qs))),
              ={glob O_THFC_Default, O_MEUFGCMA_WOTSTWES.ps, O_MEUFGCMA_WOTSTWES.qs}
           /\ O_PRF_Default.b{2} = true
           /\ O_MEUFGCMA_WOTSTWES.ss{1} = O_PRF_Default.k{2}
           /\ all valid_wadrs (map (fun (q : _ * _ * _ * _) => q.`1) O_MEUFGCMA_WOTSTWES.qs{1})
           /\ (forall (ad : adrs), 
                 (get_wgpidxs ad \in (map (fun (q : _ * _ * _ *_) => get_wgpidxs q.`1) O_MEUFGCMA_WOTSTWES.qs{2})) 
                 =>
                 (exists (ad' : adrs), (O_MEUFGCMA_WOTSTWES.ps{2}, ad') \in O_PRF_Default.m{2} /\ get_wgpidxs ad = get_wgpidxs ad'))
            /\ (forall (ad : adrs), 
                 (O_MEUFGCMA_WOTSTWES.ps{2}, ad) \in O_PRF_Default.m{2}
                 =>
                 (get_wgpidxs ad \in (map (fun (q : _ * _ * _ *_) => get_wgpidxs q.`1) O_MEUFGCMA_WOTSTWES.qs{2}))),
           (uniq_wgpidxs (map (fun (q : _ * _ * _ *_) => q.`1) O_MEUFGCMA_WOTSTWES.qs{1})
            =
            uniq_wgpidxs (map (fun (q : _ * _ * _ *_) => q.`1) O_MEUFGCMA_WOTSTWES.qs{2}))) => //=.
  - move=> O OC; apply (A_choose_ll O OC).
  - proc.
    sp 1 1; wp => /=.
    case (get_wgpidxs ad{2} \in map (fun (q : _ * _ * _ *_) => get_wgpidxs q.`1) O_MEUFGCMA_WOTSTWES.qs{2}).
    * conseq (: _ ==> true) => |>. 
      + move=> &2 uqpfqs qsch relqsm relmqs pfadin pk sig m pk' csig'.
        split => [nuqpfrcqs |]. 
        - apply negbTE => @/uniq_wgpidxs.
          rewrite -map_comp /(\o) map_rcons /= rcons_uniq negb_and /=.
          left; move/mapP: pfadin => [q] [qin /= ->].
          by rewrite mapP; exists q.
        pose uqpfrcqs := uniq_wgpidxs _; have //: ! uqpfrcqs. 
        rewrite /uqpfrcqs /uniq_wgpidxs.
        rewrite -map_comp /(\o) map_rcons /= rcons_uniq negb_and /=.
        left; move/mapP: pfadin => [q] [qin /= ->].
        by rewrite mapP; exists q.
      while (size sig{1} = size sig{2}); first by auto; smt(size_rcons).
      wp. 
      while (size pk{1} = size pk{2}); first by auto; smt(size_rcons).
      wp. 
      while (size sk{1} = size sk{2} /\ O_PRF_Default.b{2} = true).
      + inline{2} 1.
        rcondt{2} 2; first by auto.
        wp; sp => /=. 
        conseq (: _ ==> true); first by smt(size_rcons).
        by sp; if{2}; auto. 
      by wp; skip. 
    while (={ad, sk, sig, em, O_MEUFGCMA_WOTSTWES.ps} /\ size sk{1} = len /\ 0 <= size sig{1} <= len).
    * wp; skip => |>; smt(size_rcons).
    wp.
    while (={ad, pk, sk, O_MEUFGCMA_WOTSTWES.ps} /\ size sk{1} = len /\ 0 <= size pk{1} <= len).
    * wp; skip => |>; smt(size_rcons).
    wp => /=.
    exists* O_PRF_Default.m{2}; elim* => m.
    while (   ={ad, sk}
           /\ valid_wadrs ad{2}
           /\ O_PRF_Default.b{2} = true
           /\ ! (get_wgpidxs ad{2} \in map (fun (q : adrs * msgWOTS * pkWOTS * sigWOTS) => get_wgpidxs q.`1) O_MEUFGCMA_WOTSTWES.qs{2})
           /\ (forall (ad' : adrs), 
                 (get_wgpidxs ad' \in (map (fun (q : _ * _ * _ *_) => get_wgpidxs q.`1) O_MEUFGCMA_WOTSTWES.qs{2})) 
                 =>
                 (exists (ad'' : adrs), (O_MEUFGCMA_WOTSTWES.ps{2}, ad'') \in m /\ get_wgpidxs ad' = get_wgpidxs ad''))
           /\ (forall (ad' : adrs),
                 (O_MEUFGCMA_WOTSTWES.ps{2}, ad') \in m 
                 =>
                 (get_wgpidxs ad' \in (map (fun (q : _ * _ * _ *_) => get_wgpidxs q.`1) O_MEUFGCMA_WOTSTWES.qs{2})))
           /\ (forall (ad' : adrs), 
                 (O_MEUFGCMA_WOTSTWES.ps{2}, ad') \in O_PRF_Default.m{2} 
                 <=> 
                 (((O_MEUFGCMA_WOTSTWES.ps{2}, ad') \in m) \/ (ad' \in mkseq (fun (i : int) => set_hidx (set_chidx ad{2} i) 0) (size sk{2}))))
           /\ 0 <= size sk{2} <= len).
    * inline *.
      rcondt{2} 2; first by auto.
      rcondt{2} 2.
      + auto => |> &1 adch npfadin relqsm relmqs relmm ge0_szsk _ ltlen_szsk.
        move/iffLR: (relmm (set_hidx (set_chidx ad{m0} (size sk{m0})) 0)) => /contra; apply.
        rewrite negb_or; split.
        - move: (relmqs (set_hidx (set_chidx ad{m0} (size sk{m0})) 0)) => /contra /(_ _) //.
          pose gpfss := get_wgpidxs _; have -> //: gpfss = get_wgpidxs ad{m0}; rewrite /gpfss.
          by rewrite eq_gp_setchhidx // /#.
        rewrite mapP negb_exists => i /=; rewrite negb_and -implybE mem_iota /= => rng_i.
        by apply neq_after_setchhidx => //; smt(val_w).
      wp; rnd; wp; skip => |> &2 adch npfadin relqsm relmqs relmm ge0_szsk _ ltlen_szsk skele skelein.
      rewrite !andbA -3!andbA; split; last by smt(size_rcons).  
      split => [| ad']; first by rewrite get_set_sameE oget_some.
      rewrite mem_set; split => -[].
      + by rewrite size_rcons mkseqS //= mem_rcons /= => /relmm [] ->.
      + by move=> [_ ->]; right; rewrite size_rcons mkseqS //= mem_rcons.
      + by rewrite relmm => ->.
      rewrite size_rcons mkseqS //= mem_rcons /= => -[-> // |].
      by rewrite relmm => ->.
    wp; skip => |> &2 uqpf qsch relqsm relmqs npfadin. 
    split; first by smt(mkseq0 ge2_len WAddress.valP).
    move=> mr skr /lezNgt gelen_szsk _  _ relmrm ge0_szskr lelen_szskr. 
    split => [| pkr /lezNgt gelen_szpkr _  eqln_szskr ge0_szpkr lelen_szpkr]; first by smt(ge2_len).
    split => [| sigr /lezNgt gelen_szsigr _  ge0_szsigr lelen_szsigr uqpfrc]; first by smt(ge2_len).
    split; first by rewrite map_rcons -cats1 all_cat /= qsch WAddress.valP.
    split => [ad' pfadpin | ad' adpin]. 
    * move/mapP: pfadpin => [q] [] /= + ->; rewrite mem_rcons /= => -[-> /= | qin].
      + exists (set_hidx (set_chidx (WAddress.val wad{2}) 0) 0) => //=.
        split; first by rewrite relmrm mapP; right; exists 0 => //=; smt(mem_iota ge2_len).
        by rewrite eq_sym eq_gp_setchhidx //=; smt(ge2_len val_w WAddress.valP).
      move: (relqsm q.`1 _); first by rewrite mapP; exists q.
      by move=> [ad''] [adppin ->]; exists ad''; rewrite relmrm adppin.
    rewrite map_rcons mem_rcons; case (get_wgpidxs ad' = get_wgpidxs (WAddress.val wad{2})) => [-> //| neqgpf /=].
    rewrite neqgpf /= (relmqs ad'); move/relmrm: adpin => [-> // |].
    apply contraLR => _; rewrite mapP negb_exists => i /=; rewrite negb_and -implybE => /mem_iota /= rng_i.
    by move: (eq_gp_setchhidx (WAddress.val wad{2}) i 0 _ _ _) neqgpf => //=; smt(ge2_len val_w WAddress.valP).
  - move=> &2 @/uniq_wgpidxs nuqpfqs.
    proc.
    wp => /=.
    conseq (: _ ==> true). 
    * move=> &1 [#] equqpfqs adch pk' sig' /=.
      by rewrite nuqpfqs /uniq_wgpidxs 2!map_rcons rcons_uniq /= equqpfqs nuqpfqs.
    while (0 <= size sig <= len) (len - size sig); first by auto; smt(size_rcons). 
    wp.
    while (0 <= size pk <= len) (len - size pk); first by auto; smt(size_rcons).
    wp.
    while (0 <= size sk <= len) (len - size sk); first auto; smt(size_rcons ddgstblock_ll).
    by wp; skip => |>; smt(ge2_len).
  - move=> &1.
    proc.
    wp => /=.
    conseq (: _ ==> true).
    * move => &2 [#] @/uniq_wgpidxs nuqpfqs equqpfqs adch pk' sig' /=.
      by rewrite 2!map_rcons /= rcons_uniq negb_and /= equqpfqs nuqpfqs.
    while (0 <= size sig <= len) (len - size sig); first by auto; smt(size_rcons). 
    wp.
    while (0 <= size pk <= len) (len - size pk); first by auto; smt(size_rcons).
    wp.
    while (0 <= size sk <= len) (len - size sk); first auto; inline *; wp; sp => /=.
    * by if; [if |]; auto => |>; smt(size_rcons ddgstblock_ll).
    by wp; skip => |>; smt(ge2_len).
  - by proc; wp; skip.
  - move=> &2 nuqpfqs.
    by proc; wp; skip. 
  - move=> &1.
    by proc; wp; skip.
  by inline *; wp; rnd; wp; rnd; wp; skip => |>; smt(mem_empty ge2_len).
case (uniq_wgpidxs (map (fun (q : _ * _ * _ *_) => q.`1) O_MEUFGCMA_WOTSTWES.qs{2})).
+ sim => |> /#. 
wp => /=; conseq (: _ ==> true) => |>.
inline *.
wp.
while (size pkWOTS1{1} = size pkWOTS0{2} /\ 0 <= size pkWOTS1{1} <= len).
+ by auto; smt(size_rcons). 
wp => /=.
call{1} (: true ==> true); 2: call{2} (: true ==> true); first 2 proc true => //.
+ by move=> O OC; apply (A_forge_ll O OC).
+ by move=> O OC; apply (A_forge_ll O OC).
by skip; smt(ge2_len).
qed.

(* Second step: Show equivalence between M_EUF_GCMA_WOTSTWES without PRF and Game2_WOTSTWES *)
local equiv MEUFGCMA_WOTSTWES_NOPRF_Game2_WOTSTWES : 
  M_EUF_GCMA_WOTSTWES(A, O_MEUFGCMA_WOTSTWES_NOPRF, O_THFC_Default).main ~ Game2_WOTSTWES.main : 
    ={glob A} ==> ={res}.
proof.
proc; inline *.
seq 12 12 : (={glob O_MEUFGCMA_WOTSTWES, glob O_THFC_Default, ps, i, m', sig'}); last by sim.
do 2! call (: ={glob O_MEUFGCMA_WOTSTWES, glob O_THFC_Default}); [|by proc; inline *; sim | by auto].
proc.
wp; swap{1} [5..6] -2; swap{2} 6 -1.
seq 5 5 : (    #pre 
           /\ ={ad, sk, em, sig, pk}
           /\ valid_wadrs ad{1}
           /\ sig{1} = []
           /\ pk{1} = []).
+ by auto => |>; rewrite WAddress.valP.
while{1} (   valid_wadrs ad{1}
          /\ (forall (i : int), 0 <= i < size sig => 
               nth witness sig i 
               = 
               cf O_MEUFGCMA_WOTSTWES.ps (set_chidx ad i) 0 (BaseW.val em.[i]) (val (nth witness sk i))){1}
          /\ size sig{1} <= len)
         (len - size sig{1}).
+ move=> _ z.
  wp; skip => |> &m adch valsigele leln_szsig ltlen_szsig.
  split; 1: split => [i ge0_i|]; last 2 by smt(size_rcons). 
  rewrite size_rcons nth_rcons => ltsz1_i.
  case (i < size sig{m}) => ltsz_i; first by rewrite (valsigele i).
  by rewrite (: i = size sig{m}) 1:/#.
while{1} (   valid_wadrs ad{1}
          /\ (forall (i : int), 0 <= i < size pk => 
                nth witness pk i
                = 
                cf O_MEUFGCMA_WOTSTWES.ps (set_chidx ad i) 0 (w - 1) (val (nth witness sk i))){1}
          /\ size pk{1} <= len)
         (len - size pk{1}).
+ move=> _ z.
  wp; skip => |> &m adch valpkele leln_szpk ltlen_szspk.
  split; 1: split => [i ge0_i|]; last 2 by smt(size_rcons). 
  rewrite size_rcons nth_rcons => ltsz1_i.
  case (i < size pk{m}) => ltsz_i; first by rewrite (valpkele i).
  by rewrite (: i = size pk{m}) 1:/#.
while{2} (    valid_wadrs ad{2}
          /\ (forall (i : int), 0 <= i < size pk => 
                nth witness pk i 
                =
                cf O_MEUFGCMA_WOTSTWES.ps (set_chidx ad i) 0 (w - 1) (val (nth witness sk i))){2}
          /\ size pk{2} <= len)
         (len - size pk{2}).
+ move=> _ z.
  wp; skip => |> &m adch valpkele leln_szpk ltlen_szspk.
  split; 1: split => [i ge0_i|]; last 2 by smt(size_rcons). 
  rewrite size_rcons nth_rcons => ltsz1_i.
  case (i < size pk{m}) => ltsz_i; first by rewrite (valpkele i).
  by rewrite (: i = size pk{m}) 1:/#.
while{2} (   valid_wadrs ad{2}
          /\ (forall (i : int), 0 <= i < size sig => 
                nth witness sig i 
                = 
                cf O_MEUFGCMA_WOTSTWES.ps (set_chidx ad i) 0 (BaseW.val em.[i]) (val (nth witness sk i))){2}
          /\ size sig{2} <= len)
         (len - size sig{2}).
+ move=> _ z.
  wp; skip => |> &m adch valsigele leln_szsig ltlen_szsig.
  split; 1: split => [i ge0_i|]; last 2 by smt(size_rcons). 
  rewrite size_rcons nth_rcons => ltsz1_i.
  case (i < size sig{m}) => ltsz_i; first by rewrite (valsigele i).
  by rewrite (: i = size sig{m}) 1:/#.
wp; skip => |> &m adch.
split => [| sig]; first smt(ge2_len).
split => [| /lezNgt gelen_szsig sigdef lelen_szsig]; first by smt(ge2_len).
split => [| pk]; first smt(ge2_len).
split => [| /lezNgt gelen_szpk pkdef lelen_szpk]; first by smt(ge2_len).
split => [| pk']; first smt(ge2_len).
split => [| /lezNgt gelen_szpkp pkpdef lelen_szpkp]; first by smt(ge2_len).
split => [| sig']; first smt(ge2_len).
split => [| /lezNgt gelen_szsigp sigpdef lelen_szsigp]; first by smt(ge2_len).
have eqsz_pk: size pk' = size pk; 2: have eqsz_sig: size sig' = size sig; first 2 by smt().
have -> /=: pk' = pk.
+ apply (eq_from_nth witness) => // i rngi; apply DigestBlock.val_inj.
  by rewrite (pkpdef i rngi); rewrite eqsz_pk in rngi; rewrite (pkdef i rngi).
suff -> //: sig' = sig.
apply (eq_from_nth witness) => // i rngi; apply DigestBlock.val_inj.
rewrite (sigpdef i rngi); rewrite eqsz_sig in rngi; rewrite (sigdef i rngi).
by case (BaseW.val em{m}.[i] = 0) => [-> | neq0_emi]; first by rewrite ?cf0.
qed.

(* Third step: Reduce distinguishing between the relevant distributions to distinguishing between Game2_WOTSTWES and Game3_WOTSTWES *)
local lemma Game2_Game3_WOTSTWES_DistRCH &m :
  `|Pr[Game2_WOTSTWES.main() @ &m : res] - Pr[Game3_WOTSTWES.main() @ &m : res]|
  =
  `|Pr[DistRCH.main(false) @ &m : res] - Pr[DistRCH.main(true) @ &m : res]|.
proof.
do 2! congr; last congr.
+ byequiv => //.
  proc; inline *.
  seq 10 16 : (   ={glob A, glob O_THFC_Default, O_MEUFGCMA_WOTSTWES.qs, ps}
              /\ b{2} = false
              /\ (O_MEUFGCMA_WOTSTWES.ps = ps){1}
              /\ (O_DistRCH.b = b){2}
              /\ (O_DistRCH.ps = ps){2}
              /\ (O_THFC_Default.pp = ps){1}
              /\ (O_THFC_Default.pp = ps){2}
              /\ O_MEUFGCMA_WOTSTWES.qs{1} = []
              /\ O_MEUFGCMA_WOTSTWES.qs{2} = []
              /\ O_THFC_Default.tws{1} = []
              /\ O_THFC_Default.tws{2} = []
              /\ R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl{2} = []).
  - by auto => |>.
  seq 1 1 : (   ={glob A, O_MEUFGCMA_WOTSTWES.qs, ps}
             /\ O_THFC_Default.tws{1} = R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl{2}).
  - call (:   ={O_MEUFGCMA_WOTSTWES.qs, O_THFC_Default.pp} 
           /\ O_DistRCH.b{2} = false
           /\ O_MEUFGCMA_WOTSTWES.ps{1} = O_DistRCH.ps{2}
           /\ O_MEUFGCMA_WOTSTWES.ps{1} = O_THFC_Default.pp{2}
           /\ O_THFC_Default.tws{1} = R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl{2}).
    * proc; inline *.
      rcondf{2} 6; first by auto.
      wp => /=.
      seq 6 12 : (   #pre
                  /\ ={ad, em, pk} 
                  /\ valid_wadrs ad{1}
                  /\ ad0{2} = ad{2} 
                  /\ m0{2} = m{2} 
                  /\ em{1} = em0{2}
                  /\ em0{2} = encode_msgWOTS m{2}
                  /\ sk{1} = chal'{2}
                  /\ sk{1} \in ddgstblockl
                  /\ chal'{2} \in ddgstblockl
                  /\ pk{1} = []
                  /\ pk{2} = []
                  /\ sig{2} = []
                  /\ size sig{1} = len
                  /\ size chal{2} = len
                  /\ (forall (i : int), 0 <= i < len =>
                       nth witness sig{1} i 
                       = 
                       cf O_MEUFGCMA_WOTSTWES.ps{1} (set_chidx ad{1} i) 0 (BaseW.val em{1}.[i]) (val (nth witness sk{1} i)))
                  /\ (forall (i : int), 0 <= i < len => 
                       nth witness chal{2} i
                       = 
                       cf O_DistRCH.ps{2} (set_chidx ad{2} i) 0 (BaseW.val em{2}.[i] - 1) (val (nth witness chal'{2} i)))).
      + wp => /=.
        while (   ={m, ad}
               /\ ad0{2} = ad{2}
               /\ valid_wadrs ad{1}
               /\ sk{1} = chal'{2}
               /\ O_MEUFGCMA_WOTSTWES.ps{1} = O_DistRCH.ps{2}
               /\ O_MEUFGCMA_WOTSTWES.ps{1} = O_THFC_Default.pp{2}
               /\ ad0{2} = ad{2} 
               /\ m0{2} = m{2} 
               /\ em{1} = em0{2}
               /\ 0 <= size sig{1} <= len
               /\ 0 <= size chal0{2} <= len
               /\ size sig{1} = size chal0{2}
               /\ (forall (i : int), 0 <= i < size sig{1} =>
                    nth witness sig{1} i 
                    = 
                    cf O_MEUFGCMA_WOTSTWES.ps{1} (set_chidx ad{1} i) 0 (BaseW.val em{1}.[i]) (val (nth witness sk{1} i)))
               /\ (forall (i : int), 0 <= i < size chal0{2} => 
                    nth witness chal0{2} i 
                    = 
                    cf O_DistRCH.ps{2} (set_chidx ad0{2} i) 0 (BaseW.val em0{2}.[i] - 1) (val (nth witness chal'{2} i)))); last first.
        - by wp; rnd; wp; skip => |>; smt(ge2_len WAddress.valP).
        wp; skip => |> &1 &2 adch ge0_szsig lelen_szsig ge0_szc0 lelen_szc0 eq_sz valsig valc0 ltlen_szsig ltlen_szc0.
        split; last by smt(size_rcons).
        rewrite 2!andbA; split; first by smt(size_rcons).
        split => [| @/cf] i ge0_i; rewrite size_rcons => ltszsig1_i.   
        - rewrite nth_rcons; case (i < size sig{1}) => [/# | /lezNgt geszsig_i].
          by rewrite (: i = size sig{1}) 1:/#.
        rewrite nth_rcons /=; case (i < size chal0{2}) => [/# | /lezNgt geszsig_i].
        by rewrite (: i = size chal0{2}) 1:/#.
      while (   ={m, ad, pk, em}
             /\ valid_wadrs ad{1}
             /\ sk{1} = chal'{2}
             /\ sk{1} \in ddgstblockl
             /\ chal'{2} \in ddgstblockl
             /\ O_MEUFGCMA_WOTSTWES.ps{1} = O_DistRCH.ps{2}
             /\ O_MEUFGCMA_WOTSTWES.ps{1} = O_THFC_Default.pp{2}
             /\ 0 <= size pk{1} <= len
             /\ 0 <= size pk{2} <= len
             /\ 0 <= size sig{2} <= len
             /\ size pk{1} = size pk{2}
             /\ size pk{2} = size sig{2}
             /\ size sig{1} = len
             /\ size chal{2} = len
             /\ (forall (i : int), 0 <= i < len =>
                  nth witness sig{1} i 
                  = 
                  cf O_MEUFGCMA_WOTSTWES.ps{1} (set_chidx ad{1} i) 0 (BaseW.val em{1}.[i]) (val (nth witness sk{1} i)))
             /\ (forall (i : int), 0 <= i < len => 
                  nth witness chal{2} i 
                  = 
                  cf O_DistRCH.ps{2} (set_chidx ad{2} i) 0 (BaseW.val em{2}.[i] - 1) (val (nth witness chal'{2} i)))
             /\ (forall (i : int), 0 <= i < size sig{2} => 
                   nth witness sig{1} i = nth witness sig{2} i)); last first.
      + skip => |> &1 &2 adch chin eqlen_szsig eqlen_szc valsig valch. 
        split => [| pkr sigr *]; first by smt(ge2_len).        
        by have ->: sig{1} = sigr by apply (eq_from_nth witness) => /#.
      wp => /=.
      while{2} (   ={m, ad, pk, em}
                /\ valid_wadrs ad{1}
                /\ sk{1} = chal'{2}
                /\ sk{1} \in ddgstblockl
                /\ chal'{2} \in ddgstblockl
                /\ O_MEUFGCMA_WOTSTWES.ps{1} = O_DistRCH.ps{2}
                /\ O_MEUFGCMA_WOTSTWES.ps{1} = O_THFC_Default.pp{2}
                /\ 0 <= size pk{1} < len
                /\ 0 <= size pk{2} < len
                /\ 0 <= size sig{2} < len
                /\ 0 <= j{2} <= w - 1 - em_ele{2}
                /\ (forall (i : int), 0 <= i < len =>
                      nth witness sig{1} i 
                      = 
                      cf O_MEUFGCMA_WOTSTWES.ps{1} (set_chidx ad{1} i) 0 (BaseW.val em{1}.[i]) (val (nth witness sk{1} i)))
                /\ (forall (i : int), 0 <= i < len => 
                     nth witness chal{2} i 
                     =
                     cf O_DistRCH.ps{2} (set_chidx ad{2} i) 0 (BaseW.val em{2}.[i] - 1) (val (nth witness chal'{2} i)))
                /\ (forall (i : int), 0 <= i < size sig{2} => 
                      nth witness sig{1} i = nth witness sig{2} i)
                /\ chal_ele{2} = nth witness chal{2} (size pk{2})
                /\ em_ele{2} = BaseW.val em{2}.[size pk{2}]
                /\ (sig_ele{2} 
                    = 
                    if em_ele{2} <> 0 
                    then cf O_THFC_Default.pp{2} (set_chidx ad{2} (size pk{2})) (em_ele{2} - 1) 1 (val chal_ele{2})
                    else chal_ele{2})
                /\ pk_ele{2} 
                   = 
                   cf O_THFC_Default.pp{2} (set_chidx ad{2} (size pk{2})) em_ele{2} j{2} (val sig_ele{2}))
               (w - 1 - em_ele{2} - j{2}).
      + move=> &1 z.
        wp; skip => |> &2 adch skin ge0_szpk ltlen_szpk ge0_szsig ltlen_szsig ge0_j lew1em_j valsig valchal relsigs ltw1em_j.
        rewrite -andbA andbC -andbA valP; split => [| /#].
        by rewrite -/f eq_sym /cf chS 1:validwadrs_setchidx 3:valP //; smt(BaseW.valP).
      wp; skip => |> &1 &2 adch chin ge0_szpk lelen_szpk ge0_szsig lelen_szsig eq_sz eqlen_szsig eqlen_szc valsig valchal relsigs ltlen_szpk.
      split => [eq0_em @/cf | neq0_em].
      + split => [| j]; first rewrite ch0 1:validwadrs_setchidx 3:valP // valKd; smt(BaseW.valP).
        split =>[ | /lezNgt gew1_j _ _ lew1_j]; first by smt(BaseW.valP).
        rewrite (: j = w - 1 - BaseW.val em{2}.[size pk{2}]) 1:/#.
        split; last by smt(size_rcons).
        rewrite -!andbA; split; last first.
        - rewrite !andbA; split; first by smt(size_rcons).
          rewrite size_rcons => i ge0_i ltszsig1_i.
          rewrite nth_rcons; case (i < size sig{2}) => [ltszsig_i /# | /lezNgt geszsig_i].
          rewrite (: i = size sig{2}) 1:/# /= -eq_sz valsig 2:valchal // eq0_em.
          by rewrite /cf ?ch0 1,4:validwadrs_setchidx // 1,2:valP.
        congr; rewrite valchal 1:// eq0_em /=; do 2! congr.
        by rewrite /cf ch0 1:validwadrs_setchidx // 1:valP // valKd.
      rewrite valP -/f.
      split => [@/cf | jr]. 
      + rewrite ch1 1:validwadrs_setchidx // 1:valP //=; first 2 by smt(BaseW.valP).
        by rewrite ch0 1:validwadrs_setchidx // 1:valP //= valKd; smt(BaseW.valP).         
      split => [/# | /lezNgt gew1em_jr ltlen_szsig ge0_jr lew1em_jr fcf1].
      have ->: jr = w - 1 - BaseW.val em{2}.[size pk{2}] by smt().
      rewrite !andbA -andbA; split; last by smt(size_rcons). 
      rewrite andbC -!andbA andbA; split; last by smt(size_rcons). 
      split; last congr.
      + rewrite size_rcons => i ge0_i ltszsig1_i; rewrite nth_rcons.
        case (i < size sig{2}) => ?; first by rewrite (relsigs i).
        rewrite (: i = size sig{2}) 1:/# eq_sz /=.
        by rewrite (valsig (size sig{2})) 2:(valchal (size sig{2})) 1,2:/# /cf chS; smt(BaseW.valP DigestBlock.valP validwadrs_setchidx).
      rewrite eq_sym (valchal (size pk{2})) 1:/#.
      have {1}->: BaseW.val em{2}.[size pk{2}] - 1 = 0 + (BaseW.val em{2}.[size pk{2}]) - 1 by trivial.
      rewrite /cf -chS 1:validwadrs_setchidx // 1:valP //; first 2 by smt(BaseW.valP).
      rewrite eq_sym.
      have {1}->:
        w - 1
        =
        BaseW.val em{2}.[size pk{2}] + (w - 1 - BaseW.val em{2}.[size pk{2}]) by smt().
      by rewrite /cf ch_comp //; smt(BaseW.valP DigestBlock.valP validwadrs_setchidx).
    * proc; inline *. 
      by auto.
    by skip.
  wp => /=.
  by sim : (   ={m, m', i, O_MEUFGCMA_WOTSTWES.qs}
            /\ pkWOTS0{1} = pkWOTS{2}
            /\ pkWOTS1{1} = pkWOTS0{2}
            /\ O_THFC_Default.tws{1} = R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl{2}).
byequiv => //.
proc; inline *.
seq 10 16 : (   ={glob A, glob O_THFC_Default, O_MEUFGCMA_WOTSTWES.qs, ps}
             /\ b{2} = true
             /\ (O_MEUFGCMA_WOTSTWES.ps = ps){1}
             /\ (O_DistRCH.b = b){2}
             /\ (O_DistRCH.ps = ps){2}
             /\ (O_THFC_Default.pp = ps){1}
             /\ (O_THFC_Default.pp = ps){2}
             /\ O_MEUFGCMA_WOTSTWES.qs{1} = []
             /\ O_MEUFGCMA_WOTSTWES.qs{2} = []
             /\ O_THFC_Default.tws{1} = []
             /\ O_THFC_Default.tws{2} = []
             /\ R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl{2} = []).
+ by auto => |>.
seq 1 1 : (   ={glob A, O_MEUFGCMA_WOTSTWES.qs, ps}
           /\ O_THFC_Default.tws{1} = R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl{2}).
+ call (:   ={O_MEUFGCMA_WOTSTWES.qs, O_THFC_Default.pp} 
         /\ O_DistRCH.b{2} = true
         /\ O_MEUFGCMA_WOTSTWES.ps{1} = O_DistRCH.ps{2}
         /\ O_MEUFGCMA_WOTSTWES.ps{1} = O_THFC_Default.pp{2}
         /\ O_THFC_Default.tws{1} = R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl{2}).
  - proc; inline *.
    rcondt{2} 6; first by auto.
    wp => /=; swap{1} 6 -2.
    seq 4 10 : (   #pre
                /\ ={ad, em, pk}
                /\ valid_wadrs ad{1}
                /\ ad0{2} = ad{2}
                /\ em{1} = encode_msgWOTS m{1}
                /\ em{2} = encode_msgWOTS m{2}
                /\ sk{1} = chal'{2}
                /\ chal{2} = chal'{2}
                /\ sk{1} \in ddgstblockl
                /\ chal'{2} \in ddgstblockl
                /\ pk{1} = []
                /\ pk{2} = []
                /\ sig{2} = []).
    * by auto => |>; rewrite WAddress.valP.
    seq 2 0 : (   #pre
               /\ size sig{1} = len
               /\ (forall (i : int), 0 <= i < len =>
                    nth witness sig{1} i 
                    = 
                    if BaseW.val em{1}.[i] <> 0
                    then cf O_MEUFGCMA_WOTSTWES.ps{1} (set_chidx ad{1} i) (BaseW.val em{1}.[i] - 1) 1 (val (nth witness sk{1} i))
                    else nth witness sk{1} i)).
    * while{1} (   ={m, ad, pk, em}
               /\ valid_wadrs ad{1}
               /\ em{1} = encode_msgWOTS m{1}
               /\ em{2} = encode_msgWOTS m{2}
               /\ sk{1} = chal'{2}
               /\ chal{2} = chal'{2}
               /\ O_MEUFGCMA_WOTSTWES.ps{1} = O_DistRCH.ps{2}
               /\ O_MEUFGCMA_WOTSTWES.ps{1} = O_THFC_Default.pp{2}
               /\ 0 <= size sig{1} <= len
               /\ (forall (i : int), 0 <= i < size sig{1} =>
                    nth witness sig{1} i 
                    = 
                    if BaseW.val em{1}.[i] <> 0
                    then cf O_MEUFGCMA_WOTSTWES.ps{1} (set_chidx ad{1} i) (BaseW.val em{1}.[i] - 1) 1 (val (nth witness sk{1} i))
                    else nth witness sk{1} i))
             (len - size sig{1}); last first.
      + wp; skip => |> &2 adch chalin.
        by split; smt(ge2_len).
      move=> &2 z.
      wp; skip => |> &1 adch ge0_szsig lelen_szsig valsiz ltlen_szsig.
      split => [eq0_em | neq0_em]; first smt(size_rcons nth_rcons DigestBlock.valKd).
      rewrite -!andbA andbA; split; first smt(size_rcons).
      split; last smt(size_rcons).
      move=> i ge0_i; rewrite size_rcons => ltszsig1_i; rewrite nth_rcons.
      case (i < size sig{1}) => [ltszsig_i /# | /lezNgt geszsig_i].
      by rewrite (: i = size sig{1}) 1:/# neq0_em.
    while (   ={m, ad, pk, em}
           /\ valid_wadrs ad{1}
           /\ sk{1} = chal'{2}
           /\ chal{2} = chal'{2}
           /\ sk{1} \in ddgstblockl
           /\ chal'{2} \in ddgstblockl
           /\ O_MEUFGCMA_WOTSTWES.ps{1} = O_DistRCH.ps{2}
           /\ O_MEUFGCMA_WOTSTWES.ps{1} = O_THFC_Default.pp{2}
           /\ 0 <= size pk{1} <= len
           /\ 0 <= size pk{2} <= len
           /\ 0 <= size sig{2} <= len
           /\ size pk{1} = size pk{2}
           /\ size pk{2} = size sig{2}
           /\ size sig{1} = len
           /\ (forall (i : int), 0 <= i < size sig{1} =>
                nth witness sig{1} i 
                = 
                if BaseW.val em{1}.[i] <> 0
                then cf O_MEUFGCMA_WOTSTWES.ps{1} (set_chidx ad{1} i) (BaseW.val em{1}.[i] - 1) 1 (val (nth witness sk{1} i))
                else nth witness sk{1} i)
           /\ (forall (i : int), 0 <= i < size sig{2} => 
                 nth witness sig{1} i = nth witness sig{2} i)); last first.
    * skip => |> &1 &2 adch chin eqlen_szsig valsig. 
      split => [| pkr sigr *]; first by smt(ge2_len).        
      by have ->: sig{1} = sigr by apply (eq_from_nth witness) => /#.
    wp => /=.
    while{2} (   ={m, ad, pk, em}
              /\ valid_wadrs ad{1}
              /\ sk{1} = chal'{2}
              /\ chal{2} = chal'{2}
              /\ sk{1} \in ddgstblockl
              /\ chal'{2} \in ddgstblockl
              /\ O_MEUFGCMA_WOTSTWES.ps{1} = O_DistRCH.ps{2}
              /\ O_MEUFGCMA_WOTSTWES.ps{1} = O_THFC_Default.pp{2}
              /\ 0 <= size pk{1} < len
              /\ 0 <= size pk{2} < len
              /\ 0 <= size sig{2} < len
              /\ 0 <= j{2} <= w - 1 - em_ele{2}
              /\ (forall (i : int), 0 <= i < size sig{1} =>
                    nth witness sig{1} i = 
                    if BaseW.val em{1}.[i] <> 0
                    then cf O_MEUFGCMA_WOTSTWES.ps{1} (set_chidx ad{1} i) (BaseW.val em{1}.[i] - 1) 1 (val (nth witness sk{1} i))
                    else nth witness sk{1} i)
              /\ (forall (i : int), 0 <= i < size sig{2} => 
                    nth witness sig{1} i = nth witness sig{2} i)
              /\ chal_ele{2} = nth witness chal{2} (size pk{2})
              /\ em_ele{2} = BaseW.val em{2}.[size pk{2}]
              /\ (sig_ele{2} 
                  = 
                  if em_ele{2} <> 0 
                  then cf O_THFC_Default.pp{2} (set_chidx ad{2} (size pk{2})) (em_ele{2} - 1) 1 (val chal_ele{2})
                  else chal_ele{2})
              /\ pk_ele{2} = cf O_THFC_Default.pp{2} (set_chidx ad{2} (size pk{2})) em_ele{2} j{2} (val sig_ele{2}))
             (w - 1 - em_ele{2} - j{2}).
      + move=> &1 z.
        wp; skip => |> &2 adch skin ge0_szpk ltlen_szpk ge0_szsig ltlen_szsig ge0_j lew1em_j valsig relsigs ltw1em_j.
        rewrite -andbA andbC -andbA valP; split => [| /#].
        by rewrite -/f eq_sym /cf chS 1:validwadrs_setchidx 3:valP //; smt(BaseW.valP).
      wp; skip => |> &1 &2 adch chin ge0_szpk lelen_szpk ge0_szsig lelen_szsig eq_sz eqlen_szsig valsig relsigs ltlen_szpk.      
      split => [eq0_em @/cf | neq0_em].
      + split => [| j]; first rewrite ch0 1:validwadrs_setchidx 3:valP // valKd; smt(BaseW.valP).
        split =>[ | /lezNgt gew1_j _ _ lew1_j]; first by smt(BaseW.valP).
        rewrite (: j = w - 1 - BaseW.val em{2}.[size pk{2}]) 1:/#.
        split; last by smt(size_rcons).
        rewrite -!andbA; split; last first.
        - rewrite !andbA; split; first by smt(size_rcons).
          rewrite size_rcons => i ge0_i ltszsig1_i.
          rewrite nth_rcons; case (i < size sig{2}) => [ltszsig_i /# | /lezNgt geszsig_i].
          by rewrite (: i = size sig{2}) 1:/# /= -eq_sz valsig 1:/# eq0_em /=.
        by congr; rewrite valsig 1:/# eq0_em.
      split => [@/cf | jr].
      + rewrite valP ch1 1:validwadrs_setchidx // 1:valP //=; first 2 by smt(BaseW.valP).
        by rewrite ch0 1:validwadrs_setchidx // 1:valP //= valKd; smt(BaseW.valP).
      split => [/# | /lezNgt gew1em_jr ltlen_szsig ge0_jr lew1em_jr fcf1].
      have ->: jr = w - 1 - BaseW.val em{2}.[size pk{2}] by smt().
      rewrite !andbA -andbA; split; last by smt(size_rcons). 
      rewrite andbC -!andbA andbA; split; last by smt(size_rcons). 
      split; last do 2! congr.
      + rewrite size_rcons => i ge0_i ltszsig1_i; rewrite nth_rcons.
        case (i < size sig{2}) => ?; first by rewrite (relsigs i).
        rewrite (: i = size sig{2}) 1:/# eq_sz /=.
        by rewrite (valsig (size sig{2})) 1:/# -eq_sz neq0_em /= /cf ch1 //; smt(BaseW.valP DigestBlock.valP validwadrs_setchidx).
      by congr; rewrite valsig 1:/# neq0_em /cf ch1 1:validwadrs_setchidx 3,6:valP //=; first 2 by smt(BaseW.valP).
    * proc; inline *. 
    by auto.
  by skip.
wp => /=.
by sim : (   ={m, m', i, O_MEUFGCMA_WOTSTWES.qs}
          /\ pkWOTS0{1} = pkWOTS{2}
          /\ pkWOTS1{1} = pkWOTS0{2}
          /\ O_THFC_Default.tws{1} = R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl{2}).
qed.

(* Auxiliary lemma: Reduce SM_DT_UD_C to distinguishing between two relevant distributions. *)
local lemma DistRCH_SMDTUDC &m :
  `|Pr[DistRCH.main(false) @ &m : res] - Pr[DistRCH.main(true) @ &m : res]|
  =
  (w - 2)%r * 
  `|Pr[SM_DT_UD_C(R_SMDTUDC_DistRCH, O_SMDTUD_Default, O_THFC_Default).main(false) @ &m : res] - 
    Pr[SM_DT_UD_C(R_SMDTUDC_DistRCH, O_SMDTUD_Default, O_THFC_Default).main(true) @ &m : res]|.
proof.
have ->:
  Pr[DistRCH.main(false) @ &m : res] - Pr[DistRCH.main(true) @ &m : res]
  =
  Pr[DistRCHil.main(0) @ &m : res] - Pr[DistRCHil.main(w - 2) @ &m : res].
+ congr; last congr.
  - byequiv => //.
    transitivity DistRCHi.main
                 (={glob A} /\ arg{1} = false /\ arg{2} = 0 ==> ={res})
                 (={glob A, i} ==> ={res}) => [/# | // | |]; last first.
    * by apply DistRCHi_Orig_Alt.
    proc; inline *. 
    seq 16 17: (   ={glob A, glob O_MEUFGCMA_WOTSTWES, glob O_THFC_Default, O_DistRCH.ps, R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl, ps}
                /\ b{1} = false
                /\ i{2} = 0
                /\ O_DistRCH.b{1} = b{1}
                /\ DistRCHi.O_DistRCHi.i{2} = i{2}
                /\ O_THFC_Default.pp{1} = ps{1}
                /\ O_DistRCH.ps{1} = ps{1}
                /\ O_THFC_Default.tws{1} = []
                /\ O_MEUFGCMA_WOTSTWES.qs{1} = []
                /\ R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl{1} = []); first by auto.
    seq 1 1 : (={glob A, O_MEUFGCMA_WOTSTWES.qs, R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl, ps}); last by sim.
    call (:   ={O_MEUFGCMA_WOTSTWES.qs, O_THFC_Default.pp, O_DistRCH.ps, R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl}
           /\ O_DistRCH.b{1} = false
           /\ DistRCHi.O_DistRCHi.i{2} = 0) => //; last first.
    * by proc => |>; sim.
    proc; inline * => |>.
    rcondf{1} 6; first by auto.
    by sim; while (#pre /\ ={ad0, m0, chal', em0, chal0}); auto.
  byequiv => //.
  transitivity DistRCHi.main
               (={glob A} /\ arg{1} = true /\ arg{2} = w - 2 ==> ={res})
               (={glob A, i} ==> ={res}) => [/# | // | |]; last first.
  * by apply DistRCHi_Orig_Alt.
  proc; inline *.
  seq 16 17: (   ={glob A, glob O_MEUFGCMA_WOTSTWES, glob O_THFC_Default, O_DistRCH.ps, R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl, ps}
              /\ b{1} = true
              /\ i{2} = w - 2
              /\ O_DistRCH.b{1} = b{1}
              /\ DistRCHi.O_DistRCHi.i{2} = i{2}
              /\ O_THFC_Default.pp{1} = ps{1}
              /\ O_DistRCH.ps{1} = ps{1}
              /\ O_THFC_Default.tws{1} = []
              /\ O_MEUFGCMA_WOTSTWES.qs{1} = []
              /\ R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl{1} = []); first by auto.
  seq 1 1 : (={glob A, O_MEUFGCMA_WOTSTWES.qs, R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl, ps}); last by sim.
  call (:   ={O_MEUFGCMA_WOTSTWES.qs, O_THFC_Default.pp, O_DistRCH.ps, R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl}
         /\ O_DistRCH.b{1} = true
         /\ DistRCHi.O_DistRCHi.i{2} = w - 2) => //; last first.
  - by proc => |>; sim.
  proc; inline * => |>.
  rcondt{1} 6; first by auto.
  sim.
  while{2} (   #pre 
            /\ ={ad, ad0, m0, chal'}
            /\ valid_wadrs ad0{2}
            /\ (forall (i : int), 0 <= i < size chal0{2} => 
                  nth witness chal'{1} i = nth witness chal0{2} i)
            /\ 0 <= size chal0{2} <= len)
           (len - size chal0{2}). 
  - move=> &1 z.
    wp; skip => |> &2 adch valchal ge0_szchal lelen_szchal ltlen_szchal.
    rewrite -!andbA; split; last by smt(size_rcons).
    move=> i ge0_i; rewrite size_rcons nth_rcons => ltsz1_i.
    case (i < size chal0{2}) => [ltsz_i | /lezNgt gesz_i].
    * by rewrite (valchal i) 1:ge0_i 1:ltsz_i.
    rewrite (: i = size chal0{2}) 1:/# /=.
    pose v := BaseW.val _ - _ - _; have le0_v : v <= 0 by smt(BaseW.valP val_w).
    by rewrite /cf ch0 1:validwadrs_setchidx 3:valP // valKd.
  wp; rnd; wp; skip => |> &1 chal chalin.
  split => [| chal']; first by smt(ge2_len WAddress.valP).
  split => [/# |/lezNgt gelen_sz _ chalpval ge0_sz lelen_sz].
  have eq_sz: size chal = size chal'.
  - have: 0 <= len by smt(ge2_len). 
    by move/(supp_dlist_size ddgstblock _ chal) => /(_ _) // /#.
  by apply (eq_from_nth witness) => //; rewrite eq_sz.
have indtelesum:
  forall (i : int), 0 <= i =>    
    Pr[DistRCHil.main(0) @ &m : res] - Pr[DistRCHil.main(i) @ &m : res]
    =
    BRA.bigi predT (fun (x : int) => Pr[DistRCHil.main(x) @ &m : res] - Pr[DistRCHil.main(x + 1) @ &m : res]) 0 i.
+ elim => [/= | i ge0_i ih]; first by rewrite range_geq.
  rewrite -addr0 (: 0%r = (- Pr[DistRCHil.main(i) @ &m : res] + Pr[DistRCHil.main(i) @ &m : res])) 1:/#.
  by rewrite addrA ih BRA.big_int_recr //= addrA.
rewrite (indtelesum (w - 2)); first by smt(val_w).
have ->:
  BRA.bigi predT (fun (i : int) => Pr[DistRCHil.main(i) @ &m : res] - Pr[DistRCHil.main(i + 1) @ &m : res]) 0 (w - 2)
  =
  BRA.bigi predT (fun (i : int) => Pr[SM_DT_UD_Ci.main(i, false) @ &m : res] - Pr[SM_DT_UD_Ci.main(i, true) @ &m : res]) 0 (w - 2).
+ rewrite 2!BRA.big_int &(BRA.eq_bigr) => k [ge0_k ltw1_k] /=.
  congr; last congr.
  - byequiv => //.
    proc => /=; inline{1} 6.
    wp; inline{1} 5; inline{2} 5; inline{2} 6; inline{2} 4; inline{2} 7.
    seq 6 8 : (   ={glob A, glob O_MEUFGCMA_WOTSTWES, glob O_THFC_Default, R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl, O_DistRCH.b, i}
               /\ i{1} = k
               /\ b{2} = false
               /\ ps{1} = pp{2}
               /\ O_SMDTUD_Default.b{2} = b{2}
               /\ DistRCHil.O_DistRCHi.i{1} = i{1}
               /\ R_SMDTUDC_DistRCHil.O_R_SMDTUDC_DistRCHil.i{2} = i{2}
               /\ O_DistRCH.ps{1} = ps{1}
               /\ O_THFC_Default.pp{1} = ps{1}
               /\ O_SMDTUD_Default.pp{2} = pp{2}
               /\ O_MEUFGCMA_WOTSTWES.qs{1} = [] 
               /\ O_THFC_Default.tws{1} = []
               /\ O_SMDTUD_Default.ts{2} = []
               /\ R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl{1} = []).
    * by inline *; auto.
    seq 1 2 : (   ={glob A, glob O_MEUFGCMA_WOTSTWES, O_THFC_Default.pp, R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl, ps}
               /\ all valid_wadrs (map (fun (admpksig : adrs * msgWOTS * pkWOTS * sigWOTS) => admpksig.`1) O_MEUFGCMA_WOTSTWES.qs{1})
               /\ O_SMDTUD_Default.ts{2} = relcqsad_udi O_MEUFGCMA_WOTSTWES.qs{1} k
               /\ all (fun (ad : adrs) => 
                         ad \in R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl{2} 
                         \/ ad \in reltqsad_udi O_MEUFGCMA_WOTSTWES.qs{1} k) 
                         O_THFC_Default.tws{2}).
    * wp => /=.
      call (:   ={glob O_MEUFGCMA_WOTSTWES, O_THFC_Default.pp, R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl, O_DistRCH.b}
             /\ O_DistRCH.ps{1} = O_SMDTUD_Default.pp{2}
             /\ O_SMDTUD_Default.pp{2} = O_THFC_Default.pp{2} 
             /\ O_SMDTUD_Default.b{2} = false
             /\ DistRCHil.O_DistRCHi.i{1} = k
             /\ R_SMDTUDC_DistRCHil.O_R_SMDTUDC_DistRCHil.i{2} = k
             /\ all valid_wadrs (map (fun (admpksig : adrs * msgWOTS * pkWOTS * sigWOTS) => admpksig.`1) O_MEUFGCMA_WOTSTWES.qs{1})
             /\ O_SMDTUD_Default.ts{2} = relcqsad_udi O_MEUFGCMA_WOTSTWES.qs{1} k
             /\ all (fun (ad : adrs) => 
                         ad \in R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl{2} 
                         \/ ad \in reltqsad_udi O_MEUFGCMA_WOTSTWES.qs{1} k) 
                         O_THFC_Default.tws{2}); last by auto.
      + proc.
        seq 2 2 : (   ={glob O_MEUFGCMA_WOTSTWES, O_THFC_Default.pp, R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl, O_DistRCH.b, ad, m, chal}
                   /\ valid_wadrs ad{1}
                   /\ O_DistRCH.ps{1} = O_SMDTUD_Default.pp{2}
                   /\ O_SMDTUD_Default.pp{2} = O_THFC_Default.pp{2}
                   /\ O_SMDTUD_Default.b{2} = false
                   /\ DistRCHil.O_DistRCHi.i{1} = k
                   /\ R_SMDTUDC_DistRCHil.O_R_SMDTUDC_DistRCHil.i{2} = k
                   /\ all valid_wadrs (map (fun (admpksig : adrs * msgWOTS * pkWOTS * sigWOTS) => admpksig.`1) O_MEUFGCMA_WOTSTWES.qs{1})
                   /\ O_SMDTUD_Default.ts{2} = relcqsad_udi (rcons O_MEUFGCMA_WOTSTWES.qs{1} (ad{2}, m{2}, insubd pk{2}, insubd sig{2})) k
                   /\ all (fun (ad' : adrs) => 
                               ad' \in R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl{2} 
                               \/ ad' \in reltqsad_udi (rcons O_MEUFGCMA_WOTSTWES.qs{1} (ad{2}, m{2}, insubd pk{2}, insubd sig{2})) k) 
                               O_THFC_Default.tws{2}
                   /\ size chal{1} = len).
        - inline *; swap{1} 7 -2.
          wp => /=.
          while (   ={glob O_MEUFGCMA_WOTSTWES, O_THFC_Default.pp, R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl, O_DistRCH.b, ad, m, ad0, m0, em0, chal0}
                 /\ ad0{1} = ad{1}
                 /\ m0{1} = m{1}
                 /\ em0{1} = encode_msgWOTS m0{1}
                 /\ valid_wadrs ad{1}
                 /\ O_DistRCH.ps{1} = O_SMDTUD_Default.pp{2}
                 /\ O_SMDTUD_Default.pp{2} = O_THFC_Default.pp{2}
                 /\ O_SMDTUD_Default.b{2} = false
                 /\ DistRCHil.O_DistRCHi.i{1} = k
                 /\ R_SMDTUDC_DistRCHil.O_R_SMDTUDC_DistRCHil.i{2} = k
                 /\ all valid_wadrs (map (fun (admpksig : adrs * msgWOTS * pkWOTS * sigWOTS) => admpksig.`1) O_MEUFGCMA_WOTSTWES.qs{1})
                 /\ O_SMDTUD_Default.ts{2} = relcqsad_udi (rcons O_MEUFGCMA_WOTSTWES.qs{1} (ad{2}, m{2}, insubd pk{2}, insubd sig{2})) k
                 /\ all (fun (ad' : adrs) => 
                             ad' \in R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl{2} 
                             \/ ad' \in reltqsad_udi (rcons O_MEUFGCMA_WOTSTWES.qs{1} (ad{2}, m{2}, insubd pk{2}, insubd sig{2})) k) 
                             O_THFC_Default.tws{2}
                 /\ (forall (i : int), 0 <= i < len =>
                       nth witness chal'{2} i
                       = 
                       if R_SMDTUDC_DistRCHil.O_R_SMDTUDC_DistRCHil.i{2} < BaseW.val em0{2}.[i] - 1
                       then cf O_SMDTUD_Default.pp{2} (set_chidx ad0{2} i) R_SMDTUDC_DistRCHil.O_R_SMDTUDC_DistRCHil.i{2} 1 (val (nth witness chal'{1} i)) 
                       else nth witness chal'{1} i)
                 /\ size chal'{1} = size chal'{2}
                 /\ size chal'{1} = len
                 /\ 0 <= size chal0{1} <= len).
          * swap{1} 1 1; sp 1 1; wp => /=.
            if{2} => //=; last first.
            + wp; skip => |> &1 &2 *. 
              rewrite !andbA -3!andbA; split; last by smt(size_rcons).
              congr; pose em1k := BaseW.val _ - 1 - k; have le0_em1k : em1k <= 0 by smt().
              by rewrite /cf ch0 1:validwadrs_setchidx 3:valP // valKd /#.
            while{2} (   valid_wadrs ad0{2} 
                      /\ R_SMDTUDC_DistRCHil.O_R_SMDTUDC_DistRCHil.i{2} = k
                      /\ ad0{2} = ad{2}
                      /\ m0{2} = m{2}
                      /\ em0{2} = encode_msgWOTS m0{2}
                      /\ em_ele0{2} = BaseW.val em0{2}.[size chal0{2}]
                      /\ chal_ele0{2} = cf O_THFC_Default.pp{2} (set_chidx ad0{2} (size chal0{2})) (R_SMDTUDC_DistRCHil.O_R_SMDTUDC_DistRCHil.i{2} + 1) (j0{2} - 1) (val (nth witness chal'{2} (size chal0{2})))
                      /\ all (fun (ad' : adrs) => 
                             ad' \in R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl{2} 
                             \/ ad' \in reltqsad_udi (rcons O_MEUFGCMA_WOTSTWES.qs{1} (ad{2}, m{2}, insubd pk{2}, insubd sig{2})) k) 
                             O_THFC_Default.tws{2}
                      /\ size chal'{2} = len
                      /\ 0 <= size chal0{2} < len
                      /\ 1 <= j0{2} <= em_ele0{2} - 1 - R_SMDTUDC_DistRCHil.O_R_SMDTUDC_DistRCHil.i{2})
                     (em_ele0{2} - 1 - R_SMDTUDC_DistRCHil.O_R_SMDTUDC_DistRCHil.i{2} - j0{2}).
            + auto => |> &2 adch twssp eqlen_szcp ge0_szc0 ltlen_szc0 ge1_j leem1k_j ltem1k_j.
              rewrite !andbA -2!andbA; split => [| /#].
              split. 
              - by rewrite valP -/f /cf eq_sym chS 1:validwadrs_setchidx 3:valP // 1,2:/#; smt(BaseW.valP).
              rewrite allP => ad'; rewrite mem_rcons /= => -[-> | adpin] /=.
              - right; rewrite /reltqsad_udi -flatten_mapP.
                exists (ad{2}, m{2}, insubd pk{2}, insubd sig{2}) => /=; split; first by rewrite mem_rcons.
                rewrite -flatten_mapP; exists (size chal0{2}) => /=; split; first by smt(size_iota mem_iota).
                pose em_ele := BaseW.val _; case (k < em_ele - 1) => ?; last case (em_ele <> 0) => ?.
                * by rewrite mapP; exists (j0{2} - 1) => /=; split; smt(size_iota mem_iota BaseW.valP).
                * by rewrite mapP; exists (k + j0{2} - em_ele + 1) => /=; split; smt(size_iota mem_iota BaseW.valP).
                by rewrite mapP; exists (k + j0{2} - em_ele) => /=; split; smt(size_iota mem_iota BaseW.valP).
              by move/allP: twssp => /(_ ad' adpin).
            wp; skip => |> &1 &2 adch qsch twssp relcp eqsz eqlen_szcp ge0_szc0 lelen_szc0 ltlen_szc0 leem1k_j.
            split => [| twsr jr].
            + by rewrite /cf ch0 // 1:validwadrs_setchidx 3:valP // valKd -eqsz eqlen_szcp /#.
            split => [/# | /lezNgt geem1k_jr twsrsp eqlen_cp2 ge1_jr leem1k_jr].
            rewrite !andbA -3!andbA; split; last by smt(size_rcons).
            pose em1k := BaseW.val _ - 1 - k; have-> : jr = em1k by smt().
            move: (relcp (size chal0{2}) _); first by smt().
            rewrite leem1k_j /= {1}(: em1k = 1 + (em1k - 1)) // /cf => ->.
            by rewrite ch_comp 1:validwadrs_setchidx 3:valP //; smt(BaseW.valP).
          wp => /=.
          while (   ={glob O_MEUFGCMA_WOTSTWES, O_THFC_Default.pp, R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl, O_DistRCH.b, ad, m, ad0, m0, em0}
                     /\ ad0{1} = ad{1}
                     /\ m0{1} = m{1}
                     /\ em0{1} = encode_msgWOTS m0{1}
                     /\ valid_wadrs ad{1}
                     /\ O_DistRCH.ps{1} = O_SMDTUD_Default.pp{2}
                     /\ O_SMDTUD_Default.pp{2} = O_THFC_Default.pp{2}
                     /\ O_SMDTUD_Default.b{2} = false
                     /\ DistRCHil.O_DistRCHi.i{1} = k
                     /\ R_SMDTUDC_DistRCHil.O_R_SMDTUDC_DistRCHil.i{2} = k
                     /\ all valid_wadrs (map (fun (admpksig : adrs * msgWOTS * pkWOTS * sigWOTS) => admpksig.`1) O_MEUFGCMA_WOTSTWES.qs{1})
                     /\ O_SMDTUD_Default.ts{2} 
                        = 
                        relcqsad_udi O_MEUFGCMA_WOTSTWES.qs{1} k 
                        ++ relcqsad_udi_outer ad0{2} m0{2} k (size chal'{2})
                     /\ all (fun (ad' : adrs) => 
                                 ad' \in R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl{2} 
                                 \/ ad' \in reltqsad_udi (rcons O_MEUFGCMA_WOTSTWES.qs{1} (ad{2}, m{2}, insubd pk{2}, insubd sig{2})) k) 
                                 O_THFC_Default.tws{2}
                     /\ (forall (i : int), 0 <= i < size chal'{2} =>
                           nth witness chal'{2} i
                           = 
                           if R_SMDTUDC_DistRCHil.O_R_SMDTUDC_DistRCHil.i{2} < BaseW.val em0{2}.[i] - 1
                           then cf O_SMDTUD_Default.pp{2} (set_chidx ad0{2} i) R_SMDTUDC_DistRCHil.O_R_SMDTUDC_DistRCHil.i{2} 1 (val (nth witness chal'{1} i)) 
                           else nth witness chal'{1} i)
                     /\ size chal'{1} = size chal'{2}
                     /\ 0 <= size chal'{1} <= len).
          * wp; sp => /=.
            if{2} => //; last first. 
            + wp; rnd; skip => |> &1 &2 adch qsch twssp relcp eqsz ge0_szcp lelen_szcp ltlen_szcp ltlen_szcp2 geem1_k cel celin.
              rewrite !andbA -4!andbA; split; last by smt(size_rcons).
              split; first congr.
              - by rewrite /relcqsad_udi_outer size_rcons mkseqS //= geem1_k flatten_rcons cats0.
              move=> i ge0_i; rewrite size_rcons => ltszcp1_i.
              rewrite ?nth_rcons ?eqsz; case (i < size chal'{2}) => [ltszcp_i /#| /lezNgt geszcp_i].
              by rewrite (: i = size chal'{2}) 1:/# /= geem1_k.
            rcondf{2} 2; first by auto.
            wp.
            rnd DigestBlock.val DigestBlock.insubd.
            wp; skip => |> &1 &2 adch qsch twssp relcp eqsz ge0_szcp lelen_szcp ltlen_szcp ltlen_szcp2 ltem1_k.
            split => [x xin | _].
            + by rewrite insubdK; move/supp_dmap: xin => -[x' [_ ->]]; first rewrite valP. 
            split => [x xin | _]; first apply in_dmap1E_can.
            + by rewrite insubdK; move/supp_dmap: xin => -[x' [_ ->]]; first rewrite valP. 
            + by move=> y yin <-; rewrite valKd.
            move=> cel celin; split => [| _]; first by apply dmap_supp.
            rewrite valKd /= !andbA -4!andbA; split; last by smt(size_rcons).
            split; last first.
            + move=> i ge0_i; rewrite size_rcons => ltszcp1_i.
              rewrite ?nth_rcons ?eqsz; case (i < size chal'{2}) => [ltszcp_i /# | /lezNgt geszcp_i].
              by rewrite (: i = size chal'{2}) 1:/# ltem1_k /= /cf ch1 1:validwadrs_setchidx 3:valP // /#. 
            rewrite rcons_cat size_rcons; congr.
            by rewrite -relcqsad_udi_outer_cat // ltem1_k /= cats1.
          wp; skip => |> &2 qsch twssp.
          split => [| cl cr /lezNgt gelen_szcr /lezNgt gelen_szcl _ twsrcsp relclcr eqsz_clcr ge0_szcl lelen_szcl].
          + rewrite 2!andbA; split; last by smt(ge2_len).
            rewrite -andbA; split; first by rewrite WAddress.valP.
            rewrite /relcqsad_udi_outer mkseq0 flatten_nil cats0 //=.
            rewrite allP => ad' adpin /=.
            move/allP: twssp => /(_ ad' adpin) /= [-> //|].
            move/flatten_mapP => [q] [qin /= adpinrel].
            by right; rewrite -flatten_mapP; exists q; split => //; smt(mem_rcons).
          rewrite andbA -2!andbA; split; last by smt(ge2_len).
          by rewrite (: size cr = len) 1:/# &(relcqsad_udi_outer_full).
        wp => /=.
        while (   #pre 
               /\ ={em, pk, sig}
               /\ em{1} = encode_msgWOTS m{1}
               /\ size pk{1} = size sig{1}
               /\ size pk{2} = size sig{2}
               /\ 0 <= size pk{1} <= len
               /\ 0 <= size pk{2} <= len).
        - inline O_THFC_Default.query.
          wp; sp 2 2 => /=.
          while (   #pre
                 /\ ={j, sig_ele, pk_ele}
                 /\ pk_ele{1} = cf O_THFC_Default.pp{1} (set_chidx ad{1} (size pk{1})) em_ele{1} j{1} (val sig_ele{1})
                 /\ 0 <= j{1} <= w - 1 - em_ele{1}).
          * wp; skip => |> &2 adch qsch twsrcsp eqlen_szc eqsz ge0_szpk lelen_szpk ltlen_szpk ge0_j lew1em_j ltw1em_j.
            rewrite valP !andbA -andbA; split => [| /#].
            split; first rewrite -(cats1 O_THFC_Default.tws{2}) all_cat /=; split => //.
            + right; rewrite /reltqsad_udi -flatten_mapP.
              exists (ad{2}, m{2}, insubd pk{2}, insubd sig{2}); split => /=; first by smt(mem_rcons).
              rewrite -flatten_mapP /=; exists (size pk{2}); split => /=; first by smt(mem_iota size_iota).
              pose em_ele := BaseW.val _; case (k < em_ele - 1) => *.
              - by rewrite mapP; exists (em_ele + j{2} - 1 - k); smt(BaseW.valP mem_iota size_iota).
              case (em_ele <> 0) => *; rewrite mapP.
              - by exists (j{2} + 1) => /=; smt(BaseW.valP mem_iota size_iota).
              by exists j{2}; smt(BaseW.valP mem_iota size_iota).
            rewrite -/f /cf; case (j{2} = 0) => [-> | neq0_j] //=.
            + by rewrite ch0 1:validwadrs_setchidx 3:valP // ch1 1:validwadrs_setchidx 3:valP // 3:valKd; first 2 smt(BaseW.valP).
            by rewrite (chS _ _ _ _ (j{2} + 1)) 1:validwadrs_setchidx 3:valP // 4:addrA //=; smt(BaseW.valP).
          wp; skip => |> &2 adch qsch twsrcsp eqlen_szc eqsz ge0_szpk lelen_szpk ltlen_szpk.
          split => [eq0_em | neq0_em *].
          * split => [| twsr jr /lezNgt gew1em_jr _ twsrrcsp ge0_jr lew1em_jr]. 
            + by rewrite /cf ch0 //= 1:validwadrs_setchidx 3:valP // valKd /= /#.
            rewrite !andbA -5!andbA; split; last by smt(size_rcons).
            split; first by rewrite (relcqsadudi_rcons_qs _ _ _ _ (DBLL.insubd (rcons _ _)) (insubd pk{2}) _ (insubd sig{2})).
            rewrite allP=> adrs adrsin /=; move/allP: twsrrcsp => /(_ adrs adrsin) /= [-> // | ?].
            by rewrite (reltqsadudi_rcons_qs _ _ _ _ _ (insubd pk{2}) _ (insubd sig{2})); right.
          split => [| twsr jr /lezNgt gew1em_jr _ twsrrcsp ge0_jr lew1em_jr].
          * rewrite !andbA -andbA; split; last first.
            + by rewrite valP /cf ch0 1:validwadrs_setchidx 3:valP // valKd; smt(BaseW.valP).
            rewrite -(cats1 O_THFC_Default.tws{2}) all_cat twsrcsp /=.
            right.
            rewrite /reltqsad_udi -flatten_mapP.
            exists (ad{2}, m{2}, insubd pk{2}, insubd sig{2}); split => /=; first by smt(mem_rcons).
            rewrite -flatten_mapP; exists (size pk{2}); split => /=; first by smt(mem_iota size_iota).
            pose em_ele := BaseW.val _; case (k < em_ele - 1) => ?.
            - by rewrite mapP; exists (em_ele - 2 - k); smt(BaseW.valP mem_iota size_iota).
            by rewrite neq0_em /= mapP; exists 0; smt(BaseW.valP mem_iota size_iota).
          rewrite !andbA -5!andbA; split; last by smt(size_rcons).
          rewrite (relcqsadudi_rcons_qs _ _ _ _ (DBLL.insubd (rcons _ _)) (insubd pk{2}) _ (insubd sig{2})) /=.
          by rewrite (reltqsadudi_rcons_qs _ _ _ _ _ (insubd pk{2}) _ (insubd sig{2})).
        wp; skip => |> &1 adch qsch twssp eqlen_szchal.
        rewrite -2!andbA; split; first by apply relcqsadudi_rcons_qs.
        split; first by rewrite (reltqsadudi_rcons_qs _ _ _ _ _ (insubd pk{1}) _ (insubd sig{1})).
        split => [| *]; first by smt(ge2_len).
        by move: qsch; rewrite 2!all_map /preim /= -cats1 all_cat.
      proc; inline *.
      by wp; skip => |> *; smt(allP mem_rcons).
    inline{1} 9; inline{1} 8; inline{1} 7; inline{1} 6; inline{1} 3.
    inline{2} 15; inline{2} 14; inline{2} 13; inline{2} 12.
    inline{2} 9; inline{2} 8; inline{2} 7; inline{2} 6; inline{2} 3.
    wp => /=.
    call (: true); first by sim.
    wp => /=.
    call (: true) => /=.
    wp; skip => |> &2 qsch twssp ims b. 
    rewrite eq_iff; split => [[#]| /#].
    move=> ge0_szqs led_szqs ge0_i ltszqs_i bt neqqs2_m uqpf djpf.
    rewrite !andbA andbC -!andbA 2!andbA; split => [|/#].
    split; last by apply uniq_relcqsadudi => /#.
    rewrite andbC; split; first split => [| _].
    * by smt(relcqsadudi_rng).
    * apply (IntOrder.ler_trans (size O_MEUFGCMA_WOTSTWES.qs{2} * len)); first by smt(relcqsadudi_rng).
      by rewrite ler_pmul //; smt(ge2_len).
    apply (djl_parts _ _ R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl{2} (reltqsad_udi O_MEUFGCMA_WOTSTWES.qs{2} k)) => //. 
    * by apply disj_relcqsadudi => /#.
    by apply disj_relcqsadudi_reltqsadudi => /#.
  byequiv => //.
  proc => /=; inline{1} 6.
  wp; inline{1} 5; inline{2} 5; inline{2} 6; inline{2} 4; inline{2} 7.
  seq 6 8 : (   ={glob A, glob O_MEUFGCMA_WOTSTWES, glob O_THFC_Default, R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl, O_DistRCH.b}
             /\ i{1} = k + 1
             /\ i{2} = k
             /\ b{2} = true
             /\ ps{1} = pp{2}
             /\ O_SMDTUD_Default.b{2} = b{2}
             /\ DistRCHil.O_DistRCHi.i{1} = i{1}
             /\ R_SMDTUDC_DistRCHil.O_R_SMDTUDC_DistRCHil.i{2} = i{2}
             /\ O_DistRCH.ps{1} = ps{1}
             /\ O_THFC_Default.pp{1} = ps{1}
             /\ O_SMDTUD_Default.pp{2} = pp{2}
             /\ O_MEUFGCMA_WOTSTWES.qs{1} = [] 
             /\ O_THFC_Default.tws{1} = []
             /\ O_SMDTUD_Default.ts{2} = []
             /\ R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl{1} = []).
  * by inline *; auto.
  seq 1 2 : (   ={glob A, glob O_MEUFGCMA_WOTSTWES, R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl, ps}
             /\ all valid_wadrs (map (fun (admpksig : adrs * msgWOTS * pkWOTS * sigWOTS) => admpksig.`1) O_MEUFGCMA_WOTSTWES.qs{1})
             /\ O_SMDTUD_Default.ts{2} = relcqsad_udi O_MEUFGCMA_WOTSTWES.qs{1} k
             /\ all (fun (ad : adrs) => 
                       ad \in R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl{2} \/ ad \in reltqsad_udi O_MEUFGCMA_WOTSTWES.qs{1} k) 
                       O_THFC_Default.tws{2}).
  * wp => /=.
    call (:   ={glob O_MEUFGCMA_WOTSTWES, O_THFC_Default.pp, R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl, O_DistRCH.b}
           /\ O_DistRCH.ps{1} = O_SMDTUD_Default.pp{2}
           /\ O_SMDTUD_Default.pp{2} = O_THFC_Default.pp{2} 
           /\ O_SMDTUD_Default.b{2} = true
           /\ DistRCHil.O_DistRCHi.i{1} = k + 1
           /\ R_SMDTUDC_DistRCHil.O_R_SMDTUDC_DistRCHil.i{2} = k
           /\ all valid_wadrs (map (fun (admpksig : adrs * msgWOTS * pkWOTS * sigWOTS) => admpksig.`1) O_MEUFGCMA_WOTSTWES.qs{1})
           /\ O_SMDTUD_Default.ts{2} = relcqsad_udi O_MEUFGCMA_WOTSTWES.qs{1} k
           /\ all (fun (ad : adrs) => 
                       ad \in R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl{2} 
                       \/ ad \in reltqsad_udi O_MEUFGCMA_WOTSTWES.qs{1} k) 
                       O_THFC_Default.tws{2}); last by auto.
    + proc.
      seq 2 2 : (   ={glob O_MEUFGCMA_WOTSTWES, O_THFC_Default.pp, R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl, O_DistRCH.b, ad, m, chal}
                 /\ valid_wadrs ad{1}
                 /\ O_DistRCH.ps{1} = O_SMDTUD_Default.pp{2}
                 /\ O_SMDTUD_Default.pp{2} = O_THFC_Default.pp{2}
                 /\ O_SMDTUD_Default.b{2} = true
                 /\ DistRCHil.O_DistRCHi.i{1} = k + 1
                 /\ R_SMDTUDC_DistRCHil.O_R_SMDTUDC_DistRCHil.i{2} = k
                 /\ all valid_wadrs (map (fun (admpksig : adrs * msgWOTS * pkWOTS * sigWOTS) => admpksig.`1) O_MEUFGCMA_WOTSTWES.qs{1})
                 /\ O_SMDTUD_Default.ts{2} = relcqsad_udi (rcons O_MEUFGCMA_WOTSTWES.qs{1} (ad{2}, m{2}, insubd pk{2}, insubd sig{2})) k
                 /\ all (fun (ad' : adrs) => 
                             ad' \in R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl{2} 
                             \/ ad' \in reltqsad_udi (rcons O_MEUFGCMA_WOTSTWES.qs{1} (ad{2}, m{2}, insubd pk{2}, insubd sig{2})) k) 
                             O_THFC_Default.tws{2}
                 /\ size chal{1} = len).
      - inline *; swap{1} 5 -2.
        wp => /=.
        while (   ={glob O_MEUFGCMA_WOTSTWES, O_THFC_Default.pp, R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl, O_DistRCH.b, ad, m, ad0, m0, em0, chal0, chal'}
               /\ ad0{1} = ad{1}
               /\ m0{1} = m{1}
               /\ em0{1} = encode_msgWOTS m0{1}
               /\ valid_wadrs ad{1}
               /\ O_DistRCH.ps{1} = O_SMDTUD_Default.pp{2}
               /\ O_SMDTUD_Default.pp{2} = O_THFC_Default.pp{2}
               /\ O_SMDTUD_Default.b{2} = true
               /\ DistRCHil.O_DistRCHi.i{1} = k + 1
               /\ R_SMDTUDC_DistRCHil.O_R_SMDTUDC_DistRCHil.i{2} = k
               /\ all valid_wadrs (map (fun (admpksig : adrs * msgWOTS * pkWOTS * sigWOTS) => admpksig.`1) O_MEUFGCMA_WOTSTWES.qs{1})
               /\ O_SMDTUD_Default.ts{2} = relcqsad_udi (rcons O_MEUFGCMA_WOTSTWES.qs{1} (ad{2}, m{2}, insubd pk{2}, insubd sig{2})) k
               /\ all (fun (ad' : adrs) => 
                           ad' \in R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl{2} 
                           \/ ad' \in reltqsad_udi (rcons O_MEUFGCMA_WOTSTWES.qs{1} (ad{2}, m{2}, insubd pk{2}, insubd sig{2})) k) 
                           O_THFC_Default.tws{2}
               /\ size chal'{1} = len
               /\ 0 <= size chal0{1} <= len).
        * swap{1} 1 1; sp 1 1; wp => /=.
          if{2} => //=; last first.
          + wp; skip => |> &1 &2 *. 
            rewrite !andbA -3!andbA; split; last by smt(size_rcons). 
            congr; pose em1k := BaseW.val _ - 1 - (k + 1); have le0_em1k : em1k <= 0 by smt().
            by rewrite /cf ch0 1:validwadrs_setchidx 3:valP // valKd.
          while{2} (   valid_wadrs ad0{2} 
                    /\ R_SMDTUDC_DistRCHil.O_R_SMDTUDC_DistRCHil.i{2} = k
                    /\ ad0{2} = ad{2}
                    /\ m0{2} = m{2}
                    /\ em0{2} = encode_msgWOTS m0{2}
                    /\ em_ele0{2} = BaseW.val em0{2}.[size chal0{2}]
                    /\ chal_ele0{2} = cf O_THFC_Default.pp{2} (set_chidx ad0{2} (size chal0{2})) (R_SMDTUDC_DistRCHil.O_R_SMDTUDC_DistRCHil.i{2} + 1) (j0{2} - 1) (val (nth witness chal'{2} (size chal0{2})))
                    /\ all (fun (ad' : adrs) => 
                           ad' \in R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl{2} 
                           \/ ad' \in reltqsad_udi (rcons O_MEUFGCMA_WOTSTWES.qs{1} (ad{2}, m{2}, insubd pk{2}, insubd sig{2})) k) 
                           O_THFC_Default.tws{2}
                    /\ size chal'{2} = len
                    /\ 0 <= size chal0{2} < len
                    /\ 1 <= j0{2} <= em_ele0{2} - 1 - R_SMDTUDC_DistRCHil.O_R_SMDTUDC_DistRCHil.i{2})
                   (em_ele0{2} - 1 - R_SMDTUDC_DistRCHil.O_R_SMDTUDC_DistRCHil.i{2} - j0{2}).
          + auto => |> &2 adch twssp eqlen_szcp ge0_szc0 ltlen_szc0 ge1_j leem1k_j ltem1k_j.
            rewrite valP !andbA -2!andbA; split => [| /#].
            split.
            - by rewrite -/f /cf eq_sym chS // 1:validwadrs_setchidx 3:valP //; smt(BaseW.valP).
            rewrite allP => ad'; rewrite mem_rcons /= => -[-> | adpin] /=.
            - right; rewrite /reltqsad_udi -flatten_mapP.
              exists (ad{2}, m{2}, insubd pk{2}, insubd sig{2}) => /=; split; first by rewrite mem_rcons.
              rewrite -flatten_mapP; exists (size chal0{2}) => /=; split; first by smt(size_iota mem_iota).
              pose em_ele := BaseW.val _; case (k < em_ele - 1) => ?; last case (em_ele <> 0) => ?.
              * by rewrite mapP; exists (j0{2} - 1) => /=; split; smt(size_iota mem_iota BaseW.valP).
              * by rewrite mapP; exists (k + j0{2} - em_ele + 1) => /=; split; smt(size_iota mem_iota BaseW.valP).
              by rewrite mapP; exists (k + j0{2} - em_ele) => /=; split; smt(size_iota mem_iota BaseW.valP).
            by move/allP: twssp => /(_ ad' adpin).
          wp; skip => |> &2 adch qsch twssp eqlen_szcp ge0_szc0 lelen_szc0 ltlen_szc0 leem1k_j.
          by split => [| twsr jr]; [rewrite /cf ch0 1:validwadrs_setchidx 3:valP //= valKd /# | smt(size_rcons)].
        wp => /=.
        while (   ={glob O_MEUFGCMA_WOTSTWES, O_THFC_Default.pp, R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl, O_DistRCH.b, ad, m, ad0, m0, chal'}
                   /\ ad0{1} = ad{1}
                   /\ m0{1} = m{1}
                   /\ em0{2} = encode_msgWOTS m0{2}
                   /\ valid_wadrs ad{1}
                   /\ O_DistRCH.ps{1} = O_SMDTUD_Default.pp{2}
                   /\ O_SMDTUD_Default.pp{2} = O_THFC_Default.pp{2}
                   /\ O_SMDTUD_Default.b{2} = true
                   /\ DistRCHil.O_DistRCHi.i{1} = k + 1
                   /\ R_SMDTUDC_DistRCHil.O_R_SMDTUDC_DistRCHil.i{2} = k
                   /\ all valid_wadrs (map (fun (admpksig : adrs * msgWOTS * pkWOTS * sigWOTS) => admpksig.`1) O_MEUFGCMA_WOTSTWES.qs{1})
                   /\ O_SMDTUD_Default.ts{2} 
                      = 
                      relcqsad_udi O_MEUFGCMA_WOTSTWES.qs{1} k 
                      ++ relcqsad_udi_outer ad0{2} m0{2} k (size chal'{2})
                   /\ all (fun (ad' : adrs) => 
                               ad' \in R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl{2} 
                               \/ ad' \in reltqsad_udi (rcons O_MEUFGCMA_WOTSTWES.qs{1} (ad{2}, m{2}, insubd pk{2}, insubd sig{2})) k) 
                               O_THFC_Default.tws{2}
                   /\ 0 <= size chal'{1} <= len).
        * wp; sp => /=.
          if{2} => //; last first. 
          + wp; rnd; skip => |> &1 adch qsch twssp ge0_szcp lelen_szcp ltlen_szcp geem1_k cel celin.
            rewrite !andbA -andbA; split; last by smt(size_rcons).
            by rewrite size_rcons /relcqsad_udi_outer mkseqS //= geem1_k /= flatten_rcons cats0.
          rcondt{2} 2; first by auto.
          wp.
          rnd. 
          wp; skip => |> &1 adch qsch twssp ge0_szcp lelen_szcp ltlen_szcp ltem1_k.
          move=> cel celin; rewrite !andbA -andbA; split; last by smt(size_rcons).
          rewrite rcons_cat size_rcons; congr.
          by rewrite -relcqsad_udi_outer_cat // ltem1_k /= cats1.
        wp; skip => |> &2 qsch twssp.
        split => [| cr /lezNgt gelen_szcr _ _ twsrcsp ge0_szcl lelen_szcl].
        + rewrite WAddress.valP /= andbA; split; last by smt(ge2_len).
          rewrite /relcqsad_udi_outer mkseq0 flatten_nil cats0 //=.
          rewrite allP => ad' adpin /=.
          move/allP: twssp => /(_ ad' adpin) /= [-> //|].
          move/flatten_mapP => [q] [qin /= adpinrel].
          by right; rewrite -flatten_mapP; exists q; split => //; smt(mem_rcons).
        rewrite andbA -2!andbA; split; last by smt(ge2_len).
        by rewrite (: size cr = len) 1:/# &(relcqsad_udi_outer_full).
      wp => /=.
      while (   #pre 
             /\ ={em, pk, sig}
             /\ em{1} = encode_msgWOTS m{1}
             /\ size pk{1} = size sig{1}
             /\ size pk{2} = size sig{2}
             /\ 0 <= size pk{1} <= len
             /\ 0 <= size pk{2} <= len).
      - inline O_THFC_Default.query.
        wp; sp 2 2 => /=.
        while (   #pre
               /\ ={pk_ele, sig_ele, j}
               /\ pk_ele{1} = cf O_THFC_Default.pp{1} (set_chidx ad{1} (size pk{1})) em_ele{1} j{1} (val sig_ele{1})
               /\ 0 <= j{1} <= w - 1 - em_ele{1}).
        * wp; skip => |> &2 adch qsch twsrcsp eqlen_szc eqsz ge0_szpk lelen_szpk ltlen_szpk  ge0_j lew1em_j ltw1em_j.
          rewrite !andbA -andbA; split => [| /#].
          split; first rewrite -(cats1 O_THFC_Default.tws{2}) all_cat /=; split => //.
          + right; rewrite /reltqsad_udi -flatten_mapP.
            exists (ad{2}, m{2}, insubd pk{2}, insubd sig{2}); split => /=; first by smt(mem_rcons).
            rewrite -flatten_mapP /=; exists (size pk{2}); split => /=; first by smt(mem_iota size_iota).
            pose em_ele := BaseW.val _; case (k < em_ele - 1) => *.
            - by rewrite mapP; exists (em_ele + j{2} - 1 - k); smt(BaseW.valP mem_iota size_iota).
            case (em_ele <> 0) => *; rewrite mapP.
            - by exists (j{2} + 1) => /=; smt(BaseW.valP mem_iota size_iota).
            by exists j{2}; smt(BaseW.valP mem_iota size_iota).
          rewrite valP; case (j{2} = 0) => [-> | neq0_j] //=.
          + rewrite /cf ch0 1:validwadrs_setchidx 3:valP // valKd.
            by rewrite -/f ch1 1:validwadrs_setchidx 3:valP //; smt(validwadrs_setchidx BaseW.valP).
          rewrite -/f /cf (chS _ _ _ _ (j{2} + 1)) 1:validwadrs_setchidx 3:valP //; smt(BaseW.valP).
        wp; skip => |> &2 adch qsch twsrcsp eqlen_szc eqsz ge0_szpk lelen_szpk ltlen_szpk.
        split => [eq0_em | neq0_em *].
        * split => [| twsr jr /lezNgt gew1em_jr _ twsrrcsp ge0_jr lew1em_jr].  
          + by rewrite /cf ch0 1:validwadrs_setchidx 3:valP //= valKd; split => [| /#].
          rewrite !andbA -5!andbA; split; last by smt(size_rcons).
          split; first by rewrite (relcqsadudi_rcons_qs _ _ _ _ (DBLL.insubd (rcons _ _)) (insubd pk{2}) _ (insubd sig{2})).
          rewrite allP=> adrs adrsin /=; move/allP: twsrrcsp => /(_ adrs adrsin) /= [-> // | ?].
          by rewrite (reltqsadudi_rcons_qs _ _ _ _ _ (insubd pk{2}) _ (insubd sig{2})); right.
        split => [| twsr jr /lezNgt gew1em_jr _ twsrrcsp ge0_jr lew1em_jr].
        * rewrite valP !andbA ; split; last by smt(BaseW.valP).          
          rewrite -(cats1 O_THFC_Default.tws{2}) all_cat twsrcsp /=.
          split; first right.
          + rewrite /reltqsad_udi -flatten_mapP.
            exists (ad{2}, m{2}, insubd pk{2}, insubd sig{2}); split => /=; first by smt(mem_rcons).
            rewrite -flatten_mapP; exists (size pk{2}); split => /=; first by smt(mem_iota size_iota).
            pose em_ele := BaseW.val _; case (k < em_ele - 1) => ?.
            - by rewrite mapP; exists (em_ele - 2 - k); smt(BaseW.valP mem_iota size_iota).
            by rewrite neq0_em /= mapP; exists 0; smt(BaseW.valP mem_iota size_iota).
          by rewrite /cf ch0 1:validwadrs_setchidx 3:valP // valKd.
        rewrite !andbA -5!andbA; split; last by smt(size_rcons).
        rewrite (relcqsadudi_rcons_qs _ _ _ _ (DBLL.insubd (rcons _ _)) (insubd pk{2}) _ (insubd sig{2})) /=.
        by rewrite (reltqsadudi_rcons_qs _ _ _ _ _ (insubd pk{2}) _ (insubd sig{2})).
      wp; skip => |> &1 adch qsch twssp eqlen_szchal.
      rewrite -2!andbA; split; first by apply relcqsadudi_rcons_qs.
      split; first by rewrite (reltqsadudi_rcons_qs _ _ _ _ _ (insubd pk{1}) _ (insubd sig{1})).
      split => [| *]; first by smt(ge2_len).
      by move: qsch; rewrite 2!all_map /preim /= -cats1 all_cat.
    proc; inline *.
    by wp; skip => |> *; smt(allP mem_rcons).
  inline{1} 9; inline{1} 8; inline{1} 7; inline{1} 6; inline{1} 3.
  inline{2} 15; inline{2} 14; inline{2} 13; inline{2} 12.
  inline{2} 9; inline{2} 8; inline{2} 7; inline{2} 6; inline{2} 3.
  wp => /=.
  call (: true); first by sim.
  wp => /=.
  call (: true) => /=.
  wp; skip => |> &2 qsch twssp ims b. 
  rewrite eq_iff; split => [[#]| /#].
  move=> ge0_szqs led_szqs ge0_i ltszqs_i bt neqqs2_m uqpf djpf.
  rewrite !andbA andbC -!andbA 2!andbA; split => [|/#].
  split; last by apply uniq_relcqsadudi => /#.
  rewrite andbC; split; first split => [| _].
  * by smt(relcqsadudi_rng).
  * apply (IntOrder.ler_trans (size O_MEUFGCMA_WOTSTWES.qs{2} * len)); first by smt(relcqsadudi_rng).
    by rewrite ler_pmul //; smt(ge2_len).
  apply (djl_parts _ _ R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl{2} (reltqsad_udi O_MEUFGCMA_WOTSTWES.qs{2} k)) => //. 
  * by apply disj_relcqsadudi => /#.
  by apply disj_relcqsadudi_reltqsadudi => /#.
have ->:
  BRA.bigi predT (fun (i : int) => Pr[SM_DT_UD_Ci.main(i, false) @ &m : res] - Pr[SM_DT_UD_Ci.main(i, true) @ &m : res]) 0 (w - 2)
  =
  (w - 2)%r * BRA.bigi predT (fun (i : int) => Pr[SM_DT_UD_Cir.main(false) @ &m : res.`2 /\ res.`1 = i] - Pr[SM_DT_UD_Cir.main(true) @ &m : res.`2 /\ res.`1 = i]) 0 (w - 2).
+ rewrite BRA.mulr_sumr /= 2!BRA.big_int &(BRA.eq_bigr) /= => j [ge0_j ltw1_j].
  rewrite mulrBr; congr; last congr.
  - rewrite mulrC -mulr1 -eqf_div 3:divr1 3:eq_sym; first 2 by smt(val_w).
    have ->: inv ((w - 2)%r) = mu1 [0..w - 3] j by rewrite dinter1E => /#.
    byphoare (: glob A = (glob A){m} /\ b = false ==> _) => //=.
    pose pr := Pr[SM_DT_UD_Ci.main(j, false) @ &m : res].
    proc.
    seq 1: (i = j) (mu1 [0..w - 3] j) pr 1%r 0%r (glob A = (glob A){m} /\ b = false) => //=.
    * by rnd.
    * by rnd; skip.
    * call (: (glob A) = (glob A){m} /\ b = false /\ i = j ==> res) => //.
      rewrite /pr; bypr => |> &m' eq_glob -> ->.
      byequiv (: ={glob A, b, i} ==> _) => //.
      by proc; sim.
    * hoare; call (: true) => //; skip => /#.
    by rewrite mulrC.
    rewrite mulrC -mulr1 -eqf_div 3:divr1 3:eq_sym; first 2 by smt(val_w).
    have ->: inv ((w - 2)%r) = mu1 [0..w - 3] j by rewrite dinter1E => /#.
    byphoare (: glob A = (glob A){m} /\ b = true ==> _) => //=.
    pose pr := Pr[SM_DT_UD_Ci.main(j, true) @ &m : res].
    proc.
    seq 1: (i = j) (mu1 [0..w - 3] j) pr 1%r 0%r (glob A = (glob A){m} /\ b = true) => //=.
    - by rnd.
    - by rnd; skip.
    - call (: (glob A) = (glob A){m} /\ b = true /\ i = j ==> res) => //.
      rewrite /pr; bypr => |> &m' eq_glob -> ->.
      byequiv (: ={glob A, b, i} ==> _) => //.
      by proc; sim.
    - hoare; call (: true) => //; skip => /#.
  by rewrite mulrC.
rewrite normrZ 2:-BRA.sumrB; first by smt(val_w).
have indbigsplit:
  forall (i : int), 0 <= i => forall (b: bool),
    BRA.bigi predT (fun (x : int) => Pr[SM_DT_UD_Cir.main(b) @ &m : res.`2 /\ res.`1 = x]) 0 i
    =
    Pr[SM_DT_UD_Cir.main(b) @ &m : res.`2 /\ 0 <= res.`1 < i].
+ elim => [|i ge0_i ih] b. 
  - rewrite range_geq // BRA.big_nil. 
    byphoare => //; hoare.
    conseq (: _ ==> 0 <= res.`1 <= w - 2) => [/#|].
    by proc; call(: true) => //; rnd; skip; smt(supp_dinter).
  rewrite BRA.big_int_recr //= eq_sym Pr[mu_split res.`1 = i] addrC; congr.
  - rewrite ih.
    byequiv (: _ ==> ={res}) => [ | // | /#].
    by sim.
  byequiv (: _ ==> ={res}) => [ | // | /#].
  by sim.
do 3! congr; rewrite eq_sym Pr[mu_split 0 <= R_SMDTUDC_DistRCH.O_R_SMDTUDC_DistRCH.i < w - 2]; last congr.
+ rewrite eq_sym -(addr0 (BRA.bigi _ _ _ _)); congr; last first.
  - rewrite eq_sym.
    byphoare => //; hoare.
    conseq (: _ ==> 0 <= R_SMDTUDC_DistRCH.O_R_SMDTUDC_DistRCH.i < w - 2) => [/#|].
    proc; inline 4.
    seq 4 : #post; first by inline *; auto; smt(supp_dinter).
    by do ? call(: true).
  rewrite (indbigsplit (w - 2)); first by smt(val_w).
  byequiv => //.
  proc; inline{1} 2; inline{1} 7; inline{2} 4.
  swap{1} 4 -3; swap{2} 4 -2. 
  seq 10 6 : (   ={glob A, pp, R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl, O_MEUFGCMA_WOTSTWES.qs, O_SMDTUD_Default.ts, O_THFC_Default.tws}
               /\ i{1} = R_SMDTUDC_DistRCH.O_R_SMDTUDC_DistRCH.i{2}); last by wp => /=; sim.
  inline *.
  call (:   ={R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl, O_MEUFGCMA_WOTSTWES.qs, O_SMDTUD_Default.b, O_SMDTUD_Default.pp, O_SMDTUD_Default.ts, O_THFC_Default.tws, O_THFC_Default.pp}
         /\ R_SMDTUDC_DistRCHil.O_R_SMDTUDC_DistRCHil.i{1} = R_SMDTUDC_DistRCH.O_R_SMDTUDC_DistRCH.i{2}).
  - proc.
    inline *.
    seq 7 7 : (   ={m, em0, chal', ad0, ad, R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl, O_MEUFGCMA_WOTSTWES.qs, O_SMDTUD_Default.b, O_SMDTUD_Default.pp, O_SMDTUD_Default.ts, O_THFC_Default.tws, O_THFC_Default.pp}
               /\ valid_wadrs ad{1}
               /\ ad0{1} = ad{1}
               /\ R_SMDTUDC_DistRCHil.O_R_SMDTUDC_DistRCHil.i{1} = R_SMDTUDC_DistRCH.O_R_SMDTUDC_DistRCH.i{2}); last by sim.
    wp => /=.
    while (#post /\ 0 <= size chal'{1} <= len).
    * wp; sp.
      if => //=.
      + wp; sp.
        by if => //=; wp; rnd; skip => |>; smt(ge2_len size_rcons).
      wp; rnd; skip => |> &1 adch ge0_szcp _ ltlen_szcp /lezNgt geem1_i.
      by move=> cel celin; split; smt(size_rcons).
    by wp; skip => |>; smt(ge2_len WAddress.valP).
  - by proc; sim.
  by wp; rnd; rnd; skip.
rewrite eq_sym -(addr0 (BRA.bigi _ _ _ _)); congr; last first.
+ rewrite eq_sym.
  byphoare => //; hoare.
  conseq (: _ ==> 0 <= R_SMDTUDC_DistRCH.O_R_SMDTUDC_DistRCH.i < w - 2) => [/#|].
  proc; inline 4.
  seq 4 : #post; first by inline *; auto; smt(supp_dinter).
  by do ? call(: true).
rewrite (indbigsplit (w - 2)); first by smt(val_w).
byequiv => //.
proc; inline{1} 2; inline{1} 7; inline{2} 4.
swap{1} 4 -3; swap{2} 4 -2.
seq 10 6 : (   ={glob A, pp, R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl, O_MEUFGCMA_WOTSTWES.qs, O_SMDTUD_Default.ts, O_THFC_Default.tws}
               /\ i{1} = R_SMDTUDC_DistRCH.O_R_SMDTUDC_DistRCH.i{2}); last by wp => /=; sim.
inline *.
call (:   ={R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl, O_MEUFGCMA_WOTSTWES.qs, O_SMDTUD_Default.b, O_SMDTUD_Default.pp, O_SMDTUD_Default.ts, O_THFC_Default.tws, O_THFC_Default.pp}
         /\ R_SMDTUDC_DistRCHil.O_R_SMDTUDC_DistRCHil.i{1} = R_SMDTUDC_DistRCH.O_R_SMDTUDC_DistRCH.i{2}).
+ proc.
  inline *.
  seq 7 7 : (   ={m, em0, chal', ad0, ad, R_DistRCH_Game23WOTSTW.O_R_DistRCH_Game23WOTSTW_THFC.adl, O_MEUFGCMA_WOTSTWES.qs, O_SMDTUD_Default.b, O_SMDTUD_Default.pp, O_SMDTUD_Default.ts, O_THFC_Default.tws, O_THFC_Default.pp}
             /\ valid_wadrs ad{1}
             /\ ad0{1} = ad{1} 
             /\ R_SMDTUDC_DistRCHil.O_R_SMDTUDC_DistRCHil.i{1} = R_SMDTUDC_DistRCH.O_R_SMDTUDC_DistRCH.i{2}); last by sim.
  while (#post /\ 0 <= size chal'{1} <= len).
  * wp; sp.
    if => //=.
    + wp; sp.
      by if => //=; wp; rnd; skip => |>; smt(ge2_len size_rcons).
    wp; rnd; skip => |> &1 adch ge0_szcp _ ltlen_szcp /lezNgt geem1_i.
    by move=> cel celin; smt(size_rcons).
  wp; skip => |>; smt(ge2_len WAddress.valP).
+ by proc; sim.
by wp; rnd; rnd; skip.
qed.

(* Third step concluding lemma *)
local lemma Step_Game2_Game3_WOTSTWES_SMDTUDC &m :
  `|Pr[Game2_WOTSTWES.main() @ &m : res] - Pr[Game3_WOTSTWES.main() @ &m : res]|
  =
  (w - 2)%r * 
  `|Pr[SM_DT_UD_C(R_SMDTUDC_DistRCH, O_SMDTUD_Default, O_THFC_Default).main(false) @ &m : res] - 
    Pr[SM_DT_UD_C(R_SMDTUDC_DistRCH, O_SMDTUD_Default, O_THFC_Default).main(true) @ &m : res]|.
proof.
by rewrite Game2_Game3_WOTSTWES_DistRCH DistRCH_SMDTUDC.
qed.

(* Fourth step: Reduce/Bound distinguishing between Game3_WOTSTWES and Game4_WOTSTWES *)
local lemma Game3_Game4_WOTSTWES_Hchwcoll &m :
  Pr[Game3_WOTSTWES.main() @ &m : res] - Pr[Game4_WOTSTWES.main() @ &m : res]
  =
  Pr[Game3_WOTSTWES_Hchwcoll.main() @ &m : res /\ Game3_WOTSTWES_Hchwcoll.hchwcoll].
proof.
have ->: 
  Pr[Game3_WOTSTWES.main() @ &m : res] = Pr[Game3_WOTSTWES_Hchwcoll.main() @ &m : res].
+ byequiv => //. 
  proc; inline *.
  seq 12 11 : (={glob O_THFC_Default, O_MEUFGCMA_WOTSTWES.qs, ps, i, m', sig'}); last first.
  - by wp; sim : (={i, m, m', O_MEUFGCMA_WOTSTWES.qs, O_THFC_Default.tws} /\ pkWOTS0{1} = pkWOTS{2} /\ pkWOTS1{1} = pkWOTS0{2}).
  do 2! call (: ={glob O_THFC_Default, O_MEUFGCMA_WOTSTWES.qs, O_MEUFGCMA_WOTSTWES.ps}); first 2 by proc; inline *; sim.
   by auto.
rewrite Pr[mu_split Game3_WOTSTWES_Hchwcoll.hchwcoll].
have -> /#: 
  Pr[Game3_WOTSTWES_Hchwcoll.main() @ &m : res /\ !Game3_WOTSTWES_Hchwcoll.hchwcoll]
  =
  Pr[Game4_WOTSTWES.main() @ &m : res].
byequiv => //.
proc; inline *. wp.
by wp; sim :  (={i, ps, pkWOTS0, pkWOTS, ad, m, m', sig, sig', O_MEUFGCMA_WOTSTWES.qs, O_THFC_Default.tws}).
qed.

(* Fifth step: Reduce SM-DT-TCR-C of f to distinguishing between Game3_WOTSTWES and Game4_WOTSTWES *)
local lemma Step_Game3_Game4_WOTSTWES_SMDTTCRC &m :
  `|Pr[Game3_WOTSTWES.main() @ &m : res] - Pr[Game4_WOTSTWES.main() @ &m : res]|
  <=
    Pr[SM_DT_TCR_C(R_SMDTTCRC_Game34WOTSTWES(A), O_SMDTTCR_Default, O_THFC_Default).main() @ &m : res].
proof.
rewrite Game3_Game4_WOTSTWES_Hchwcoll ger0_norm 1:Pr[mu_ge0] //.
byequiv => //.
proc; inline *.
swap{2} 13 -11.
wp => /=.
seq 9 12 : (   ={glob A, ps}
            /\ pp{2} = ps{2}
            /\ O_MEUFGCMA_WOTSTWES.ps{1} = ps{1}
            /\ O_THFC_Default.pp{1} = ps{1}
            /\ O_SMDTTCR_Default.pp{2} = ps{2}
            /\ O_THFC_Default.pp{2} = ps{2}
            /\ O_MEUFGCMA_WOTSTWES.qs{1} = []
            /\ O_MEUFGCMA_WOTSTWES.qs{2} = []
            /\ R_SMDTTCRC_Game34WOTSTWES.O_R_SMDTTCRC_Game34WOTSTWES.xll{2} = []
            /\ O_THFC_Default.tws{1} = []
            /\ O_SMDTTCR_Default.ts{2} = []
            /\ O_THFC_Default.tws{2} = []).
+ by auto.
pose pkvals (qs : (adrs * msgWOTS * pkWOTS * sigWOTS) list) (ps : pseed) (i : int) :=
  all (fun (admpksig : adrs * msgWOTS * pkWOTS * sigWOTS) => 
         all (fun (j : int) =>
           let ad = admpksig.`1 in
           let em_ele = BaseW.val (encode_msgWOTS admpksig.`2).[j] in
           let sig_ele = nth witness (val admpksig.`4) j in 
             nth witness (val admpksig.`3) j 
             = 
             cf ps (set_chidx ad j) em_ele (w - 1 - em_ele) (val sig_ele)) (range 0 i)) qs.
pose sigvals (qs : (adrs * msgWOTS * pkWOTS * sigWOTS) list) (xll : dgstblock list list) (ps : pseed) (i : int) :=
  all (fun (admpksigxl : (adrs * msgWOTS * pkWOTS * sigWOTS) * dgstblock list) => 
         let (admpksig, xl) = (admpksigxl.`1, admpksigxl.`2) in
           all (fun (j : int) =>
             let ad = admpksig.`1 in
             let em_ele = BaseW.val (encode_msgWOTS admpksig.`2).[j] in
             let sig_ele = nth witness (val admpksig.`4) j in 
               sig_ele
               = 
               if em_ele <> 0
               then cf ps (set_chidx ad j) (em_ele - 1) 1 (val (nth witness xl j))
               else nth witness xl j) (range 0 i)) (zip qs xll).
seq 1 1 : (    ={glob A, glob O_THFC_Default, O_MEUFGCMA_WOTSTWES.qs, ps}
            /\ pp{2} = ps{2}
            /\ O_MEUFGCMA_WOTSTWES.ps{1} = ps{1}
            /\ O_THFC_Default.pp{1} = ps{1}
            /\ O_SMDTTCR_Default.pp{2} = ps{2}
            /\ O_THFC_Default.pp{2} = ps{2}
            /\ size O_MEUFGCMA_WOTSTWES.qs{1} = size R_SMDTTCRC_Game34WOTSTWES.O_R_SMDTTCRC_Game34WOTSTWES.xll{2}
            /\ all valid_wadrs (map (fun (admpksig : adrs * msgWOTS * pkWOTS * sigWOTS) => admpksig.`1) O_MEUFGCMA_WOTSTWES.qs{1})
            /\ pkvals O_MEUFGCMA_WOTSTWES.qs{1} O_MEUFGCMA_WOTSTWES.ps{1} len
            /\ sigvals O_MEUFGCMA_WOTSTWES.qs{1} R_SMDTTCRC_Game34WOTSTWES.O_R_SMDTTCRC_Game34WOTSTWES.xll{2} O_MEUFGCMA_WOTSTWES.ps{1} len
            /\ unzip1 O_SMDTTCR_Default.ts{2} = relcqsad_tcr O_MEUFGCMA_WOTSTWES.qs{1}
            /\ unzip2 O_SMDTTCR_Default.ts{2} = relcqsdg_tcr O_MEUFGCMA_WOTSTWES.qs{1} R_SMDTTCRC_Game34WOTSTWES.O_R_SMDTTCRC_Game34WOTSTWES.xll{2} O_MEUFGCMA_WOTSTWES.ps{1}).
+ call (:   ={glob O_THFC_Default, O_MEUFGCMA_WOTSTWES.qs}
         /\ O_MEUFGCMA_WOTSTWES.ps{1} = O_THFC_Default.pp{1}
         /\ O_THFC_Default.pp{1} = O_THFC_Default.pp{2}
         /\ O_THFC_Default.pp{2} = O_SMDTTCR_Default.pp{2}
         /\ size O_MEUFGCMA_WOTSTWES.qs{1} = size R_SMDTTCRC_Game34WOTSTWES.O_R_SMDTTCRC_Game34WOTSTWES.xll{2}
         /\ all valid_wadrs (map (fun (admpksig : adrs * msgWOTS * pkWOTS * sigWOTS) => admpksig.`1) O_MEUFGCMA_WOTSTWES.qs{1})
         /\ pkvals O_MEUFGCMA_WOTSTWES.qs{1} O_MEUFGCMA_WOTSTWES.ps{1} len
         /\ sigvals O_MEUFGCMA_WOTSTWES.qs{1} R_SMDTTCRC_Game34WOTSTWES.O_R_SMDTTCRC_Game34WOTSTWES.xll{2} O_MEUFGCMA_WOTSTWES.ps{1} len
         /\ unzip1 O_SMDTTCR_Default.ts{2} = relcqsad_tcr O_MEUFGCMA_WOTSTWES.qs{1}
         /\ unzip2 O_SMDTTCR_Default.ts{2} = relcqsdg_tcr O_MEUFGCMA_WOTSTWES.qs{1} R_SMDTTCRC_Game34WOTSTWES.O_R_SMDTTCRC_Game34WOTSTWES.xll{2} O_MEUFGCMA_WOTSTWES.ps{1}); last by auto.
  - proc; inline * => //.
    seq 6 5 : (   #pre
               /\ ={ad, pk, em}
               /\ valid_wadrs ad{1}
               /\ em{1} = encode_msgWOTS m{1}
               /\ em{2} = encode_msgWOTS m{2}
               /\ sk{1} = xl{2}
               /\ xl{2} \in ddgstblockl
               /\ pk{1} = []
               /\ pk{2} = []
               /\ sig{2} = []
               /\ size sig{1} = len
               /\ (forall (i : int), 0 <= i < len =>
                     nth witness sig{1} i 
                     = 
                     if BaseW.val em{1}.[i] <> 0
                     then cf O_MEUFGCMA_WOTSTWES.ps{1} (set_chidx ad{1} i) (BaseW.val em{1}.[i] - 1) 1 (val (nth witness sk{1} i))
                     else nth witness sk{1} i)).
    * wp => /=.
      while{1} (   valid_wadrs ad{1}
                /\ size sig{1} <= len
                /\ (forall (i : int), 0 <= i < size sig{1} =>
                      nth witness sig{1} i
                      = 
                      if BaseW.val em{1}.[i] <> 0
                      then cf O_MEUFGCMA_WOTSTWES.ps{1} (set_chidx ad{1} i) (BaseW.val em{1}.[i] - 1) 1 (val (nth witness sk{1} i))
                      else nth witness sk{1} i))
               (len - size sig{1}).
      + move=> _ z; wp; skip => |> &1 adch _ valsig ltlen_szsig.
        split=> [eq0_em | neq0_em]. 
        - rewrite andbC andbA; split; first by smt(nth_rcons size_rcons).
          move=> i ge0_i; rewrite size_rcons => ltszsig1_i.
          rewrite nth_rcons; case (i < size sig{1}) => [ltszsig_i /# | /lezNgt geszsig_i].
          by rewrite (: i = size sig{1}) 1:/# /= eq0_em.
        rewrite andbC andbA; split; first by smt(nth_rcons size_rcons).
        move=> i ge0_i; rewrite size_rcons => ltszsig1_i.
        rewrite nth_rcons; case (i < size sig{1}) => [ltszsig_i /# | /lezNgt geszsig_i].
        by rewrite (: i = size sig{1}) 1:/# /= neq0_em.
      wp; rnd; wp; skip => |> *; split; smt(ge2_len WAddress.valP).
    wp => //=.
    while (   ={glob O_THFC_Default, ad, m, pk, em, O_MEUFGCMA_WOTSTWES.qs} 
           /\ O_MEUFGCMA_WOTSTWES.ps{1} = O_THFC_Default.pp{1}
           /\ O_THFC_Default.pp{1} = O_THFC_Default.pp{2} 
           /\ O_THFC_Default.pp{2} = O_SMDTTCR_Default.pp{2}
           /\ size O_MEUFGCMA_WOTSTWES.qs{1} = size R_SMDTTCRC_Game34WOTSTWES.O_R_SMDTTCRC_Game34WOTSTWES.xll{2}
           /\ unzip1 O_SMDTTCR_Default.ts{2} 
              = 
              relcqsad_tcr O_MEUFGCMA_WOTSTWES.qs{1} 
              ++ relcqsad_tcr_outer ad{2} m{2} (size pk{2})
           /\ unzip2 O_SMDTTCR_Default.ts{2} 
              = 
              relcqsdg_tcr O_MEUFGCMA_WOTSTWES.qs{1} R_SMDTTCRC_Game34WOTSTWES.O_R_SMDTTCRC_Game34WOTSTWES.xll{2} O_MEUFGCMA_WOTSTWES.ps{1} 
              ++ relcqsdg_tcr_outer O_MEUFGCMA_WOTSTWES.ps{1} ad{2} m{2} (insubd sig{1}) xl{2} (size pk{2})
           /\ valid_wadrs ad{1} 
           /\ em{1} = encode_msgWOTS m{1} 
           /\ em{2} = encode_msgWOTS m{2} 
           /\ sk{1} = xl{2} 
           /\ xl{2} \in ddgstblockl
           /\ size pk{1} <= len
           /\ size pk{2} <= len
           /\ size sig{1} = len
           /\ size sig{2} <= len
           /\ size pk{1} = size pk{2}
           /\ size pk{2} = size sig{2} 
           /\ (forall (i : int), 0 <= i < len =>
                nth witness sig{1} i 
                =
                if (BaseW.val em{1}.[i]) <> 0 
                then cf O_MEUFGCMA_WOTSTWES.ps{1} (set_chidx ad{1} i)((BaseW.val em{1}.[i]) - 1) 1 (val (nth witness sk{1} i))
                else nth witness sk{1} i)
           /\ (forall (i : int), 0 <= i < size pk{1} =>
                nth witness pk{1} i 
                =
                cf O_MEUFGCMA_WOTSTWES.ps{1} (set_chidx ad{1} i) (BaseW.val em{1}.[i]) (w - 1 - BaseW.val em{1}.[i]) (val (nth witness sig{1} i)))
           /\ (forall (i : int), 0 <= i && i < size sig{2} =>
                 nth witness sig{1} i = nth witness sig{2} i)).
    * wp => /=.
      while{2} (   ={glob O_THFC_Default, ad, m, pk, em, O_MEUFGCMA_WOTSTWES.qs} 
                /\ O_MEUFGCMA_WOTSTWES.ps{1} = O_THFC_Default.pp{1} 
                /\ O_THFC_Default.pp{1} = O_THFC_Default.pp{2} 
                /\ O_THFC_Default.pp{2} = O_SMDTTCR_Default.pp{2}
                /\ size O_MEUFGCMA_WOTSTWES.qs{1} = size R_SMDTTCRC_Game34WOTSTWES.O_R_SMDTTCRC_Game34WOTSTWES.xll{2}
                /\ unzip1 O_SMDTTCR_Default.ts{2} 
                   = 
                   relcqsad_tcr O_MEUFGCMA_WOTSTWES.qs{1} 
                   ++ relcqsad_tcr_outer ad{2} m{2} (size pk{2})
                   ++ relcqsad_tcr_inner (set_chidx ad{2} (size pk{2})) em_ele{2} j{2}
                /\ unzip2 O_SMDTTCR_Default.ts{2} 
                   = 
                   relcqsdg_tcr O_MEUFGCMA_WOTSTWES.qs{1} R_SMDTTCRC_Game34WOTSTWES.O_R_SMDTTCRC_Game34WOTSTWES.xll{2} O_MEUFGCMA_WOTSTWES.ps{1} 
                   ++ relcqsdg_tcr_outer O_MEUFGCMA_WOTSTWES.ps{1} ad{2} m{2} (insubd sig{1}) xl{2} (size pk{2})
                   ++ relcqsdg_tcr_inner O_MEUFGCMA_WOTSTWES.ps{1} (set_chidx ad{2} (size pk{2})) em_ele{2} sig_ele{2} x{2} j{2}
                /\ valid_wadrs ad{1} 
                /\ em{1} = encode_msgWOTS m{1} 
                /\ em{2} = encode_msgWOTS m{2} 
                /\ sk{1} = xl{2} 
                /\ xl{2} \in ddgstblockl
                /\ size pk{1} < len
                /\ size pk{2} < len
                /\ size sig{1} = len
                /\ size sig{2} < len
                /\ size pk{1} = size pk{2}
                /\ size pk{2} = size sig{2} 
                /\ (forall (i : int), 0 <= i < len =>
                     nth witness sig{1} i 
                     =
                     if (BaseW.val em{1}.[i]) <> 0 
                     then cf O_MEUFGCMA_WOTSTWES.ps{1} (set_chidx ad{1} i)((BaseW.val em{1}.[i]) - 1) 1 (val (nth witness sk{1} i))
                     else nth witness sk{1} i)
                /\ (forall (i : int), 0 <= i < size pk{1} =>
                      nth witness pk{1} i 
                      =
                      cf O_MEUFGCMA_WOTSTWES.ps{1} (set_chidx ad{1} i) (BaseW.val em{1}.[i]) (w - 1 - BaseW.val em{1}.[i]) (val (nth witness sig{1} i)))  
                /\ (forall (i : int), 0 <= i && i < size sig{2} =>
                      nth witness sig{1} i = nth witness sig{2} i)
                /\ em_ele{2} = BaseW.val em{2}.[size pk{2}]
                /\ sig_ele{2} = nth witness sig{1} (size pk{2})
                /\ pk_ele{2} = cf O_SMDTTCR_Default.pp{2} (set_chidx ad{2} (size pk{2})) (em_ele{2}) j{2} (val sig_ele{2})
                /\ x{2} = nth witness xl{2} (size pk{2})
                /\ 0 <= j{2} <= w - 1 - em_ele{2})
               (w - 1 - em_ele{2} - j{2}).
      + move=> &1 z.
        wp; skip => |> &2 eq_szqsxll rcqsad rcqsdg adch skin ltlen_szpk1 ltlen_szsig1 ltlen_szsig2 eq_sz valsig1 valpk1 rsigs ge0_j lew1em_j ltw1em_j.
        rewrite !andbA -2!andbA; split => [| /#].
        split; last first.
        - rewrite /cf ch_comp 1:validwadrs_setchidx 3:valP //; first 2 by smt(BaseW.valP).
          by rewrite /cf ch1 1:validwadrs_setchidx 3:valP //; smt(BaseW.valP).
        rewrite 2!map_rcons /= rcqsad rcqsdg 2!rcons_cat; split; congr.
        - by rewrite -relcqsad_tcr_inner_rcons // /#.
        rewrite -relcqsdg_tcr_inner_rcons //; congr.
        case (BaseW.val (encode_msgWOTS m{1}).[size pk{1}] <> 0) => [neq0_em | //].
        move: (valsig1 (size pk{1}) _); first by smt(size_ge0).
        rewrite neq0_em /= => ->.
        by congr; rewrite (Ring.IntID.addrC j{2} 1) /cf ch_comp 1:validwadrs_setchidx 3:valP //; smt(BaseW.valP ge2_len).
      wp; skip => |> &1 &2 eqsz_qsxll rcqsad rcqsdg adch xlin lelen_szpk1 lelen_szsig1 lelen_szsig2 eq_sz valsig1 valpk1 rsigs ltlen_szpk2.
      split => [eq0_em | neq0_em].
      + split => [| ts j]; last split => [/# | /lezNgt gew1em_j rcqsadp rcqsdgp ltlen_szsig2 eq_nthsig ge0_j lew1em_j]. 
        - rewrite !andbA -3!andbA; split; last first.
          * by rewrite /cf ch0 1:validwadrs_setchidx 3:valP //= valKd; smt(size_ge0 BaseW.valP).
          rewrite rcqsad rcqsdg -2!catA; split; congr.
          * by rewrite /relcqsad_tcr_inner eq0_em /= /mkseq iota0 //= cats0.
          by rewrite /relcqsdg_tcr_inner eq0_em /= /mkseq iota0 //= cats0.
        rewrite !andbA -8!andbA; split; last first.
        - rewrite 4!andbA; split; first by smt(size_rcons).
          rewrite andbA; split; last by smt(size_rcons).
          split=> i ge0_i; rewrite size_rcons => ltsz1_i. 
          * rewrite nth_rcons; case (i < size pk{2}) => [/# | /lezNgt geszsig_i].
            by rewrite (: i = size pk{2}) 1:/#.
          rewrite nth_rcons; case (i < size sig{2}) => [/# | /lezNgt geszsig_i].
          by rewrite (: i = size sig{2}) /#.
        rewrite -andbA; split; first by congr => /#.
        rewrite rcqsadp rcqsdgp ?size_rcons -2!catA.
        have -> : j =  w - 1 - BaseW.val (encode_msgWOTS m{2}).[size pk{2}] by smt().
        by split; congr; smt(size_ge0 relcqsad_tcr_outer_inner_full relcqsdg_tcr_outer_inner_full DBLL.insubdK). 
      split => [| ts j]; last split => [/# | /lezNgt gew1em_j rcqsadp rcqsdgp ltlen_szsig2 eq_nthsig ge0_j lew1em_j].
      + rewrite !andbA -3!andbA; split; last first. 
        - rewrite /cf ch0 1:validwadrs_setchidx 3:valP // -eq_sz ltlen_szpk2 /=. 
          rewrite valKd /=; split; last by smt(BaseW.valP). 
          rewrite (valsig1 (size pk{2}) _) 2:neq0_em /cf; first by smt(size_ge0).
          by rewrite /cf ch1 1:validwadrs_setchidx 3:valP //; smt(size_ge0 BaseW.valP).
        rewrite 2!map_rcons /= rcqsad rcqsdg 2!rcons_cat -2!catA; split; congr.
        * by rewrite /relcqsad_tcr_inner neq0_em /= /mkseq iota1 //= cats1.
        rewrite /relcqsdg_tcr_inner neq0_em /= /mkseq iota1 //= cats1.
        by rewrite /cf ch0 1:validwadrs_setchidx 3:valP // insubdK 1:valP.
      rewrite !andbA -8!andbA; split; last first. 
      + rewrite 4!andbA; split; first by smt(size_rcons).
        rewrite andbA; split; last by smt(size_rcons).
        split=> i ge0_i; rewrite size_rcons => ltsz1_i. 
        * rewrite nth_rcons; case (i < size pk{2}) => [/# | /lezNgt geszsig_i].
          by rewrite (: i = size pk{2}) 1:/#.
        rewrite nth_rcons; case (i < size sig{2}) => [/# | /lezNgt geszsig_i].
        rewrite (: i = size sig{2}) 1:/# /= &(DigestBlock.val_inj) valsig1 1:/# -eq_sz neq0_em /=.
        by rewrite /cf ch1 1:validwadrs_setchidx 3:valP //; smt(BaseW.valP).
      rewrite -andbA; split; first by smt(size_rcons BaseW.valP).
      rewrite rcqsadp rcqsdgp ?size_rcons -2!catA.
      split; congr.
      + by rewrite -relcqsad_tcr_outer_inner_full; smt(size_ge0).
      by rewrite -relcqsdg_tcr_outer_inner_full 2:insubdK 3:-eq_nthsig; smt(size_ge0).
    wp; skip => |> &1 &2 eqsz_qsxll qsch pkvs sigvs rcqsad rcqsdg adch xlin eqlen_szsig1 valsig1.
    split => [| ts pk' sig' _ /lezNgt].
    * rewrite !andbA -4!andbA; split; last by smt(ge2_len).
      rewrite rcqsad rcqsdg /relcqsad_tcr_outer /relcqsdg_tcr_outer.
      by rewrite 2!mkseq0 2!flatten_nil 2!cats0.
    move=> gelen_szpkp rcqsadp rcqsdgp lelen_szpkp lelen_szsigp eq_sz valpk1p rsigsp.
    have eq_sigs : sig{1} = sig' by apply (eq_from_nth witness) => /#.
    rewrite eq_sigs /=; split; first by smt(size_rcons).
    rewrite !andbA -andbA; split; last first.
    * by rewrite rcqsadp rcqsdgp (: size pk' = len); smt(relcqsad_tcr_outer_full relcqsdg_tcr_outer_full).
    rewrite -andbA; split; first by smt(allP map_rcons mem_rcons).
    rewrite /pkvals /sigvals 2!allP; split => x. 
    * rewrite mem_rcons /= => -[-> | xin]; rewrite allP => i /mem_range rng_i /=; first by smt(DBLL.insubdK).
      move/allP: pkvs => hx; move: (hx x _) => //=.
      by move/allP => hi; move: (hi i _); first rewrite mem_range.
    rewrite zip_rcons // mem_rcons /= => -[-> /=| xin]; rewrite allP => i /mem_range rng_i /=; first by smt(DBLL.insubdK).
    move/allP: sigvs => hx; move: (hx x _) => //=.
    by move/allP => hi; move: (hi i _); first rewrite mem_range.
  proc; inline *.
  by wp; skip => |>.
seq 1 1 : (   #pre
           /\ ={m', sig'}
           /\ i{1} = i0{2}).
+ by call(: true); skip.
case (0 <= i{1} < size O_MEUFGCMA_WOTSTWES.qs{1}); last first.
+ conseq (: _ ==> true) => [/#| ]. 
  while{1} (true) (len - size pkWOTS0{1}); first by auto; smt(size_rcons).
  by wp; skip => |> /#.
while{1} (   #pre
          /\ valid_wadrs ad1{1}
          /\ (forall (i : int), 0 <= i < size pkWOTS0{1} =>
                nth witness pkWOTS0{1} i 
                = 
                cf ps1{1} (set_chidx ad1{1} i) (BaseW.val em0{1}.[i])
                   (w - 1 - BaseW.val em0{1}.[i]) (val (nth witness (val sig1{1}) i)))
          /\ size pkWOTS0{1} <= len)
         (len - size pkWOTS0{1}).
+ move=> &2 z.
  wp; skip => |> &1 eqsz allch pkvs sigv unz1_relcqsad unz2_relcqsdg ge0_i0 ltszqs_i0 adch valpkw _ ltlen_szpkw0.
  rewrite -!andbA; split; last by smt(size_rcons).
  move=> i ge0_i; rewrite size_rcons => ltszpkw1_i.
  rewrite nth_rcons; case (i < size pkWOTS0{1}) => [/# | /lezNgt geszpkw1_i].
  by rewrite (: i = size pkWOTS0{1}) 1:/#.
wp; skip => |> &1 eq_sz qsch pkvs sigvs rcqsad rcqsdg ge0_i0 ltszqs_i0.
split => [| pk].
+ split; last by smt(ge2_len).
  move/(all_nthP _ _ witness): qsch => /(_ i0{1} _); first by rewrite size_map. 
  by rewrite (nth_map witness) //= => adch; rewrite insubdK.
split => [/#| /lezNgt gelen_szqs3 adch pkpval lelen_szqs3 ge0_szqs led_szqs eqins_pk neqmp_qs2 uniq_qs disj_qs hchwcoll].
split.
+ by rewrite -(size_map (fun (p : adrs * dgst) => p.`1)) rcqsad; smt(relcqsadtcr_rng val_w ge2_len).
split; first by smt(uniq_relcqsadtcr allP all_map).
rewrite andbA; split; last by rewrite rcqsad &(disj_relcqsadtcr).
pose i := find_chwcollidx _ _ _ _ _ _.
pose j := find_collidx_l _ _ _ _ _ _.
pose k := find_collidx_r ps{1} (set_chidx (nth witness O_MEUFGCMA_WOTSTWES.qs{1} i0{1}).`1 i)
           (BaseW.val (encode_msgWOTS (nth witness O_MEUFGCMA_WOTSTWES.qs{1} i0{1}).`2).[i])
           (BaseW.val (encode_msgWOTS m'{1}).[i])
           (val (nth witness (val (nth witness O_MEUFGCMA_WOTSTWES.qs{1} i0{1}).`4) i))
           (val (nth witness (val sig'{1}) i)).
have rng_i: 0 <= i < len by apply hchwcoll_findchrng.
move/allP: (qsch) => qsch'; move: (qsch' ((nth witness O_MEUFGCMA_WOTSTWES.qs{1} i0{1}).`1) _) => //.
+ by rewrite mapP; exists (nth witness O_MEUFGCMA_WOTSTWES.qs{1} i0{1}); rewrite mem_nth.
move => adch_i0.
have eq_cf : 
  cf ps{1} (set_chidx (nth witness O_MEUFGCMA_WOTSTWES.qs{1} i0{1}).`1 i)
     (BaseW.val (encode_msgWOTS (nth witness O_MEUFGCMA_WOTSTWES.qs{1} i0{1}).`2).[i])
     (w - 1 - BaseW.val (encode_msgWOTS (nth witness O_MEUFGCMA_WOTSTWES.qs{1} i0{1}).`2).[i])
     (val (nth witness (val (nth witness O_MEUFGCMA_WOTSTWES.qs{1} i0{1}).`4) i)) =
  cf ps{1} (set_chidx (nth witness O_MEUFGCMA_WOTSTWES.qs{1} i0{1}).`1 i)
     (BaseW.val (encode_msgWOTS m'{1}).[i])
     (w - 1 - BaseW.val (encode_msgWOTS m'{1}).[i]) (val (nth witness (val sig'{1}) i)).
+ move: (pkpval i _); first by smt().
  rewrite /pkvals allP /= in pkvs.
  move: (pkvs (nth witness O_MEUFGCMA_WOTSTWES.qs{1} i0{1}) _); first by rewrite mem_nth => /#.
  move/allP => /= h; move: (h i _); first by rewrite mem_range.
  by move => <-; rewrite -eqins_pk insubdK 1:/#.
move/hchwcoll_hcoll /(_ _ _): (eq_cf) => // hcoll.
move/hchwcoll_findlcollrng /(_ _ _): (eq_cf) => //; rewrite -/j -/i => rng_j.
move/(nth_find witness): (hchwcoll); rewrite nth_range //= -/i; elim => ltem_emp neq_nthsig.
have neq0_em: BaseW.val (encode_msgWOTS (nth witness O_MEUFGCMA_WOTSTWES.qs{1} i0{1}).`2).[i] <> 0 by smt(BaseW.valP).
have ->:
  (nth witness O_SMDTTCR_Default.ts{1} (qsdgtcr_idx O_MEUFGCMA_WOTSTWES.qs{1} R_SMDTTCRC_Game34WOTSTWES.O_R_SMDTTCRC_Game34WOTSTWES.xll{1} ps{1} i0{1} i (j + 1))).`2
  =
  nth witness (unzip2 O_SMDTTCR_Default.ts{1}) (qsdgtcr_idx O_MEUFGCMA_WOTSTWES.qs{1} R_SMDTTCRC_Game34WOTSTWES.O_R_SMDTTCRC_Game34WOTSTWES.xll{1} ps{1} i0{1} i (j + 1)).
+ rewrite (nth_map witness witness) //.
  rewrite (: size O_SMDTTCR_Default.ts{1} = size (unzip2 O_SMDTTCR_Default.ts{1})) 1:size_map //. 
  by rewrite rcqsdg qsdgtcridx_rng // neq0_em /#.
have ->:
  nth witness (unzip2 O_SMDTTCR_Default.ts{1}) 
              (qsdgtcr_idx O_MEUFGCMA_WOTSTWES.qs{1} R_SMDTTCRC_Game34WOTSTWES.O_R_SMDTTCRC_Game34WOTSTWES.xll{1} ps{1} i0{1} i (j + 1))
  =
  val (extr_coll_l ps{1} (set_chidx (nth witness O_MEUFGCMA_WOTSTWES.qs{1} i0{1}).`1 i)
              (BaseW.val (encode_msgWOTS (nth witness O_MEUFGCMA_WOTSTWES.qs{1} i0{1}).`2).[i])
              (BaseW.val (encode_msgWOTS m'{1}).[i])
              (val (nth witness (val (nth witness O_MEUFGCMA_WOTSTWES.qs{1} i0{1}).`4) i))
              (val (nth witness (val sig'{1}) i))).
+ rewrite rcqsdg nth_relcqsdgtcr_qsdgtcridx // 1:/# neq0_em /= /extr_coll_l -/cf -/j /=. 
  rewrite (Ring.IntID.addrC j 1) /cf ch_comp 1:validwadrs_setchidx 3:valP //=; first 3 smt(BaseW.valP).
  congr; rewrite /sigvals allP /= in sigvs.
  move: (sigvs (nth (witness, witness) 
               (zip O_MEUFGCMA_WOTSTWES.qs{1} R_SMDTTCRC_Game34WOTSTWES.O_R_SMDTTCRC_Game34WOTSTWES.xll{1}) i0{1}) _). 
  - by rewrite mem_nth; smt(size_zip).
  move/allP => /= h; move: (h i _); first by rewrite mem_range.
  by rewrite ?nth_zip // neq0_em /= => ->.
have ->: 
  (nth witness O_SMDTTCR_Default.ts{1}
     (qsdgtcr_idx O_MEUFGCMA_WOTSTWES.qs{1} R_SMDTTCRC_Game34WOTSTWES.O_R_SMDTTCRC_Game34WOTSTWES.xll{1} ps{1} i0{1} i (j + 1))).`1
  =
  nth witness (unzip1 O_SMDTTCR_Default.ts{1}) (qsdgtcr_idx O_MEUFGCMA_WOTSTWES.qs{1} R_SMDTTCRC_Game34WOTSTWES.O_R_SMDTTCRC_Game34WOTSTWES.xll{1} ps{1} i0{1} i (j + 1)).
+ rewrite(nth_map witness witness) //.
  rewrite (: size O_SMDTTCR_Default.ts{1} = size (unzip2 O_SMDTTCR_Default.ts{1})) 1:size_map //. 
  by rewrite rcqsdg qsdgtcridx_rng // neq0_em /#.
have {1}-> :
  nth witness (unzip1 O_SMDTTCR_Default.ts{1}) (qsdgtcr_idx O_MEUFGCMA_WOTSTWES.qs{1} R_SMDTTCRC_Game34WOTSTWES.O_R_SMDTTCRC_Game34WOTSTWES.xll{1} ps{1} i0{1} i (j + 1))
  = 
  (set_hidx (set_chidx ((nth witness O_MEUFGCMA_WOTSTWES.qs{1} i0{1}).`1) i) ((BaseW.val (encode_msgWOTS (nth witness O_MEUFGCMA_WOTSTWES.qs{1} i0{1}).`2).[i]) + j)).
+ by rewrite rcqsad -eq_qsadtcridx_qsdgtcridx 3:nth_relcqsadtcr_qsadtcridx // neq0_em /= /#.
have {1}->: 
  nth witness (unzip1 O_SMDTTCR_Default.ts{1}) (qsdgtcr_idx O_MEUFGCMA_WOTSTWES.qs{1} R_SMDTTCRC_Game34WOTSTWES.O_R_SMDTTCRC_Game34WOTSTWES.xll{1} ps{1} i0{1} i (j + 1))
  =
  (set_hidx (set_chidx ((nth witness O_MEUFGCMA_WOTSTWES.qs{1} i0{1}).`1) i) ((BaseW.val (encode_msgWOTS m'{1}).[i]) + k)).
+ by rewrite rcqsad -eq_qsadtcridx_qsdgtcridx 3:nth_relcqsadtcr_qsadtcridx // neq0_em /= /#.
by apply collision_extraction.
qed.

(* Sixth step: Reduce/Bound success probability in Game4_WOTSTWES *)
local lemma Step_Game4_WOTSTWES_SMDTPREC &m :
  Pr[Game4_WOTSTWES.main() @ &m : res] 
  <= 
  Pr[SM_DT_PRE_C(R_SMDTPREC_Game4WOTSTWES(A), O_SMDTPRE_Default, O_THFC_Default).main() @ &m : res].
proof.
byequiv => //.
transitivity Game4_WOTSTWES_Alt.main (={glob A} ==> ={res}) (={glob A} ==> res{1} => res{2}) => [/# | // | |].
+ by apply Game4_WOTSTWES_Orig_Alt.             
proc; inline *.
swap{2} 13 -11.
wp => /=.
seq 9 12 : (   ={glob A, glob O_THFC_Default, O_MEUFGCMA_WOTSTWES.qs, ps}
            /\ pp{2} = ps{2}
            /\ O_MEUFGCMA_WOTSTWES.ps{1} = ps{1}
            /\ O_THFC_Default.pp{1} = ps{1}
            /\ O_THFC_Default.pp{2} = ps{2}
            /\ O_SMDTPRE_Default.pp{2} = ps{2}
            /\ O_MEUFGCMA_WOTSTWES.qs{1} = []
            /\ O_MEUFGCMA_WOTSTWES.qs{2} = []
            /\ O_SMDTPRE_Default.ts{2} = []
            /\ O_THFC_Default.tws{1} = []
            /\ O_THFC_Default.tws{2} = []
            /\ R_SMDTPREC_Game4WOTSTWES.O_R_SMDTPREC_Game4WOTSTWES.adl{2} = []).
+ by auto.
seq 1 1 : (   ={glob A, O_MEUFGCMA_WOTSTWES.qs, ps}
           /\ pp{2} = ps{2}
           /\ all (fun (admpksig : adrs * msgWOTS * pkWOTS * sigWOTS) => valid_wadrs admpksig.`1) O_MEUFGCMA_WOTSTWES.qs{1}
           /\ unzip1 O_SMDTPRE_Default.ts{2} = relcqsad_pre O_MEUFGCMA_WOTSTWES.qs{1}
           /\ unzip2 O_SMDTPRE_Default.ts{2} = relcqsdg_pre O_MEUFGCMA_WOTSTWES.qs{1}
           /\ (uniq_wgpidxs (map (fun (admpksig : adrs * msgWOTS * pkWOTS * sigWOTS) => admpksig.`1) 
                 O_MEUFGCMA_WOTSTWES.qs{1})
               => 
               disj_wgpidxs (map (fun (admpksig : adrs * msgWOTS * pkWOTS * sigWOTS) => admpksig.`1) 
                 O_MEUFGCMA_WOTSTWES.qs{1}) O_THFC_Default.tws{1} 
               => 
               disj_lists (unzip1 O_SMDTPRE_Default.ts{2}) O_THFC_Default.tws{2})).
+ call (:   ={O_MEUFGCMA_WOTSTWES.qs, O_THFC_Default.pp}
         /\ O_MEUFGCMA_WOTSTWES.ps{1} = O_SMDTPRE_Default.pp{2}
         /\ O_THFC_Default.pp{1} = O_SMDTPRE_Default.pp{2}
         /\ all (fun (admpksig : adrs * msgWOTS * pkWOTS * sigWOTS) => valid_wadrs admpksig.`1) O_MEUFGCMA_WOTSTWES.qs{1}
         /\ unzip1 O_SMDTPRE_Default.ts{2} = relcqsad_pre O_MEUFGCMA_WOTSTWES.qs{1}
         /\ unzip2 O_SMDTPRE_Default.ts{2} = relcqsdg_pre O_MEUFGCMA_WOTSTWES.qs{1}
         /\ R_SMDTPREC_Game4WOTSTWES.O_R_SMDTPREC_Game4WOTSTWES.adl{2} = reltqsad_pre O_MEUFGCMA_WOTSTWES.qs{1}
         /\ (forall ad, ad \in O_THFC_Default.tws{2} => 
               ad \in O_THFC_Default.tws{1} \/ ad \in R_SMDTPREC_Game4WOTSTWES.O_R_SMDTPREC_Game4WOTSTWES.adl{2})); last first.
  - skip => |> _ _ _ tws qs ts tws' qsch rcqsad rcqsdg twspmem uqpfqs /hasPn djpfqs.
    apply (djl_parts _ _ tws (reltqsad_pre qs)); first by rewrite allP.
    * rewrite hasPn => ad; rewrite rcqsad /relcqsad_pre -flatten_mapP => -[q] [qin /=].
      move/flatten_mapP => -[i] [] /mem_iota [ge0_i /= ltlen_i].
      case (BaseW.val (encode_msgWOTS q.`2).[i] <> 0) => //= neq0_em adval.
      move: (djpfqs (get_wgpidxs ad)).
      rewrite -map_comp /(\o) /= => /(_ _). 
      + by rewrite mapP; exists q; rewrite qin /= adval eq_gp_setchhidx //; smt(allP BaseW.valP).
      by apply /contra /map_f.
    by rewrite rcqsad disj_relcqsadpre_reltqsadpre 1:all_map.
  - proc; inline *.
    swap{1} 6 -2.
    sp; wp => /=.
    while{1} (   0 <= size pk{1} <= len
              /\ valid_wadrs ad{1}
              /\ (forall (i : int), 0 <= i < size pk{1} =>
                    let em_ele = BaseW.val em{1}.[i] in
                    let sig_ele = nth witness sig{1} i in
                    nth witness pk{1} i
                    =
                    cf O_MEUFGCMA_WOTSTWES.ps{1} (set_chidx ad{1} i) 
                      em_ele (w - 1 - em_ele) (val sig_ele)))
             (len - size pk{1}).
    * move=> _ z.
      wp; skip => |> &1 ge0_szpk _ adch valpk ltlen_szpk.
      rewrite andbC !andbA; split; first by smt(size_rcons).
      move=> i ge0_i; rewrite size_rcons => ltszpk1_i.
      rewrite nth_rcons; case (i < size pk{1}) => [/# | /lezNgt geszpk1_i].
      by rewrite (: i = size pk{1}) 1:/#.
    while (   ={ad, m, em, sig}
           /\ valid_wadrs ad{2} 
           /\ em{1} = encode_msgWOTS m{1}
           /\ em{2} = encode_msgWOTS m{2}
           /\ O_MEUFGCMA_WOTSTWES.ps{1} = O_SMDTPRE_Default.pp{2}
           /\ O_THFC_Default.pp{1} = O_SMDTPRE_Default.pp{2}
           /\ unzip1 O_SMDTPRE_Default.ts{2} 
              = 
              relcqsad_pre O_MEUFGCMA_WOTSTWES.qs{1} ++ relcqsad_pre_outer ad{2} m{2} (size pk{2})
           /\ unzip2 O_SMDTPRE_Default.ts{2} 
              = 
              relcqsdg_pre O_MEUFGCMA_WOTSTWES.qs{1} ++ relcqsdg_pre_outer m{2} sig{2} (size pk{2})
           /\ R_SMDTPREC_Game4WOTSTWES.O_R_SMDTPREC_Game4WOTSTWES.adl{2}
              =
              reltqsad_pre O_MEUFGCMA_WOTSTWES.qs{1} ++ reltqsad_pre_outer ad{2} m{2} (size pk{2})
           /\ size sig{1} = size pk{2}
           /\ (forall (ad : adrs), ad \in O_THFC_Default.tws{2} =>
                ad \in O_THFC_Default.tws{1} \/
                ad \in R_SMDTPREC_Game4WOTSTWES.O_R_SMDTPREC_Game4WOTSTWES.adl{2})
           /\ 0 <= size sig{1} <= len
           /\ 0 <= size pk{2} <= len
           /\ (forall (i : int), 0 <= i < size pk{2} =>
                let em_ele = BaseW.val em{2}.[i] in
                let sig_ele = nth witness sig{2} i in
                nth witness pk{2} i
                =
                cf O_THFC_Default.pp{2} (set_chidx ad{2} i) 
                  em_ele (w - 1 - em_ele) (val sig_ele))).
    * wp => /=.
      while{2} (   ={ad}
                /\ valid_wadrs ad{2}
                /\ pk_ele{2} 
                   = 
                   cf O_THFC_Default.pp{2} (set_chidx ad{2} (size pk{2})) em_ele{2} j{2} (val sig_ele{2})
                /\ em_ele{2} = BaseW.val em{2}.[size pk{2}]
                /\ R_SMDTPREC_Game4WOTSTWES.O_R_SMDTPREC_Game4WOTSTWES.adl{2}
                   =
                   reltqsad_pre O_MEUFGCMA_WOTSTWES.qs{1} 
                   ++ reltqsad_pre_outer ad{2} m{2} (size pk{2})
                   ++ reltqsad_pre_inner (set_chidx ad{2} (size pk{2})) em_ele{2} j{2}
                /\ size sig{1} = size pk{2}
                /\ (forall (ad : adrs), ad \in O_THFC_Default.tws{2} =>
                     ad \in O_THFC_Default.tws{1} \/
                     ad \in R_SMDTPREC_Game4WOTSTWES.O_R_SMDTPREC_Game4WOTSTWES.adl{2})
                /\ size sig{2} = size pk{2}
                /\ 0 <= size pk{2} < len
                /\ 0 <= j{2} <= w - 1 - em_ele{2})
               (w - 1 - em_ele{2} - j{2}).
      + move=> &1 z.
        wp; skip => |> &2 adch eq_sz1 twsmem eq_sz2 ge0_szpk ltlen_szpk ge0_j lew1em_j ltw1em_j.
        rewrite !andbA -2!andbA; split => [| /#].
        split => [| ad']; last by rewrite 2!mem_rcons /= => /#.
        split; first by rewrite valP -/f eq_sym /cf chS 1:validwadrs_setchidx 3:valP //; smt(BaseW.valP).
        by rewrite rcons_cat reltqsad_pre_inner_rcons.
      sp; if{2} => //=.
      + wp; rnd; skip => |> &1 &2 adch rcqsad rcqsdg eq_sz twsmem ge0_szsig lelen_szsig ge0_szpk lelen_szpk valpk ltlen_szsig ltlen_szpk eq0_em.
        move=> cel celin. 
        rewrite /cf ch0 1:validwadrs_setchidx 3:valP // valKd /=.
        rewrite {1}/reltqsad_pre_inner mkseq0 cats0 /=.
        split => [| tws' j]; first by smt(BaseW.valP).
        split => [/# | /lezNgt gew1em_j twspmem ge0_j lew1em_j].
        rewrite eq_sz eq0_em /=; split; last by smt(size_rcons).
        rewrite !andbA andbC -!andbA 3!andbA; split; last by smt(size_rcons nth_rcons).
        split; last first.
        - rewrite -catA -eq0_em; congr.
          have ->: j =  w - 1 - BaseW.val (encode_msgWOTS m{2}).[size pk{2}] by smt().
          by rewrite size_rcons reltqsad_pre_outer_inner_full.
        rewrite -andbA; split. 
        - move=> i ge0_i; rewrite size_rcons => ltszpk1_i.
          rewrite ?nth_rcons ?eq_sz; case (i < size pk{2}) => [/# | /lezNgt geszpk1_i].
          by rewrite (: i = size pk{2}) /#.
        rewrite rcqsad rcqsdg size_rcons /=; split; congr.
        - rewrite /relcqsad_pre_outer /mkseq iota_add //= map_cat iota1 /=.
          by rewrite flatten_cat flatten_seq1 eq0_em /= cats0.
        rewrite /relcqsdg_pre_outer /mkseq iota_add //= map_cat iota1 /=.
        rewrite flatten_cat flatten_seq1 eq0_em /= cats0.
        congr; rewrite -eq_in_map => i /mem_iota [ge0_i /= ltszpk_i] /=.
        by rewrite nth_rcons eq_sz ltszpk_i.
      wp; rnd DigestBlock.val DigestBlock.insubd.
      wp; skip => |> &1 &2 adch rcqsad rcqsdg eq_sz twsmem ge0_szsig lelen_szsig ge0_szpk lelen_szpk valpk ltlen_szsig ltlen_szpk neq0_em.
      split => [x xin | _].
      + by rewrite insubdK; move/supp_dmap: xin => -[x' [_ ->]]; first rewrite valP.
      split => [x xin | _]; first apply in_dmap1E_can.
      + by rewrite insubdK; move/supp_dmap: xin => -[x' [_ ->]]; first rewrite valP. 
      + by move=> ce' cepin <-; rewrite valKd.
      move=> cel celin; split => [| _]; first by apply dmap_supp.
      rewrite valKd /= /cf ch0 1:validwadrs_setchidx 3:valP //= {1}/reltqsad_pre_inner mkseq0 cats0 valKd /=.
      split => [| tws' j]; first by smt(BaseW.valP).
      split => [/# | /lezNgt gew1em_j twspmem ge0_j lew1em_j].
      split => [/# | neq0p_em].
      rewrite !andbA -andbA; split; last by smt(size_rcons).
      rewrite andbC !andbA -4!andbA; split; last by smt(size_rcons).
      rewrite -!andbA; split.
      - move=> i ge0_i; rewrite size_rcons => ltszpk1_i.
        rewrite ?nth_rcons ?eq_sz; case (i < size pk{2}) => [/# | /lezNgt geszpk1_i].
        by rewrite (: i = size pk{2}) /#.
      rewrite !andbA; split; last by rewrite -catA size_rcons /=; congr; smt(reltqsad_pre_outer_inner_full).
      rewrite -!andbA; split.
      + by congr; rewrite eq_sz /cf ch1 1:validwadrs_setchidx 3:valP //; smt(BaseW.valP).
      rewrite 2!map_rcons size_rcons rcqsad rcqsdg 2!rcons_cat /=; split; congr.
      + rewrite /relcqsad_pre_outer /mkseq iota_add //= map_cat flatten_cat iota1 /=.
        by rewrite flatten_seq1 neq0_em /= cats1.
      rewrite /relcqsdg_pre_outer /mkseq iota_add //= map_cat flatten_cat iota1 /=.
      rewrite neq0_em /= nth_rcons eq_sz /= flatten_seq1 cats1; congr.
      congr; rewrite -eq_in_map => i /mem_iota [ge0_i /= ltlszpk_i].
      rewrite nth_rcons eq_sz; case (BaseW.val (encode_msgWOTS m{2}).[i] <> 0) => _ //.
      by have ->: i < size pk{2} by smt().
    skip => |> &1 &2 qsch rcqsad rcqsdg twsmem.
    split => [| ts tws pk sig /lezNgt gelen_szsig /lezNgt gelen_szpk _ rcqsadts rcqsdgts eq_sz twspmem ge0_szsig lelen_szsig ge0_szpk lelen_szpk valpk].
    * rewrite rcqsad rcqsdg /relcqsad_pre_outer /relcqsdg_pre_outer /reltqsad_pre_outer.
      by rewrite 3!mkseq0 2!flatten_nil 3!cats0 /=; smt(ge2_len WAddress.valP).
    split => [/# | pk']; split => [/# | /lezNgt gelen_pkp ge0_pkp lelen_pkp valpkp].
    have -> /=: pk = pk'.
    * apply (eq_from_nth witness) => [/# | i rng_i].
      by apply DigestBlock.val_inj => /#.
    rewrite rcqsadts rcqsdgts (: size pk = len) 1:/# (: size pk' = len) 1:/#. 
    rewrite -relcqsad_pre_outer_full -relcqsdg_pre_outer_full -reltqsad_pre_outer_full insubdK 1:/# /=.
    by rewrite allP => q; rewrite mem_rcons /= => -[-> |] //=; smt(allP WAddress.valP).
  proc; inline *.
  wp; skip => |> &1 &2 qsch rcqsad rcqsdg twsmem ad.
  rewrite mem_rcons /= => -[->| adin]; first by left; rewrite mem_rcons.
  by move: (twsmem ad adin); rewrite mem_rcons /#.
seq 1 1 : (#pre /\ ={m', sig'} /\ i{1} = i0{2}).
+ by call (: true).
while{1} (true) (len - size pkWOTS0{1}).
+ move=> _ z.
  by wp; skip; smt(size_rcons).
wp; skip => |> &1 &2 qsch rcqsad rcqsdg uqpfdjpf_impl_djl pk'.  
split => [/# | /lezNgt gelen_szq3 ge1_szqs led_szqs ge0_i0 ltszqs_i0 eqins_pkp neqq2_mp uqpf djpf nhchwcoll].
split; first by smt(size_map relcqsadpre_rng ge2_len). 
split; first by rewrite rcqsad uniq_relcqsadpre 1:all_map.
split => [| /#].
pose q := nth witness O_MEUFGCMA_WOTSTWES.qs{2} i0{2}; rewrite eq_sym in neqq2_mp.
move/(nhchwcoll_hchwpre ps{2} q.`1 _ _ q.`4 sig'{2}) /(_ _): (neqq2_mp) => //.
move=> hchwpre; rewrite eq_sym; pose qsdgidx := qsdgpre_idx _ _ _.
rewrite -(nth_map witness witness snd qsdgidx O_SMDTPRE_Default.ts{2}).
+ rewrite -(size_map (fun (p : _ * _) => p.`2)) rcqsdg qsdgpreidx_rng 2:/#.
  - by apply hchwpre_neq0_findchwpre.
  by apply hchwpre_findprerng.
rewrite rcqsdg /tsdgidx nth_relcqsdgpre_qsdgpreidx 2:/#.
+ by apply hchwpre_neq0_findchwpre.
+ by apply hchwpre_findprerng.
move/(nth_find witness): (hchwpre); rewrite /extr_pre -/cf /find_chwpreidx.
pose fchw := find%List _ _; rewrite /is_chwpre -/cf nth_range /= => [ | [lem <-]].
+ by apply hchwpre_findprerng.
rewrite /cf chS 1:validwadrs_setchidx 3:valP //; first 5 smt(all_nthP BaseW.valP).
rewrite -(nth_map witness witness fst qsdgidx O_SMDTPRE_Default.ts{2}).
+ rewrite -(size_map (fun (p : _ * _) => p.`2)) rcqsdg qsdgpreidx_rng 2:/#.
  - by apply hchwpre_neq0_findchwpre.
  by apply hchwpre_findprerng.  
rewrite rcqsad /qsdgidx -eq_qsadpreidx_qsdgpreidx 1:/#.
rewrite -/q -/fchw nth_relcqsadpre_qsadpreidx 2,4:/# //. 
+ by apply hchwpre_neq0_findchwpre.
by apply hchwpre_findprerng.
qed.

(* Penultimate lemma comprising complete security proof without initial (PRF-reduction) step *)
lemma MEUFGCMA_WOTSTWES_NOPRF &m :
     Pr[M_EUF_GCMA_WOTSTWES(A, O_MEUFGCMA_WOTSTWES_NOPRF, O_THFC_Default).main() @ &m : res] 
  <=    (w - 2)%r
        * `|Pr[SM_DT_UD_C(R_SMDTUDC_Game23WOTSTWES(A), O_SMDTUD_Default, O_THFC_Default).main(false) @ &m : res]
            - Pr[SM_DT_UD_C(R_SMDTUDC_Game23WOTSTWES(A), O_SMDTUD_Default, O_THFC_Default).main(true) @ &m : res]| 
     + Pr[SM_DT_TCR_C(R_SMDTTCRC_Game34WOTSTWES(A), O_SMDTTCR_Default, O_THFC_Default).main() @ &m : res] 
     + Pr[SM_DT_PRE_C(R_SMDTPREC_Game4WOTSTWES(A), O_SMDTPRE_Default, O_THFC_Default).main() @ &m : res].
proof.
have ^ -> ->: 
  forall b, 
    Pr[SM_DT_UD_C(R_SMDTUDC_Game23WOTSTWES(A), O_SMDTUD_Default, O_THFC_Default).main(b) @ &m: res]
    = 
    Pr[SM_DT_UD_C(R_SMDTUDC_DistRCH, O_SMDTUD_Default, O_THFC_Default).main(b) @ &m: res].
+ by move=> b; byequiv=> //; sim.
have ->:
  Pr[M_EUF_GCMA_WOTSTWES(A, O_MEUFGCMA_WOTSTWES_NOPRF, O_THFC_Default).main() @ &m : res]
  =
  Pr[Game2_WOTSTWES.main() @ &m : res].
+ by byequiv MEUFGCMA_WOTSTWES_NOPRF_Game2_WOTSTWES. 
have ->:
  Pr[Game2_WOTSTWES.main() @ &m : res]
  =
  `|Pr[Game2_WOTSTWES.main() @ &m : res] - 
    Pr[Game4_WOTSTWES.main() @ &m : res] +
    Pr[Game4_WOTSTWES.main() @ &m : res]|.
+ smt(ge0_mu).
apply (ler_trans (  `|Pr[Game2_WOTSTWES.main() @ &m : res] -
                      Pr[Game4_WOTSTWES.main() @ &m : res]|
                  +   Pr[Game4_WOTSTWES.main() @ &m : res])).
+ rewrite -{4}(ger0_norm Pr[Game4_WOTSTWES.main() @ &m : res]). 
  - by rewrite Pr[mu_ge0]. 
  by apply ler_norm_add.
apply (ler_trans (  `|Pr[Game2_WOTSTWES.main() @ &m : res] - 
                      Pr[Game3_WOTSTWES.main() @ &m : res]|
                  + `|Pr[Game3_WOTSTWES.main() @ &m : res] - 
                      Pr[Game4_WOTSTWES.main() @ &m : res]|
                  +   Pr[Game4_WOTSTWES.main() @ &m : res])).
+ by rewrite ler_add 1:ler_dist_add.
rewrite ler_add 1:ler_add.
+ by rewrite Step_Game2_Game3_WOTSTWES_SMDTUDC.
+ by apply Step_Game3_Game4_WOTSTWES_SMDTTCRC.
by apply Step_Game4_WOTSTWES_SMDTPREC.
qed.

(* Security theorem: Combine previous steps to derive security theorem *)
lemma MEUFGCMA_WOTSTWES &m :
    Pr[M_EUF_GCMA_WOTSTWES(A, O_MEUFGCMA_WOTSTWES, O_THFC_Default).main() @ &m : res] 
    <=
  `|Pr[PRF(R_PRF_Game0NOPRFWOTSTWES(A), O_PRF_Default).main(false) @ &m : res] - 
    Pr[PRF(R_PRF_Game0NOPRFWOTSTWES(A), O_PRF_Default).main(true) @ &m : res]|
    +
   (w - 2)%r * 
  `|Pr[SM_DT_UD_C(R_SMDTUDC_Game23WOTSTWES(A), O_SMDTUD_Default, O_THFC_Default).main(false) @ &m : res] - 
    Pr[SM_DT_UD_C(R_SMDTUDC_Game23WOTSTWES(A), O_SMDTUD_Default, O_THFC_Default).main(true) @ &m : res]| 
    +
    Pr[SM_DT_TCR_C(R_SMDTTCRC_Game34WOTSTWES(A), O_SMDTTCR_Default, O_THFC_Default).main() @ &m : res] 
    +
    Pr[SM_DT_PRE_C(R_SMDTPREC_Game4WOTSTWES(A), O_SMDTPRE_Default, O_THFC_Default).main() @ &m : res].
proof.
move: (MEUFGCMA_WOTSTWES_NOPRF &m) => thm_nprf.
have ->:
  Pr[M_EUF_GCMA_WOTSTWES(A, O_MEUFGCMA_WOTSTWES, O_THFC_Default).main() @ &m : res] 
  = 
  Pr[Game0_WOTSTWES.main() @ &m : res].
+ by byequiv MEUFGCMA_Game0_WOTSTWES.
have ->:
  Pr[Game0_WOTSTWES.main() @ &m : res]
  =
  `|Pr[Game0_WOTSTWES.main() @ &m : res] - 
    Pr[M_EUF_GCMA_WOTSTWES(A, O_MEUFGCMA_WOTSTWES_NOPRF, O_THFC_Default).main() @ &m : res] + 
    Pr[M_EUF_GCMA_WOTSTWES(A, O_MEUFGCMA_WOTSTWES_NOPRF, O_THFC_Default).main() @ &m : res]|.
+ by smt(ge0_mu).
apply (ler_trans (  `|Pr[Game0_WOTSTWES.main() @ &m : res] -
                      Pr[M_EUF_GCMA_WOTSTWES(A, O_MEUFGCMA_WOTSTWES_NOPRF, O_THFC_Default).main() @ &m : res]|
                  +   Pr[M_EUF_GCMA_WOTSTWES(A, O_MEUFGCMA_WOTSTWES_NOPRF, O_THFC_Default).main() @ &m : res])).
+ rewrite -{4}(ger0_norm Pr[M_EUF_GCMA_WOTSTWES(A, O_MEUFGCMA_WOTSTWES_NOPRF, O_THFC_Default).main() @ &m : res]). 
  - by rewrite Pr[mu_ge0].
  by apply ler_norm_add.
by rewrite -2!addrA ler_add 1:Step_Game0_MEUFGCMA_WOTSTWES_NOPRF_PRF // addrA.
qed.

end section Proof_M_EUF_GCMA_WOTSTWES.
