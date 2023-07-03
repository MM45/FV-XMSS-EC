(* --- Require/Import --- *)
require import AllCore IntDiv List StdOrder.
require (*--*) Subtype.
(*---*) import IntOrder.



(* --- Checksum (slightly more generic than necessary, instantiated below) --- *)
theory Checksum.
  op w : { int | 0 < w } as gt0_w.

  clone import Subtype as BaseW with
    type T   <= int,
      op P x <= 0 <= x < w
    rename [type] "sT" as "baseW".

  op int2lbw (l n : int) =
    mkseq (fun (i : int) => BaseW.insubd ((n %/ w ^ (l - 1 - i)) %% w)) l.

  lemma int2lbw0 (n : int): int2lbw 0 n = [].
  proof. by rewrite /int2lbw mkseq0. qed.

  lemma int2lbwS (l n : int):
       0 <= l
    => 0 <= n
    => int2lbw (l + 1) n = rcons (int2lbw l (n %/ w)) (BaseW.insubd (n %% w)).
  proof.
  move=> ge0_l ge0_n.
  rewrite /int2lbw mkseqS //= expr0 divz1. 
  congr; apply eq_in_mkseq => i rng_i /=.
  do 3! congr; rewrite -divz_mul; 1: by smt(gt0_w).
  by rewrite -{2}(Ring.IntID.expr1 w) -exprD_nneg // /#.
  qed.

  op bw2int (ms : baseW list) =
  with ms = []      => 0
  with ms = m :: ms => BaseW.val m * w ^ (size ms) + bw2int ms.

  lemma size_int2lbw l n:
       0 <= l
    => 0 <= n
    => size (int2lbw l n) = l.
  proof.
  move=> ge0_l; elim: l ge0_l n.
  + by move=> n; rewrite int2lbw0.
  move=> l ge0_l ih n ge0_n; rewrite int2lbwS // size_rcons ih //.
  smt(gt0_w).
  qed.

  lemma bw2int_ge0 ms: 0 <= bw2int ms.
  proof.
  elim: ms=> //= m ms ih.
  apply: addr_ge0=> //.
  apply: mulr_ge0.
  + smt(BaseW.valP).
  by apply/expr_ge0; smt(gt0_w).
  qed.

  lemma bw2int_lt_exp_w_l ms: bw2int ms < w ^ (size ms).
  proof.
  elim: ms=> //=.
  + by rewrite expr0.
  move=> m ms ih.
  apply: (ler_lt_trans ((w - 1) * w ^ (size ms) + (w ^ (size ms) - 1))).
  + apply: ler_add.
    apply: ler_wpmul2r.
    + smt(bw2int_ge0).
    + smt(BaseW.valP).
    + smt().
  by rewrite mulzDl (addzC 1) exprS 1:size_ge0 /#.
  qed.

  lemma bw2int_rcons ms m:
    bw2int (rcons ms m) = BaseW.val m + w * bw2int ms.
  proof.
  elim: ms=> //= [|m' ms ih].
  + by rewrite expr0.
  by rewrite ih size_rcons exprS 1:size_ge0 /#.
  qed.

  lemma int2lbwK (l n : int):
       0 <= l
    => 0 <= n < w ^ l
    => bw2int (int2lbw l n) = n.
  proof.
  move=> ge0_l; elim: l ge0_l n.
  + by move=> n; rewrite int2lbw0 expr0 /#.
  move=> l ge0_l ih n [] ge0_n lt_n_wSl.
  rewrite int2lbwS // bw2int_rcons BaseW.insubdK 1:#smt:(BaseW.valP gt0_w).
  rewrite ih; 2:smt(gt0_w).
  by rewrite ltz_divLR 1:#smt:(gt0_w) mulzC -exprS #smt:(gt0_w).
  qed.

  lemma bw2intK (ms : baseW list):
    int2lbw (size ms) (bw2int ms) = ms.
  proof.
  elim/last_ind: ms=> //= [|ms m ih].
  + by rewrite int2lbw0.
  rewrite bw2int_rcons size_rcons //= int2lbwS 1:size_ge0.
  + smt(BaseW.valP gt0_w bw2int_ge0).
  rewrite mulzC modzMDr pmod_small 1:#smt:(BaseW.valP) BaseW.valKd.
  rewrite divzMDr 1:#smt:(gt0_w) pdiv_small 1:#smt:(BaseW.valP) /=.
  by rewrite ih.
  qed.

  lemma leq_all l m n:
       0 <= l
    => 0 <= m < w ^ l
    => 0 <= n < w ^ l
    => (forall i, 0 <= i < l => BaseW.val (nth witness (int2lbw l m) i) <= BaseW.val (nth witness (int2lbw l n) i))
    => m <= n.
  proof.
  move=> ge0_l; elim: l ge0_l m n.
  + by move=> m n; rewrite expr0 !int2lbw0 /#.
  move=> l ge0_l ih m n [] ge0_m lt_m_wSl [] ge0_n lt_n_wSl Hleq.
  rewrite (divz_eq m w) (divz_eq n w).
  apply: ler_add.
  + apply: ler_wpmul2r; 1:smt(gt0_w).
    apply: ih.
    + by rewrite ltz_divLR 1:#smt:(gt0_w) mulzC -exprS //; smt(gt0_w).
    + by rewrite ltz_divLR 1:#smt:(gt0_w) mulzC -exprS //; smt(gt0_w).
    move=> i [] ge0_i lt_i_l; move: (Hleq i _); 1:smt().
    rewrite !int2lbwS 1..4://#.
    rewrite nth_rcons size_int2lbw // 1:#smt:(gt0_w) lt_i_l /=.
    by rewrite nth_rcons size_int2lbw // 1:#smt:(gt0_w) lt_i_l.
  move: (Hleq l _)=> //=.
  + smt().
  rewrite !int2lbwS 1..4://#.
  rewrite nth_rcons size_int2lbw // 1:#smt:(gt0_w) /= BaseW.insubdK 1:#smt:(gt0_w).
  by rewrite nth_rcons size_int2lbw // 1:#smt:(gt0_w) /= BaseW.insubdK 1:#smt:(gt0_w).
  qed.

  require StdBigop.
  import StdBigop.Bigint StdBigop.Bigint.BIA.

  op checksum (l1 n l2 : int) =
    let n_bw = int2lbw l1 n in
    let wcs  = big predT (fun nw => w - 1 - BaseW.val nw) n_bw in
    int2lbw l2 wcs.

  lemma big_pos_eq0 (P : 'a -> bool) F s:
       (forall x, x \in filter P s => 0 <= F x)
    => (big P F s = 0 <=> forall x, x \in filter P s => F x = 0).
  proof.
  move=> H; split; last first.
  + move=> {H} H; apply: big1_seq=> x; rewrite -mem_filter; exact: H.
  elim: s H=> //= x xs ih H.
  rewrite big_cons=> //=; case: (P x) H=> /=; last by exact: ih.
  move=> Hleq; rewrite paddr_eq0=> [| |[]].
  + by apply: (Hleq x).
  + by apply: sumr_ge0_seq=> x0 x0_in_xs P_x0; apply: Hleq; rewrite mem_filter x0_in_xs P_x0.
  move=> + + x0; case: (x0 = x)=> /> _ _ Hbig x0_in_Ps.
  apply: ih=> //.
  by move=> x' x'_in_Ps; apply: Hleq; rewrite x'_in_Ps.
  qed.

  lemma big_neg_eq0 (P : 'a -> bool) F s:
       (forall x, x \in filter P s => F x <= 0)
    => (big P F s = 0 <=> forall x, x \in filter P s => F x = 0).
  proof.
  move=> H; rewrite -oppr_eq0 sumrN.
  rewrite -(forall_iff (fun x=> x \in filter P s => -F x = 0)).
  + by move=> x /=; rewrite oppr_eq0.
  by apply: big_pos_eq0=> x /H /= /#.
  qed.

  lemma eq_all l m n:
       0 <= l
    => 0 <= m < w ^ l
    => 0 <= n < w ^ l
    => (forall i, 0 <= i < l =>
            BaseW.val (nth witness (int2lbw l m) i)
          = BaseW.val (nth witness (int2lbw l n) i))
    => m = n.
  proof.
  move=> ge0_l Hm Hn Heq; apply: ler_asym; split=> [|_].
  + by apply: (leq_all l m n ge0_l Hm Hn)=> i /Heq ->.
  + by apply: (leq_all l n m ge0_l Hn Hm)=> i /Heq ->.
  qed.

  lemma size_checksum l1 n l2:
       0 <= l1
    => 0 <= n
    => 0 <= l2
    => size (checksum l1 n l2) = l2.
  proof.
  move=> ge0_l1 ge0_n ge0_l2.
  rewrite /checksum /= size_int2lbw //.
  by rewrite sumr_ge0_seq; smt(BaseW.valP).
  qed.

  lemma checksum_prop l1 l2 x x':
       0 <= l1
    => 0 <= l2
    => (w - 1) * l1 < w ^ l2
    => 0 <= x  < w ^ l1
    => 0 <= x' < w ^ l1
    => (forall i, 0 <= i < l1 => BaseW.val (nth witness (int2lbw l1 x) i) <= BaseW.val (nth witness (int2lbw l1 x') i))
    => (forall i, 0 <= i < l2 => BaseW.val (nth witness (checksum l1 x l2) i) <= BaseW.val (nth witness (checksum l1 x' l2) i))
    => x = x'.
  proof.
  move=> ge0_l1 ge0_l2 l1_l2 [] ge0_x lt_x_wl1 [] ge0_x' lt_x'_wl2 Hxx' Hcc'.
  apply: (eq_all l1)=> //= i Hi.
  rewrite -Ring.IntID.subr_eq0.
  have {Hi}: i \in filter predT (range 0 l1).
  + by rewrite mem_filter mem_range.
  move: i; rewrite -big_neg_eq0.
  + by move=> i; rewrite mem_filter mem_range /predT //= /Hxx' /#.
  apply: ler_asym; split=> [|_].
  + apply: oppr_ge0; rewrite sumrN.
    by apply: sumr_ge0_seq=> i /mem_range /Hxx' /#.
  move: (leq_all l2 (bw2int (checksum l1 x l2)) (bw2int (checksum l1 x' l2)) _ _ _ _)=> //.
  (** Lemmify and clean up **)
  + rewrite bw2int_ge0 /= -{2}(size_checksum l1 x l2) //.
    by rewrite bw2int_lt_exp_w_l.
  + rewrite bw2int_ge0 /= -{2}(size_checksum l1 x' l2) //.
    by rewrite bw2int_lt_exp_w_l.
  + rewrite -{2}(size_checksum l1 x l2) //.
    rewrite -{4}(size_checksum l1 x' l2) //.
    by rewrite !bw2intK.
  rewrite /checksum /= !int2lbwK //.
  + split=> [|_].
    + by apply: sumr_ge0; smt(BaseW.valP).
    + apply: (ler_lt_trans (big predT (fun _=> w - 1) (int2lbw l1 x))).
      + by apply: ler_sum; smt(BaseW.valP).
      by rewrite big_constz count_predT size_int2lbw.
  + split=> [|_].
    + by apply: sumr_ge0; smt(BaseW.valP).
    + apply: (ler_lt_trans (big predT (fun _=> w - 1) (int2lbw l1 x'))).
      + by apply: ler_sum; smt(BaseW.valP).
      by rewrite big_constz count_predT size_int2lbw.
  rewrite -sumrB big_const -sumrB big_const !count_predT !size_int2lbw //.
  rewrite ler_add2l ler_opp2 -subr_ge0.
  rewrite !(big_nth witness _ BaseW.val) /predT /(\o) /= -/predT.
  by rewrite !size_int2lbw // sumrB.
  qed.

end Checksum.



(* --- WOTS-TW with checksum --- *)
(* -- Require/Import -- *)
require import RealExp BitEncoding.
require Word.
import RField BS2Int.

require WOTS_TW.


(* -- Parameters (copied from WOTS-TW.ec) -- *)
(* Base 2 logarithm of the Winternitz parameter w *)
const log2_w : { int | log2_w = 2 \/ log2_w = 4 \/ log2_w = 8 } as val_log2w.

(* Winternitz parameter (base/radix) *)
const w = 2 ^ log2_w. 

(* Winternitz parameter w equals either 4, 16, or 256 *)
lemma val_w : w = 4 \/ w = 16 \/ w = 256.
proof.
rewrite /w; case: val_log2w => [->|]; last case => ->.
+ by left; rewrite expr2.
+ by right; left; rewrite (: 4 = (2 + 2)) 2:exprD_nneg // expr2. 
+ by right; right; rewrite (: 8 = 2 * 2 * 2) // 2!exprM ?expr2.
qed.


(* -- Checksum instantiation -- *)
clone import Checksum as CS with
  op w <- w
    
  proof gt0_w by smt(val_w).

(* Function to turn an integer (representing a message) into a list of base w digits. *)
op encode_int (l1 n l2 : int) : BaseW.baseW list =
  int2lbw l1 n ++ checksum l1 n l2.

(* Slight variant of checksum_prop lemma that uses encode_int operator and added lengths *)  
lemma checksum_prop_var (l1 l2 x x' : int) :
     0 <= l1
  => 0 <= l2
  => (w - 1) * l1 < w ^ l2
  => 0 <= x  < w ^ l1
  => 0 <= x' < w ^ l1
  => (forall i, 0 <= i < l1 + l2 => BaseW.val (nth witness (encode_int l1 x l2) i) <= BaseW.val (nth witness (encode_int l1 x' l2) i))
  => x = x'.
proof.
move=> gt0_l1 gt0_l2 l1_l2 rng_x rng_xp @/encode_int all_le.
move: (checksum_prop l1 l2 x x' gt0_l1 gt0_l2 l1_l2 rng_x rng_xp _ _) => // i rng_i.
+ move: (all_le i _); first by smt().
  by rewrite 2!nth_cat ?size_int2lbw 1..4:/# (: i < l1) 1:/#.
move: (all_le (l1 + i) _); first by smt().
by rewrite 2!nth_cat ?size_int2lbw 1..4:/# (: ! l1 + i < l1) /#.
qed.

  
clone import WOTS_TW as WTW with
  op log2_w <- log2_w,
  op w <- w,
  
  theory BaseW <- BaseW,
  
  op encode_msgWOTS <- fun (m : msgWOTS) => 
                          EmsgWOTS.mkemsgWOTS (encode_int len1 (bs2int (rev (DigestBlock.val m))) len2)
  
  proof val_log2w, two_encodings.
  realize val_log2w by exact: val_log2w.
  realize two_encodings.    
    move=> m m' neqm_mp.
    have eq28n_wl1 : 2 ^ (8 * n) = w ^ len1.
    + rewrite /w -exprM; congr.
      rewrite /len1 log2_wP -fromint_div 2:from_int_ceil; first by smt(val_log2w).
      by rewrite -divMr 2:mulKz 3://; first 2 smt(val_log2w).
    move: (checksum_prop_var len1 len2 (bs2int (rev (DigestBlock.val m'))) (bs2int (rev (DigestBlock.val m)))).
    move=> /(_ _ _ _); first 2 by smt(ge1_len1 ge1_len2).
    + rewrite -lt_fromint -fromintXn 1:#smt:(ge1_len2) -rpow_int 1:#smt:(val_w).
      have <- := rpowK w%r ((w - 1) * len1)%r _ _ _; first 3 by smt(val_w ge1_len1).
      apply: rexpr_hmono_ltr; first by smt(val_w).
      split=> [|_]; first by rewrite log_ge0 #smt:(val_w ge1_len1).
      rewrite /len2; pose l1w1 := len1 * (w - 1). 
      have ->: log2 l1w1%r / log2 w%r = log w%r l1w1%r; last by smt(floor_bound).
      by rewrite /log2 /log; field; first 2 by smt(ln_eq0 val_w).
    move=> /(_ _ _); first 2 by smt(bs2int_ge0 DigestBlock.valP size_rev bs2int_le2Xs).
    move=> /contra; rewrite negb_forall=> //= /(_ _).
    + rewrite -negP=> /(congr1 (int2bs (8 * n))).
      rewrite -{1}(DigestBlock.valP m') -(size_rev (DigestBlock.val m')) -{1}(DigestBlock.valP m) -(size_rev (DigestBlock.val m)).
      rewrite !bs2intK => /(congr1 rev); rewrite !revK => /(congr1 DigestBlock.insubd).
      by rewrite !DigestBlock.valKd => ->>.
    move=> [] i; rewrite negb_imply (lezNgt (BaseW.val _)) /= => -[Hi Hlt].
    exists i; split; first by exact: Hi.
    rewrite /encode_msgWOTS !EmsgWOTS.getE Hi /= !EmsgWOTS.ofemsgWOTSK //.
    + by rewrite /encode_int size_cat 1:size_int2lbw 3:size_checksum; smt(ge1_len1 ge1_len2 bs2int_ge0).
    by rewrite /encode_int size_cat 1:size_int2lbw 3:size_checksum; smt(ge1_len1 ge1_len2 bs2int_ge0).   
  qed.
