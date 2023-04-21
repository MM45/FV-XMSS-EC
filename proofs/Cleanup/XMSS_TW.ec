(* --- Require/Import --- *)
(* -- Built-In (Standard Library) -- *)
require import AllCore List Distr FinType BitEncoding.
require (*--*) ROM.
(*---*) import BS2Int.

(* -- Local -- *)
require import FL_XMSS_TW.
require (*--*) DigitalSignatures DigitalSignaturesROM KeyedHashFunctions HashThenSign.
(*---*) import WOTS_TW.

type mseed.
type mkey.

op [lossless full uniform] dmseed : mseed distr.

op [lossless full uniform] dmkey : mkey distr.

(* Authentication paths in Fixed-Length XMSS-TW binary hash tree *)
type apXMSSTW = apFLXMSSTW.

(* Public keys *)
type pkXMSSTW = pkFLXMSSTW.

(* Secret keys *)
type skXMSSTW = mseed * skFLXMSSTW.

(* Messages *)
type msgXMSSTW.

(* Signatures *)
type sigXMSSTW = mkey * sigFLXMSSTW.

clone import FinType as MKey with
  type t <= mkey.
  
clone import FinType as MsgXMSSTW with
  type t <= msgXMSSTW.

clone import FinProdType as MKeyMsgXMSSTW with
  type t1 <- mkey,
  type t2 <- msgXMSSTW,
  theory FT1 <- MKey,
  theory FT2 <- MsgXMSSTW
  
  proof *.



clone import DigitalSignatures as XMSSTW with
  type pk_t <- pkXMSSTW,
  type sk_t <- skXMSSTW,
  type msg_t <- msgXMSSTW,
  type sig_t <- sigXMSSTW
  
  proof *.


clone import ROM as MCORO with
  type in_t <- mkey * msgXMSSTW,
  type out_t <- msgFLXMSSTW,
    op dout <- fun _ => dmsgFLXMSSTW,
  type d_in_t <- int,
  type d_out_t <- bool
  
  proof *.

clone import MCORO.LazyEager as MCOROLE with
  theory FinType <- MKeyMsgXMSSTW
  
  proof *. 

module MCO = ERO.


op mkg : mseed -> index -> mkey.
op mco : mkey -> msgXMSSTW -> msgFLXMSSTW.


clone import DigitalSignaturesROM as XMSSTW_RNDROM with
  type pk_t <- pkXMSSTW,
  type sk_t <- skFLXMSSTW,
  type msg_t <- msgXMSSTW,
  type sig_t <- sigXMSSTW,
  
  type in_t <- mkey * msgXMSSTW,
  type out_t <- msgFLXMSSTW,
  type d_in_t <- int,
  type d_out_t <- bool,
  
    op doutm <- fun _ => dmsgFLXMSSTW,
   
  theory RO <- MCORO
  
  proof *.

clone import DigitalSignaturesROM as XMSSTW_ROM with
  type pk_t <- pkXMSSTW,
  type sk_t <- skXMSSTW,
  type msg_t <- msgXMSSTW,
  type sig_t <- sigXMSSTW,
  
  type in_t <- mkey * msgXMSSTW,
  type out_t <- msgFLXMSSTW,
  type d_in_t <- int,
  type d_out_t <- bool,
  
    op doutm <- fun _ => dmsgFLXMSSTW,
   
  theory RO <- MCORO
  
  proof *.

import XMSSTW_ROM.KeyUpdatingROM.
import DSS.
import KeyUpdating.

clone import KeyedHashFunctions as MKG with
  type key_t <- mseed,
  type in_t <- index,
  type out_t <- mkey,
  
    op dkey <- dmseed,
    op doutm <- fun _ => dmkey
  
  proof dkey_ll, doutm_ll.
  realize dkey_ll by exact: dmseed_ll.
  realize doutm_ll. by move=> _; apply dmkey_ll. qed.
  

(* Signature queries *)
op qS : { int | 0 <= qS <= l } as rng_qS.

(* Random oracle (hash) queries *)
op qH : { int | 0 <= qH } as ge0_qH. 


clone import HashThenSign as HtS with
  type pk_fl_t <- pkFLXMSSTW,
  type sk_fl_t <- skFLXMSSTW,
  type msg_fl_t <- msgFLXMSSTW,
  type sig_fl_t <- sigFLXMSSTW,
  type rco_t <- mkey,
  type msg_al_t <- msgXMSSTW,
    
    op n <- l,
    op qS <- qS,
    op qH <- qH,
    
    op MSG_FL.enum <- map DigestBlock.insubd (map (int2bs (8 * n)) (range 0 (2 ^ (8 * n)))),
    
    op dmsg_fl <- dmsgFLXMSSTW,
    op drco <- dmkey,

  theory RCO <- MKey,
  theory MSG_AL <- MsgXMSSTW,
  theory MCORO <- MCORO,
  theory MCOROLE <- MCOROLE,
  theory DSS_FL <- FLXMSSTW,
  theory DSS_AL <- XMSSTW_RNDROM
  
  proof *.
  realize ge0_n by smt(ge2_l).
  realize rng_qS by exact: rng_qS.
  realize ge0_qH by exact: ge0_qH.
  realize dmsg_fl_ll by exact: dmsgFLXMSSTW_ll.
  realize dmsg_fl_uni by exact: dmsgFLXMSSTW_uni.
  realize dmsg_fl_fu by exact: dmsgFLXMSSTW_fu.
  realize drco_ll by exact: dmkey_ll.
  realize drco_uni by exact: dmkey_uni.
  realize drco_fu by exact: dmkey_fu.
  realize MSG_FL.enum_spec.
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

(* Scheme *)
module XMSS_TW : XMSSTW.KeyUpdating.Scheme = {
  proc keygen() : pkXMSSTW * skXMSSTW  = {
    var ms : mseed;
    var pk : pkXMSSTW;
    var skfl : skFLXMSSTW;
    var sk : skXMSSTW;
    
    ms <$ dmseed;
    
    (pk, skfl) <@ FL_XMSS_TW.keygen();
    
    sk <- (ms, skfl);
    
    return (pk, sk);
  }
  
  proc sign(sk : skXMSSTW, m : msgXMSSTW) : sigXMSSTW * skXMSSTW = {
    var ms : mseed;
    var skfl : skFLXMSSTW;
    var idx : index;
    var mk : mkey;
    var cm : msgFLXMSSTW;
    var sigfl: sigFLXMSSTW;
    var sig : sigXMSSTW;
    
    ms <- sk.`1;
    skfl <- sk.`2;
    
    idx <- skfl.`1;
    
    mk <- mkg ms idx;
    cm <- mco mk m;
    
    (sigfl, skfl) <@ FL_XMSS_TW.sign(skfl, cm);
    
    sig <- (mk, sigfl);
    sk <- (ms, skfl);
    
    return (sig, sk);
  }
  
  proc verify(pk : pkXMSSTW, m : msgXMSSTW, sig : sigXMSSTW) : bool = {
    var mk : mkey;
    var sigfl : sigFLXMSSTW;
    var cm : msgFLXMSSTW;
    var ver : bool;
    
    mk <- sig.`1;
    sigfl <- sig.`2;
    
    cm <- mco mk m;
    
    ver <@ FL_XMSS_TW.verify(pk, cm, sigfl);
     
    return ver;
  }
}.


(* Scheme *)
module (XMSS_TW_RO : XMSSTW_ROM.KeyUpdatingROM.Scheme_RO) (RO : POracle) = {
  proc keygen() : pkXMSSTW * skXMSSTW = {
    var ms : mseed;
    var pk : pkXMSSTW;
    var skfl : skFLXMSSTW;
    var sk : skXMSSTW;
    
    ms <$ dmseed;
    
    (pk, skfl) <@ FL_XMSS_TW.keygen();
    
    sk <- (ms, skfl);
    
    return (pk, sk);
  }
  
  proc sign(sk : skXMSSTW, m : msgXMSSTW) : sigXMSSTW * skXMSSTW = {
    var ms : mseed;
    var skfl : skFLXMSSTW;
    var idx : index;
    var mk : mkey;
    var cm : msgFLXMSSTW;
    var sigfl: sigFLXMSSTW;
    var sig : sigXMSSTW;
    
    ms <- sk.`1;
    skfl <- sk.`2;
    
    idx <- skfl.`1;
    
    mk <- mkg ms idx;
    cm <@ RO.o((mk, m));
    
    (sigfl, skfl) <@ FL_XMSS_TW.sign(skfl, cm);
    
    sig <- (mk, sigfl);
    sk <- (ms, skfl);
    
    return (sig, sk);
  }
  
  proc verify(pk : pkXMSSTW, m : msgXMSSTW, sig : sigXMSSTW) : bool = {
    var mk : mkey;
    var sigfl : sigFLXMSSTW;
    var cm : msgFLXMSSTW;
    var ver : bool;
    
    mk <- sig.`1;
    sigfl <- sig.`2;
    
    cm <@ RO.o((mk, m));
    
    ver <@ FL_XMSS_TW.verify(pk, cm, sigfl);
     
    return ver;
  }
}.

print O_Base_Default.
(* -- Reduction Adversaries -- *)
module (R_PRF_EFCMAROXMSSTW (A : Adv_EFCMA_RO) : Adv_PRF) (O : Oracle_PRF) = {
  module O_CMA_R_PRF_EFCMAROXMSSTW : SOracle_CMA = {
    include var O_Base_Default
    
    var skfl : skFLXMSSTW
    
    proc init(skfl_init : skFLXMSSTW) = {
      skfl <- skfl_init;
      qs <- [];
    }
    
    proc sign(m : msgXMSSTW) : sigXMSSTW = {
      var idx : index;
      var mk : mkey;
      var cm : msgFLXMSSTW;
      var sigfl : sigFLXMSSTW;
      var sig : sigXMSSTW;
      
      idx <- skfl.`1;
      
      mk <@ O.query(idx);
      
      cm <@ MCO.o(mk, m);
      
      (sigfl, skfl) <@ FL_XMSS_TW.sign(skfl, cm);
      
      sig <- (mk, sigfl);
      
      return sig;
    }
  }
  
  proc distinguish() : bool = {
    var pk : pkXMSSTW;
    var skfl : skFLXMSSTW; 
    var m : msgXMSSTW;
    var sig : sigXMSSTW;
    var is_valid, is_fresh;
    
    (pk, skfl) <@ FL_XMSS_TW.keygen();
    
    O_CMA_R_PRF_EFCMAROXMSSTW.init(skfl);
    
    (m, sig) <@ A(MCO, O_CMA_R_PRF_EFCMAROXMSSTW).forge(pk);
    
    is_valid <@ XMSS_TW_RO(MCO).verify(pk, m, sig);
    
    is_fresh <@ O_CMA_R_PRF_EFCMAROXMSSTW.fresh(m);
    
    return is_valid /\ is_fresh;
  }
}.

section Proof_EF_CMA_RO_XMSSTW.

declare module A <: XMSSTW_ROM.KeyUpdatingROM.Adv_EFCMA_RO.


end section Proof_EF_CMA_RO_XMSSTW.
