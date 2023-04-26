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

op [lossless] dmseed : mseed distr.

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


(*
clone import DigitalSignatures as XMSSTW with
  type pk_t <- pkXMSSTW,
  type sk_t <- skXMSSTW,
  type msg_t <- msgXMSSTW,
  type sig_t <- sigXMSSTW
  
  proof *.
*)

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
(*op mco : mkey -> msgXMSSTW -> msgFLXMSSTW.*)

(*
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
*)

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
  
    op f <- mkg, 
    
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
  type WithPRF.ms_t <- mseed,
  type WithPRF.id_t <- index,
  
    op n <- l,
    op qS <- qS,
    op qH <- qH,
    
    op MSG_FL.enum <- map DigestBlock.insubd (map (int2bs (8 * n)) (range 0 (2 ^ (8 * n)))),
    
    op WithPRF.mkg <- mkg,
    op WithPRF.extr_id <- fun (skfl : skFLXMSSTW) => skfl.`1,
    
    op dmsg_fl <- dmsgFLXMSSTW,
    op drco <- dmkey,
    op WithPRF.dms <- dmseed,
    
  theory RCO <- MKey,
  theory MSG_AL <- MsgXMSSTW,
  theory MCORO <- MCORO,
  theory MCOROLE <- MCOROLE,
  theory DSS_FL <- FLXMSSTW,
  theory WithPRF.MKG <- MKG,
  theory WithPRF.DSS_AL_PRF <- XMSSTW_ROM
  
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
  realize WithPRF.dms_ll by exact: dmseed_ll.

import WithPRF.
import WS.
import EFRMAEqv.
import DSS_FL_EFRMA.

(* Scheme *)
module (XMSS_TW : Scheme_RO) (RO : POracle) = {
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

(*
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
*)

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
    
    MCO.init();
    
    (pk, skfl) <@ FL_XMSS_TW.keygen();
    
    O_CMA_R_PRF_EFCMAROXMSSTW.init(skfl);
    
    (m, sig) <@ A(MCO, O_CMA_R_PRF_EFCMAROXMSSTW).forge(pk);
    
    is_valid <@ XMSS_TW(MCO).verify(pk, m, sig);
    
    is_fresh <@ O_CMA_R_PRF_EFCMAROXMSSTW.fresh(m);
    
    return is_valid /\ is_fresh;
  }
}.

section Proof_EF_CMA_RO_XMSSTW.

declare op opsign : skFLXMSSTW -> msgFLXMSSTW -> sigFLXMSSTW * skFLXMSSTW.

declare axiom FLXMSSTW_sign_fun (skfl : skFLXMSSTW) (cm : msgFLXMSSTW) :
  hoare[FL_XMSS_TW.sign: arg = (skfl, cm) ==> res = opsign skfl cm].

local lemma FLXMSSTW_sign_pfun (skfl : skFLXMSSTW) (cm : msgFLXMSSTW) :
  phoare[FL_XMSS_TW.sign: arg = (skfl, cm) ==> res = opsign skfl cm] = 1%r.
proof. by conseq FLXMSSTW_sign_ll (FLXMSSTW_sign_fun skfl cm). qed.

declare module A <: Adv_EFCMA_RO{-FL_XMSS_TW, -ERO, -O_CMA_Default, -O_METCR, -R_EFCMARO_CRRO, -R_EFCMARO_METCRRO, -Repro.Wrapped_Oracle, -Repro.RepO, -O_RMA_Default, -R_EFCMARO_IEFRMA, -QC_A, -Lazy.LRO, -Repro.ReproGame, -R_EFRMA_IEFRMA, -R_PRF_EFCMARO, -O_PRF_Default, -DSS_AL.DSS.KeyUpdating.O_CMA_Default}.

declare axiom A_forge_ll (RO <: POracle{-A}) (SO <: SOracle_CMA{-A}) : 
  islossless RO.o => islossless SO.sign => islossless A(RO, SO).forge.

declare axiom A_forge_queries (RO <: POracle{-A, -QC_A}) (SO <: SOracle_CMA{-A, -QC_A}) : 
  hoare[A(QC_A(A, RO, SO).QC_RO, QC_A(A, RO, SO).QC_SO).forge : 
    QC_A.cH = 0 /\ QC_A.cS = 0 ==> QC_A.cH <= qH /\ QC_A.cS <= qS].
    
lemma EFCMARO_XMSSTW &m :
  Pr[EF_CMA_RO(XMSS_TW, A, O_CMA_Default, MCO).main() @ &m : res]  
  <=
  `| Pr[PRF(R_PRF_EFCMARO(FL_XMSS_TW, A), O_PRF_Default).main(false) @ &m : res] -
     Pr[PRF(R_PRF_EFCMARO(FL_XMSS_TW, A), O_PRF_Default).main(true) @ &m : res] |
  +
  Pr[CR_RO(R_EFCMARO_CRRO(FL_XMSS_TW, A), MCO).main() @ &m : res]
  +
  Pr[EF_RMA(FL_XMSS_TW, R_EFRMA_IEFRMA(R_EFCMARO_IEFRMA(A))).main() @ &m : res]
  +
  qS%r * (qS + qH + 1)%r * mu1 dmkey witness
  +
  l%r * mu1 dmsgFLXMSSTW witness.
proof.
have ->:
  Pr[EF_CMA_RO(XMSS_TW, A, O_CMA_Default, MCO).main() @ &m : res]
  =
  Pr[EF_CMA_RO(WithPRF.AL_KU_DSS(FL_XMSS_TW), A, O_CMA_Default, MCO).main() @ &m : res].
+ byequiv => //.
  proc.
  inline{1} 2; inline{2} 2.
  seq 5 5 : (={O_Base_Default.qs, m, is_valid}); last by sim.
  inline{1} 5; inline{2} 5.
  inline{1} 11; inline{2} 11.
  wp; call(: true); 1: by sim.
  simplify => />.
  wp; call(: ={ERO.m}); 1: by wp.
  simplify => />.
  wp => />.
  call(: ={O_Base_Default.qs, O_CMA_Default.sk, ERO.m}); first 2 by sim.
  simplify => />.
  inline *.
  wp.
  while (={ss1, ss0, ps1, ps0, ms, leafl0, ad1, ad0, ERO.m}).
  by sim.
  simplify => />.
  wp. rnd; rnd; rnd.
  while (={w, ERO.m}).
  wp.
  rnd.
  wp.
  by skip.
  by wp; skip.
move: (ALKUDSS_EFCMARO_PRF_CRRO_EFRMA FL_XMSS_TW FLXMSSTW_sign_ll FLXMSSTW_verify_ll).
move=> /(_ (fun (skfl : skFLXMSSTW) => skfl.`1 = Index.insubd 0) 
           (fun (skfl : skFLXMSSTW) => (Index.insubd (Index.val skfl.`1 + 1), skfl.`2, skfl.`3, skfl.`4))
           opsign _ FLXMSSTW_sign_fun _ _ _ _).
+ proc; inline *.
  wp.
  while (true).
  - wp; while (true); 1: by wp.
    wp; while (true); 1: by wp.
    by wp.
  wp. 
  rnd; rnd.
  by skip.
+ move=> skfl.
  proc; inline *.
  wp => />; while (true).
  - wp; while (true); 1: by wp.
    wp; while (true); 1: by wp.
    by wp.
  wp; while (true); 1: by wp.
  wp; while (true); 1: by wp.
  by wp; skip.
+ move=> i j skfl init_sk leqS_i leqS_j neqj_i.
  admit.
+ by sim.  
+ by sim.
by move=> /(_ A A_forge_ll A_forge_queries &m).
qed.

end section Proof_EF_CMA_RO_XMSSTW.
