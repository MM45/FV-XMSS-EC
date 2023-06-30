(* --- Require/Import --- *)
(* -- Built-In (Standard Library) -- *)
require import AllCore List Distr FinType BitEncoding.
require (*--*) ROM.
(*---*) import BS2Int.

(* -- Local -- *)
require import FL_XMSS_TW.
require (*--*) DigitalSignatures DigitalSignaturesROM KeyedHashFunctions HashThenSign.
(*---*) import WOTS_TW FLXMSSTW_EUFRMA.



(* --- Parameters --- *)
(* -- Proof-specific -- *)
(* Number of allowed signature queries *)
op qS : { int | 0 <= qS <= l } as rng_qS.

(* Number of allowed random oracle (hash) queries *)
op qH : { int | 0 <= qH } as ge0_qH.



(* --- Types --- *)
(* -- General -- *)
(* 
  Seeds (i.e., indexing keys) for PRF that produces (pseudo)randomness 
  (i.e., indexing keys) for message compression 
*)
type mseed.

(* Indexing keys used for message compression (assumed to be finite) *)
type mkey.

clone import FinType as MKey with
  type t <= mkey.


(* -- XMSS-TW specific -- *)
(* Authentication paths in XMSS-TW binary hash tree *)
type apXMSSTW = apFLXMSSTW.

(* Public keys *)
type pkXMSSTW = pkFLXMSSTW.

(* Secret keys *)
type skXMSSTW = mseed * skFLXMSSTW.

(* Messages (assumed to be finite) *)
type msgXMSSTW.

clone import FinType as MsgXMSSTW with
  type t <= msgXMSSTW.
  
(* Signatures *)
type sigXMSSTW = mkey * sigFLXMSSTW.


(* -- Miscellaneous -- *)
(* Product type of indexing keys used for message compression and messages *)
clone import FinProdType as MKeyMsgXMSSTW with
  type t1 <- mkey,
  type t2 <- msgXMSSTW,
  theory FT1 <- MKey,
  theory FT2 <- MsgXMSSTW
  
  proof *.


    
(* --- Distributions --- *)
(* Proper distribution over seeds used for PRF that generates (pseudo)randomness for message compression *)
op [lossless] dmseed : mseed distr.

(* Proper, full, and uniform distribution over indexing keys used for message compression *)
op [lossless full uniform] dmkey : mkey distr.



(* --- Operators --- *)
(* PRF that generates indexing keys for message compression given a seed and an index *)  
op mkg : mseed -> index -> mkey.

clone import KeyedHashFunctions as MKG with
  type key_t <- mseed,
  type in_t <- index,
  type out_t <- mkey,
  
    op f <- mkg
    
  proof *.
  
clone import PRF as MKG_PRF with  
  op dkey <- dmseed,
  op doutm <- fun _ => dmkey
  
  proof *.
  realize dkey_ll by exact: dmseed_ll.
  realize doutm_ll. by move=> _; apply dmkey_ll. qed.



(* --- Clones and imports --- *)
(* -- Model -- *)
(* Random oracle *)
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


(* -- Scheme specification and security notions -- *)
(* XMSS-TW (where the message compression function is considered to be an RO) *)
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


(* -- Proof-specific -- *)
(* Hash-then-sign proof technique *)
clone import HashThenSign as HtS with
  type pk_fl_t <= pkFLXMSSTW,
  type sk_fl_t <= skFLXMSSTW,
  type msg_fl_t <= msgFLXMSSTW,
  type sig_fl_t <= sigFLXMSSTW,
  type rco_t <= mkey,
  type msg_al_t <= msgXMSSTW,
  type WithPRF.ms_t <= mseed,
  type WithPRF.id_t <= index,
  
    op n <- l,
    op qS <- qS,
    op qH <- qH,
    
    op WithPRF.mkg <= mkg,
    op WithPRF.extr_id <= fun (skfl : skFLXMSSTW) => skfl.`1,
    
    op dmsg_fl <= dmsgFLXMSSTW,
    op drco <= dmkey,
    op WithPRF.dms <= dmseed,
    
  theory RCO <= MKey,
  theory MSG_FL <= DigestBlockFT,
  theory MSG_AL <= MsgXMSSTW,
  theory MCORO <= MCORO,
  theory MCOROLE <= MCOROLE,
  theory DSS_FL <= FLXMSSTW,
  theory EUFRMAEqv.DSS_FL_EUFRMA <= FLXMSSTW_EUFRMA,
  theory WithPRF.MKG <= MKG,
  theory WithPRF.MKG_PRF <= MKG_PRF,
  theory WithPRF.DSS_AL_PRF <= XMSSTW_ROM
  
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
  realize WithPRF.dms_ll by exact: dmseed_ll.

import WithPRF.
import WS.
import EUFRMAEqv.
  

(* --- XMSS-TW --- *)
(* Specification of XMSS-TW (assuming the message compression function is an RO) *)
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


(* --- Reduction adversaries --- *)
module (R_PRF_EUFCMAROXMSSTW (A : Adv_EUFCMA_RO) : Adv_PRF) (O : Oracle_PRF) = {
  module O_CMA_R_PRF_EUFCMAROXMSSTW : SOracle_CMA = {
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
    
    O_CMA_R_PRF_EUFCMAROXMSSTW.init(skfl);
    
    (m, sig) <@ A(MCO, O_CMA_R_PRF_EUFCMAROXMSSTW).forge(pk);
    
    is_valid <@ XMSS_TW(MCO).verify(pk, m, sig);
    
    is_fresh <@ O_CMA_R_PRF_EUFCMAROXMSSTW.fresh(m);
    
    return is_valid /\ is_fresh;
  }
}.


(* --- Proofs of EUF-CMA property for XMSS-TW (assuming message compression is a RO) --- *) 
section Proofs_EUF_CMA_RO_XMSSTW.
(* -- Declarations -- *)
(* Models the signing procedure of FL-XMSS-TW *)
declare op opsign : skFLXMSSTW -> msgFLXMSSTW -> sigFLXMSSTW * skFLXMSSTW.

(* opsign precisely captures the semantics of the signing procedure of FL-XMSS-TW *)
declare axiom FLXMSSTW_sign_fun (skfl : skFLXMSSTW) (cm : msgFLXMSSTW) :
  hoare[FL_XMSS_TW.sign: arg = (skfl, cm) ==> res = opsign skfl cm].

(* The signing procedure of FL-XMSS-TW is lossless (and captured by opsign) *)
local lemma FLXMSSTW_sign_pfun (skfl : skFLXMSSTW) (cm : msgFLXMSSTW) :
  phoare[FL_XMSS_TW.sign: arg = (skfl, cm) ==> res = opsign skfl cm] = 1%r.
proof. by conseq FLXMSSTW_sign_ll (FLXMSSTW_sign_fun skfl cm). qed.

(* Adversary against EUF-CMA in the ROM *)
declare module A <: Adv_EUFCMA_RO{-FL_XMSS_TW, -ERO, -O_CMA_Default, -O_METCR, -R_EUFCMARO_CRRO, -R_EUFCMARO_METCRRO, -Repro.Wrapped_Oracle, -Repro.RepO, -O_RMA_Default, -R_EUFCMARO_IEUFRMA, -QC_A, -Lazy.LRO, -Repro.ReproGame, -R_EUFRMA_IEUFRMA, -R_PRF_EUFCMARO, -O_PRF_Default, -DSS_AL.DSS.KeyUpdating.O_CMA_Default, -PRF_SK_PRF.O_PRF_Default, -FC.O_THFC_Default, -FC_PRE.O_SMDTPRE_Default, -FC_TCR.O_SMDTTCR_Default, -FC_UD.O_SMDTUD_Default, -O_MEUFGCMA_WOTSTWES, -PKCOC.O_THFC_Default, -PKCOC_TCR.O_SMDTTCR_Default, -TRHC.O_THFC_Default, -TRHC_TCR.O_SMDTTCR_Default, -R_SMDTUDC_Game23WOTSTWES, -R_SMDTTCRC_Game34WOTSTWES, -R_PRF_FLXMSSTWESInlineNOPRF, -R_SMDTPREC_Game4WOTSTWES, -R_MEUFGCMAWOTSTWES_EUFRMAFLXMSSTWESNOPRF, -R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF, -R_SMDTTCRCPKCO_EUFRMAFLXMSSTWESNOPRF, -R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF, -R_EUFRMAFLXMSSTW_EUFRMAFLXMSSTWES}.

(* The adversary always terminates if the oracle procedures it can call terminate *)
declare axiom A_forge_ll (RO <: POracle{-A}) (SO <: SOracle_CMA{-A}) : 
  islossless RO.o => islossless SO.sign => islossless A(RO, SO).forge.

(* The adversary makes a limited number of queries to the given random (hash) oracle and signing oracle *)
declare axiom A_forge_queries (RO <: POracle{-A, -QC_A}) (SO <: SOracle_CMA{-A, -QC_A}) : 
  hoare[A(QC_A(A, RO, SO).QC_RO, QC_A(A, RO, SO).QC_SO).forge : 
    QC_A.cH = 0 /\ QC_A.cS = 0 ==> QC_A.cH <= qH /\ QC_A.cS <= qS].


(* -- Security theorems -- *)
(* 
  High-level security theorem (based on EUF-RMA of FL-XMSS-TW):
  XMSS-TW is EUF-CMA secure in the ROM if mkg (i.e., the function that generates
  indexing keys for the message compression function) is a PRF, MCO (i.e., the message
  compression function) is a collision-resistant random oracle, and FL-XMSS-TW is EUF-RMA
  secure
*)
lemma EUFCMARO_XMSSTW_EUFRMA &m :
  Pr[EUF_CMA_RO(XMSS_TW, A, O_CMA_Default, MCO).main() @ &m : res]  
  <=
  `| Pr[PRF(R_PRF_EUFCMARO(FL_XMSS_TW, A), O_PRF_Default).main(false) @ &m : res] -
     Pr[PRF(R_PRF_EUFCMARO(FL_XMSS_TW, A), O_PRF_Default).main(true) @ &m : res] |
  +
  Pr[CR_RO(R_EUFCMARO_CRRO(FL_XMSS_TW, A), MCO).main() @ &m : res]
  +
  Pr[EUF_RMA(FL_XMSS_TW, R_EUFRMA_IEUFRMA(R_EUFCMARO_IEUFRMA(A))).main() @ &m : res]
  +
  qS%r * (qS + qH + 1)%r * mu1 dmkey witness
  +
  l%r * mu1 dmsgFLXMSSTW witness.
proof.
have ->:
  Pr[EUF_CMA_RO(XMSS_TW, A, O_CMA_Default, MCO).main() @ &m : res]
  =
  Pr[EUF_CMA_RO(WithPRF.AL_KU_DSS(FL_XMSS_TW), A, O_CMA_Default, MCO).main() @ &m : res].
+ byequiv => //.
  proc; inline{1} 2; inline{2} 2.
  seq 5 5 : (={O_Base_Default.qs, m, is_valid}); last by sim.
  inline{1} 5; inline{2} 5.
  inline{1} 11; inline{2} 11.
  wp; call(: true); 1: by sim.
  wp; call(: ={ERO.m}); 1: by wp.
  wp; call(: ={O_Base_Default.qs, O_CMA_Default.sk, ERO.m}); first 2 by sim.
  inline *.
  wp; while (={ss1, ss0, ps1, ps0, ms, leafl0, ad1, ad0, ERO.m}); 1: by sim.
  wp; do 3! rnd.
  while (={w, ERO.m}); 1: by wp; rnd; wp; skip.
  by wp; skip.
move: (ALKUDSS_EUFCMARO_PRF_CRRO_EUFRMA FL_XMSS_TW FLXMSSTW_sign_ll FLXMSSTW_verify_ll).
move=> /(_ (fun (skfl : skFLXMSSTW) => skfl.`1 = Index.insubd 0) 
           (fun (skfl : skFLXMSSTW) => (Index.insubd (Index.val skfl.`1 + 1), skfl.`2, skfl.`3, skfl.`4))
           opsign _ FLXMSSTW_sign_fun _ _ _ _).
+ proc; inline *.
  wp; while (true).
  - wp; while (true); 1: by wp.
    wp; while (true); 1: by wp.
    by wp.
  by wp; do 2! rnd; skip.
+ move=> skfl.
  proc; inline *.
  wp => />; while (true).
  - wp; while (true); 1: by wp.
    wp; while (true); 1: by wp.
    by wp.
  wp; while (true); 1: by wp.
  wp; while (true); 1: by wp.
  by wp; skip.
+ move=> i j skfl /= init_sk [ge0i leqS_i] [ge0_j leqS_j] neqj_i.
  have fupd_it: 
    forall (k : int), 0 <= k => k < qS => 
      (fold (fun (sk : skFLXMSSTW) => 
        ((Index.insubd ((Index.val sk.`1) + 1)), sk.`2, sk.`3, sk.`4)) skfl k).`1 
      = 
      Index.insubd k.
  - elim => [@/fupd | k ge0_k @/fupd ih ltqS_k1].
    * by rewrite fold0.
    rewrite foldS //= ih 2:Index.insubdK //; smt(rng_qS).
  rewrite fupd_it // fupd_it //.
  move: neqj_i; apply contra => eqins_ij. 
  by rewrite -(Index.insubdK i) 2:-(Index.insubdK j) 3:eqins_ij; 1,2: smt(rng_qS).
+ by sim.  
+ by sim.
by move=> /(_ A A_forge_ll A_forge_queries &m).
qed.


(*
  Low-level security theorem (based on properties of KHFs and THFs)
  XMSS-TW is EUF-CMA secure in the ROM if mkg (i.e., the function that generates
  indexing keys for the message compression function) is a PRF; MCO (i.e., the message
  compression function) is a collision-resistant random oracle; prf_sk (i.e., the
  function used to generate WOTS-TW secret keys) is a PRF; f (i.e., the function used
  in the WOTS-TW chains) has SM-DT-UD-C, SM-DT-TCR-C, and SM-DT-PRE-C; pkco (i.e., the
  fucntion used to compress WOTS-TW public keys to leaves of the binary hash tree) has 
  SM-DT-TCR-C; and trh (i.e., the function used to construct the full binary hash tree from
  the leaves) has SM-DT-TCR-C.
*)
lemma EUFCMARO_XMSSTW &m :
  l <= d =>
    Pr[EUF_CMA_RO(XMSS_TW, A, O_CMA_Default, MCO).main() @ &m : res]  
    <=
    `| Pr[MKG_PRF.PRF(R_PRF_EUFCMARO(FL_XMSS_TW, A), O_PRF_Default).main(false) @ &m : res] -
       Pr[MKG_PRF.PRF(R_PRF_EUFCMARO(FL_XMSS_TW, A), O_PRF_Default).main(true) @ &m : res] |
    +
    Pr[CR_RO(R_EUFCMARO_CRRO(FL_XMSS_TW, A), MCO).main() @ &m : res]
    +
    `|Pr[PRF_SK_PRF.PRF(R_PRF_FLXMSSTWESInlineNOPRF(R_EUFRMAFLXMSSTW_EUFRMAFLXMSSTWES(R_EUFRMA_IEUFRMA(R_EUFCMARO_IEUFRMA(A)))), PRF_SK_PRF.O_PRF_Default).main(false) @ &m : res] - 
    Pr[PRF_SK_PRF.PRF(R_PRF_FLXMSSTWESInlineNOPRF(R_EUFRMAFLXMSSTW_EUFRMAFLXMSSTWES(R_EUFRMA_IEUFRMA(R_EUFCMARO_IEUFRMA(A)))), PRF_SK_PRF.O_PRF_Default).main(true) @ &m : res]|
    +
    (w - 2)%r * 
  `|Pr[FC_UD.SM_DT_UD_C(R_SMDTUDC_Game23WOTSTWES(R_MEUFGCMAWOTSTWES_EUFRMAFLXMSSTWESNOPRF(R_EUFRMAFLXMSSTW_EUFRMAFLXMSSTWES(R_EUFRMA_IEUFRMA(R_EUFCMARO_IEUFRMA(A))))), FC_UD.O_SMDTUD_Default, FC.O_THFC_Default).main(false) @ &m : res] - 
    Pr[FC_UD.SM_DT_UD_C(R_SMDTUDC_Game23WOTSTWES(R_MEUFGCMAWOTSTWES_EUFRMAFLXMSSTWESNOPRF(R_EUFRMAFLXMSSTW_EUFRMAFLXMSSTWES(R_EUFRMA_IEUFRMA(R_EUFCMARO_IEUFRMA(A))))), FC_UD.O_SMDTUD_Default, FC.O_THFC_Default).main(true) @ &m : res]| 
    +
    Pr[FC_TCR.SM_DT_TCR_C(R_SMDTTCRC_Game34WOTSTWES(R_MEUFGCMAWOTSTWES_EUFRMAFLXMSSTWESNOPRF(R_EUFRMAFLXMSSTW_EUFRMAFLXMSSTWES(R_EUFRMA_IEUFRMA(R_EUFCMARO_IEUFRMA(A))))), FC_TCR.O_SMDTTCR_Default, FC.O_THFC_Default).main() @ &m : res] 
    +
    Pr[FC_PRE.SM_DT_PRE_C(R_SMDTPREC_Game4WOTSTWES(R_MEUFGCMAWOTSTWES_EUFRMAFLXMSSTWESNOPRF(R_EUFRMAFLXMSSTW_EUFRMAFLXMSSTWES(R_EUFRMA_IEUFRMA(R_EUFCMARO_IEUFRMA(A))))), FC_PRE.O_SMDTPRE_Default, FC.O_THFC_Default).main() @ &m : res]
    +
    Pr[PKCOC_TCR.SM_DT_TCR_C(R_SMDTTCRCPKCO_EUFRMAFLXMSSTWESNOPRF(R_EUFRMAFLXMSSTW_EUFRMAFLXMSSTWES(R_EUFRMA_IEUFRMA(R_EUFCMARO_IEUFRMA(A)))), PKCOC_TCR.O_SMDTTCR_Default, PKCOC.O_THFC_Default).main() @ &m : res]
    +
    Pr[TRHC_TCR.SM_DT_TCR_C(R_SMDTTCRCTRH_EUFRMAFLXMSSTWESNOPRF(R_EUFRMAFLXMSSTW_EUFRMAFLXMSSTWES(R_EUFRMA_IEUFRMA(R_EUFCMARO_IEUFRMA(A)))), TRHC_TCR.O_SMDTTCR_Default, TRHC.O_THFC_Default).main() @ &m : res]
    +
    qS%r * (qS + qH + 1)%r * mu1 dmkey witness
    +
    l%r * mu1 dmsgFLXMSSTW witness.
proof.
move=> led_l.
move: (EUFRMA_FLXMSSTW (R_EUFRMA_IEUFRMA(R_EUFCMARO_IEUFRMA(A))) _ &m led_l) (EUFCMARO_XMSSTW_EUFRMA &m); 2: smt().
proc; inline *.
wp; call (: true). 
+ by move=> RO SO ROll SOll; apply (A_forge_ll RO SO).
+ proc; inline *.
  wp; rnd; skip => />.
  by apply dmkey_ll.
+ proc; inline *.
  by wp; skip.
wp; while (true) (size w).
+ move=> z.
  wp; rnd; wp; skip => /> &1 neqel_w.
  split; 2: by apply dmsgFLXMSSTW_ll.
  by elim: (w{1}) neqel_w => //= /#.
by wp; skip => />; smt(size_eq0 size_ge0).
qed.

end section Proofs_EUF_CMA_RO_XMSSTW.
