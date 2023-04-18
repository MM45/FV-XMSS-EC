require import AllCore Distr List.

require FL_XMSS_TW EFRMA_Interactive_Equiv QDigitalSignaturesStateful_Proofs.

theory Glue.
clone include FL_XMSS_TW.
import EFRMA WOTS_TW.

clone import QDigitalSignaturesStateful_Proofs as QDSSP with
  type QDSP.msg_s  <- msgFLXMSSTW,
  type QDSP.sig_s  <- sigFLXMSSTW,
  type pk_s        <- pkFLXMSSTW,
  type sk_s        <- skFLXMSSTW,
  op   QDSP.dmsg_s <- dmsgFLXMSSTW,
  type root_s      <- WOTS_TW.dgstblock,
  op   get_root_pk (pk : _ *_ *_ ) <- pk.`1,
  op   QDSP.qS     <- n_efrma,
  lemma QDSP.dmsg_s_ll <- dmsg_ll,
  lemma QDSP.ge0_qS <- ge0_nefrma.

import QDSP.
import ROM_PROOF.

(** We give XMSS an oracle it ignores to fit the expected type **)
module (FL_XMSS_TW_RO : Scheme_RO_C) (R : SS1.RO.ROM_.POracle) = {
  proc keygen = FL_XMSS_TW.keygen
  proc sign = FL_XMSS_TW.sign
  proc verify = FL_XMSS_TW.verify
}.

module ReductionL (RO2 : SS2.RO.QRO_i) (A0 : SS2.LI.Adv_EFCMA_RO)
                  (RO1 : QRO_s_t) (SO : SS1.KeyUpdating.SOracle_RMA) = {
  proc forge(pk : pkFLXMSSTW): msgFLXMSSTW * sigFLXMSSTW = {
     var r;
     SS1.RO.QRO.init();
     r <@Reduction(RO2,A0,RO1,SO).forge(pk);
     return r;
  }
}.

(* Reproduce this here to allow local clone
— ideally, we'd merge reductions as we go up the instantiation chain *)
module R_EFRMA_IEFRMA (A : Adv_I_EFRMA) : Adv_EFRMA = {
  module O_R : SOracle_RMA = {
    var q : int
    var msigl : (msgFLXMSSTW * sigFLXMSSTW) list
    
    proc init(msigl_init : (msgFLXMSSTW * sigFLXMSSTW) list) = {
      q <- 0;
      msigl <- msigl_init;
    }
    
    proc sign() : msgFLXMSSTW * sigFLXMSSTW = {
      var q_old : int;

      q_old <- q;
      q <- q + 1;
      
      return nth witness msigl q_old;
    }
    
    proc fresh(m : msgFLXMSSTW) : bool = {
     return ! m \in unzip1 (take q msigl); 
    }
    
    proc nr_queries() : int = {
      return q;
    }
  }
  
  proc forge(pk : pkFLXMSSTW, msigl : (msgFLXMSSTW * sigFLXMSSTW) list) : msgFLXMSSTW * sigFLXMSSTW = {
    var m', sig';
    
    O_R.init(msigl);
    
    (m', sig') <@ A(O_R).forge(pk);

    return (m', sig');
  }
}.

section.
declare module A <: QDSSP.ROM_PROOF.Adv_EFCMA_RO_C_Idx {-SS1.KeyUpdating.O_RMA_Default, -SS2.KeyUpdating.O_CMA_Default, -R_QRO.Wrapped_QRO, -R_QRO.RepO, -R_QRO.QROM.QRO, -OverwriteByQRO_s, -QRO_l, -QRO_s, -QROmsg, -O_CMA_Repro, -Reduction, -O_CMA_Coll, -O_CMA_Game3, -O_CMA_Game3_red, -Game4, -PseudoRF.PRF, -RF.RF, -HS_idx, -SSSt.KeyUpdating.O_CMA_Default, -R_QRO.QROM.LE.ERO, -SS1.RO.LE.ERO, -QROm.ROM_.Lazy.LRO, -QROm.LE.ERO,-R_QRO.CLASSICAL.Wrapped_Oracle, -R_QRO.CLASSICAL.RepO,  -O_CMA_Coll_Simplified, -CountingA, -SS2.RO.ROM_.Lazy.LRO, -SS2.RO.LE.ERO, -O_RMA_Default, -WOTS_TW.PRF_SK.O_PRF_Default, -WOTS_TW.F.O_THFC_Default, -WOTS_TW.F.O_SMDTPRE_Default, -WOTS_TW.F.O_SMDTTCR_Default, -WOTS_TW.F.O_SMDTUD_Default, -WOTS_TW.O_MEFGCMA_WOTSTWES, -PKCO.O_THFC_Default, -PKCO.O_SMDTTCR_Default, -TRH.O_THFC_Default, -TRH.O_SMDTTCR_Default, -R_SMDTUDC_Game23WOTSTWES, -R_SMDTTCRC_Game34WOTSTWES, -R_SMDTPREC_Game4WOTSTWES, -R_PRF_FLXMSSTWESInlineNOPRF, -R_SMDTPREC_Game4WOTSTWES, -R_MEFGCMAWOTSTWES_EFRMAFLXMSSTWESNOPRF, -R_SMDTTCRCTRH_EFRMAFLXMSSTWESNOPRF, -R_SMDTTCRCPKCO_EFRMAFLXMSSTWESNOPRF, -R_SMDTTCRCTRH_EFRMAFLXMSSTWESNOPRF, -R_EFRMAFLXMSSTW_EFRMAFLXMSSTWES, -R_EFRMA_IEFRMA}.

declare axiom forge_q (O <: SS2.KeyUpdating.SOracle_CMA {-CountingA_C, -QDSSP.ROM_PROOF.B2_C(A)})
                      (H0 <: SS2.RO.QRO {-CountingA_C, -QDSSP.ROM_PROOF.B2_C(A)}):
  hoare[ AWrap(QDSSP.ROM_PROOF.B2_C(A), CountingA(AWrap(QDSSP.ROM_PROOF.B2_C(A)), H0, O).Ho, CountingA(AWrap(QDSSP.ROM_PROOF.B2_C(A)), H0, O).S).forge :
          CountingA.cS = 0 /\ CountingA.cH = 0 ==> CountingA.cS <= n_efrma /\ CountingA.cH <= qH].

declare axiom forge_q_C (O <: SS2.KeyUpdating.SOracle_CMA {-CountingA_C, -QDSSP.ROM_PROOF.B2_C(A)})
                        (H0 <: SS2.RO.ROM_.POracle {-CountingA_C, -QDSSP.ROM_PROOF.B2_C(A)}):
  hoare[ QDSSP.ROM_PROOF.B2_C(A, CountingA_C(QDSSP.ROM_PROOF.B2_C(A), H0, O).Ho, CountingA_C(QDSSP.ROM_PROOF.B2_C(A), H0, O).S).forge :
          CountingA.cS = 0 /\ CountingA.cH = 0 ==> CountingA.cS <= n_efrma /\ CountingA.cH <= qH].

declare axiom A_ll (RO <: SS2.RO.ROM_.POracle {-A}) (O <: SSSt.KeyUpdating.SOracle_CMA {-A}) : 
   islossless RO.o => islossless O.sign => islossless A(RO,O).forge.

declare op prGuess : { real | forall m, mu1 dmsgFLXMSSTW m <= prGuess } as prGuessP.

declare op opsign : skFLXMSSTW -> msgFLXMSSTW -> (sigFLXMSSTW * skFLXMSSTW).
declare axiom FL_XMSS_TW_fun sk m:
  hoare [ FL_XMSS_TW.sign: arg = (sk, m) ==> res = opsign sk m ].

local lemma restate_rma &m : Pr[I_EF_RMA(FL_XMSS_TW, ReductionL(SS2.RO.QRO, AWrap(QDSSP.ROM_PROOF.B2_C(A)),SS1.RO.QRO), O_RMA_Default).main() @ &m : res] = 
    Pr[SS1.SI.I_EF_RMA_RO(SWrap(FL_XMSS_TW_RO), Reduction(SS2.RO.QRO, AWrap(QDSSP.ROM_PROOF.B2_C(A))), SS1.KeyUpdating.O_RMA_Default, SS1.RO.QRO).main() @ &m : res].
proof. 
byequiv => //.
proc.
inline {2} 2.
wp;call(_: (glob O_RMA_Default){1} =  (glob SS1.KeyUpdating.O_RMA_Default){2}); 1: by sim.
wp;call(_: (glob O_RMA_Default){1} =  (glob SS1.KeyUpdating.O_RMA_Default){2}); 1: by sim.
call(_: true); 1: by inline *;sim. 
inline {1} 3. inline{1} 5. inline {2} 4.
wp;conseq />. sim 9 8.
inline {1} 9. inline {2} 8.
inline {1} 10. inline {2} 9.
wp;conseq />;call(_: ={glob SSSt.KeyUpdating.O_CMA_Default, glob HS_idx, glob O_CMA_Repro, glob SS2.RO.QRO, glob R_QRO.Wrapped_QRO, glob HS_idx, glob SS1.RO.QRO} /\  (glob O_RMA_Default){1} =  (glob SS1.KeyUpdating.O_RMA_Default){2}); last by swap {1} 4 -3; inline *;conseq />;sim; auto => />; sim. 
proc;inline *.
sp; if=> [/>||]; auto.
+ wp; conseq (: _ ==> ={r,idx,sigWOTS,leafl0,ps,ad,i,glob O_CMA_Repro, m0,tmp,m1, idx,ss} /\  (glob O_RMA_Default){1} =  (glob SS1.KeyUpdating.O_RMA_Default){2}); 1: smt().
by sim; auto => />.
by proc; inline *; auto => />.
qed.

local lemma XMSS_from_FL_XMSS &m : 
     n_efrma = IDX.card
  => Pr[SSSt.LIS.EF_CMA_RO(HS_idx(SWrap(FL_XMSS_TW_RO), PseudoRF.PseudoRF), QDSSP.ROM_PROOF.AWrap_Idx(A), SS2.RO.QRO, SSSt.KeyUpdating.O_CMA_Default).main() @ &m : res]
     <= `|Pr[PRF_.IND(PseudoRF.PRF, B1(SWrap(FL_XMSS_TW_RO), QDSSP.ROM_PROOF.AWrap_Idx(A))).main() @ &m : res]
          - Pr[PRF_.IND(RF.RF, B1(SWrap(FL_XMSS_TW_RO), QDSSP.ROM_PROOF.AWrap_Idx(A))).main() @ &m : res]|
      + Pr[I_EF_RMA(FL_XMSS_TW, ReductionL(SS2.RO.QRO, AWrap(QDSSP.ROM_PROOF.B2_C(A)),SS1.RO.QRO), O_RMA_Default).main() @ &m : res]
      + n_efrma%r * ((n_efrma + qH + 1)%r * (mu1 dr_t witness))
      + ((qH + n_efrma + 3) * (qH + n_efrma + 2))%r / 2%r * (mu1 dmsg witness).
proof.
move=> H_n.
rewrite restate_rma.
print QDSSP.ROM_PROOF.final_statement_C_idx.
apply (QDSSP.ROM_PROOF.final_statement_C_idx A FL_XMSS_TW_RO forge_q forge_q_C _ _ _ A_ll &m H_n _).
+ by move=> O _; apply: XMSS_keygen_ll.
+ by move=> O _; apply: XMSS_sign_ll.
+ by move=> O _; apply: XMSS_verify_ll.
+ by move=> O _; apply: XMSS_verify_ll.
qed.

local clone import EFRMA_Interactive_Equiv as Bridging with
  type msg_t       <- msgFLXMSSTW,
  type sig_t       <- sigFLXMSSTW,
  type pk_t        <- pkFLXMSSTW,
  type sk_t        <- skFLXMSSTW,
  op   dmsg        <- dmsgFLXMSSTW,
  op   n_efrma     <- l,
  lemma dmsg_ll    <- dmsgFLXMSSTW_ll,
  lemma ge0_nefrma <- ge0_nefrma
proof *.

module B = ReductionL(SS2.RO.QRO, AWrap(QDSSP.ROM_PROOF.B2_C(A)),SS1.RO.QRO).

local lemma XMSS_Interactive &m:
     l <= d
  => Pr[I_EF_RMA(FL_XMSS_TW, B, O_RMA_Default).main() @ &m : res]
     <= `|Pr[PRF_SK.PRF(R_PRF_FLXMSSTWESInlineNOPRF(R_EFRMAFLXMSSTW_EFRMAFLXMSSTWES(R_EFRMA_IEFRMA(B))), PRF_SK.O_PRF_Default).main(false) @ &m : res] -
         Pr[PRF_SK.PRF(R_PRF_FLXMSSTWESInlineNOPRF(R_EFRMAFLXMSSTW_EFRMAFLXMSSTWES(R_EFRMA_IEFRMA(B))), PRF_SK.O_PRF_Default).main(true) @ &m : res]|
     + (w - 2)%r
       * `|Pr[F.SM_DT_UD_C(R_SMDTUDC_Game23WOTSTWES(R_MEFGCMAWOTSTWES_EFRMAFLXMSSTWESNOPRF(R_EFRMAFLXMSSTW_EFRMAFLXMSSTWES(R_EFRMA_IEFRMA(B)))), WOTS_TW.F.O_SMDTUD_Default, WOTS_TW.F.O_THFC_Default).main(false) @ &m : res]
           - Pr[F.SM_DT_UD_C(R_SMDTUDC_Game23WOTSTWES(R_MEFGCMAWOTSTWES_EFRMAFLXMSSTWESNOPRF(R_EFRMAFLXMSSTW_EFRMAFLXMSSTWES(R_EFRMA_IEFRMA(B)))), WOTS_TW.F.O_SMDTUD_Default, WOTS_TW.F.O_THFC_Default).main(true) @ &m : res]| 
     + Pr[F.SM_DT_TCR_C(R_SMDTTCRC_Game34WOTSTWES(R_MEFGCMAWOTSTWES_EFRMAFLXMSSTWESNOPRF(R_EFRMAFLXMSSTW_EFRMAFLXMSSTWES(R_EFRMA_IEFRMA(B)))), WOTS_TW.F.O_SMDTTCR_Default, WOTS_TW.F.O_THFC_Default).main() @ &m : res] 
     + Pr[F.SM_DT_PRE_C(R_SMDTPREC_Game4WOTSTWES(R_MEFGCMAWOTSTWES_EFRMAFLXMSSTWESNOPRF(R_EFRMAFLXMSSTW_EFRMAFLXMSSTWES(R_EFRMA_IEFRMA(B)))), F.O_SMDTPRE_Default, F.O_THFC_Default).main() @ &m : res]
     + Pr[PKCO.SM_DT_TCR_C(R_SMDTTCRCPKCO_EFRMAFLXMSSTWESNOPRF(R_EFRMAFLXMSSTW_EFRMAFLXMSSTWES(R_EFRMA_IEFRMA(B))), PKCO.O_SMDTTCR_Default, PKCO.O_THFC_Default).main() @ &m : res]
     + Pr[TRH.SM_DT_TCR_C(R_SMDTTCRCTRH_EFRMAFLXMSSTWESNOPRF(R_EFRMAFLXMSSTW_EFRMAFLXMSSTWES(R_EFRMA_IEFRMA(B))), TRH.O_SMDTTCR_Default, TRH.O_THFC_Default).main() @ &m : res]
     + l%r * prGuess.
proof.
move=> l_le_d.
move: (EFRMA_FLXMSSTW (R_EFRMA_IEFRMA(B)) _ &m _)=> //.
+ islossless.
  apply: (A_ll (<: AWrap(QDSSP.ROM_PROOF.B2_C(A), OverwriteByQRO_s(SS1.RO.QRO, R_QRO.Wrapped_QRO(SS2.RO.QRO)), O_CMA_Repro(R_QRO.Wrapped_QRO(SS2.RO.QRO), R_EFRMA_IEFRMA(ReductionL(SS2.RO.QRO, AWrap(QDSSP.ROM_PROOF.B2_C(A)), SS1.RO.QRO)).O_R)).OC) 
               (<: SSSt.KeyUpdating.O_CMA_Default(QDSSP.ROM_PROOF.B2_C(A, AWrap(QDSSP.ROM_PROOF.B2_C(A), OverwriteByQRO_s(SS1.RO.QRO, R_QRO.Wrapped_QRO(SS2.RO.QRO)), O_CMA_Repro(R_QRO.Wrapped_QRO(SS2.RO.QRO), R_EFRMA_IEFRMA(ReductionL(SS2.RO.QRO, AWrap(QDSSP.ROM_PROOF.B2_C(A)), SS1.RO.QRO)).O_R)).OC, O_CMA_Repro(R_QRO.Wrapped_QRO(SS2.RO.QRO), R_EFRMA_IEFRMA(ReductionL(SS2.RO.QRO, AWrap(QDSSP.ROM_PROOF.B2_C(A)), SS1.RO.QRO)).O_R)).HS_idx_Red2))).
  + by islossless.
  + by islossless.
move=> H.
apply: (StdOrder.RealOrder.ler_trans (Pr[EF_RMA(FL_XMSS_TW, R_EFRMA_IEFRMA(B)).main() @ &m : res] + l%r * prGuess)).
+ have ->: Pr[I_EF_RMA(FL_XMSS_TW, B, O_RMA_Default).main() @ &m : res]
         = Pr[Class_EFRMA.I_EF_RMA(FL_XMSS_TW, B, Class_EFRMA.O_RMA_Default).main() @ &m : res].
  + by byequiv=> //; sim.
  have ->: Pr[EF_RMA(FL_XMSS_TW, R_EFRMA_IEFRMA(B)).main() @ &m : res]
         = Pr[Class_EFRMA.EF_RMA(FL_XMSS_TW, R_EFRMA_IEFRMA(B)).main() @ &m : res].
  + by byequiv=> //; sim.
  apply: (I_EFRMA_le_EF_RMA B _ FL_XMSS_TW _ _ opsign FL_XMSS_TW_fun _ _ prGuess &m _).
  + move=> O O_sign_ll; islossless.
    apply: (A_ll (<: AWrap(QDSSP.ROM_PROOF.B2_C(A), OverwriteByQRO_s(SS1.RO.QRO, R_QRO.Wrapped_QRO(SS2.RO.QRO)), O_CMA_Repro(R_QRO.Wrapped_QRO(SS2.RO.QRO), O)).OC)
                 (<: SSSt.KeyUpdating.O_CMA_Default(QDSSP.ROM_PROOF.B2_C(A, AWrap(QDSSP.ROM_PROOF.B2_C(A), OverwriteByQRO_s(SS1.RO.QRO, R_QRO.Wrapped_QRO(SS2.RO.QRO)), O_CMA_Repro(R_QRO.Wrapped_QRO(SS2.RO.QRO), O)).OC, O_CMA_Repro(R_QRO.Wrapped_QRO(SS2.RO.QRO), O)).HS_idx_Red2))).
    + by islossless.
    + by islossless.
  + exact: XMSS_sign_ll.
  + exact: XMSS_verify_ll.
  + by sim.
  + by sim.
  + exact: prGuessP.
smt().
qed.

lemma XMSS_Final &m:
     n_efrma = IDX.card
  => l <= d
  => Pr[SSSt.LIS.EF_CMA_RO(HS_idx(SWrap(FL_XMSS_TW_RO), PseudoRF.PseudoRF), QDSSP.ROM_PROOF.AWrap_Idx(A), SS2.RO.QRO, SSSt.KeyUpdating.O_CMA_Default).main() @ &m : res]
     <= `|Pr[PRF_.IND(PseudoRF.PRF, B1(SWrap(FL_XMSS_TW_RO), QDSSP.ROM_PROOF.AWrap_Idx(A))).main() @ &m : res]
          - Pr[PRF_.IND(RF.RF, B1(SWrap(FL_XMSS_TW_RO), QDSSP.ROM_PROOF.AWrap_Idx(A))).main() @ &m : res]|
      + `|Pr[PRF_SK.PRF(R_PRF_FLXMSSTWESInlineNOPRF(R_EFRMAFLXMSSTW_EFRMAFLXMSSTWES(Glue.R_EFRMA_IEFRMA(B))), PRF_SK.O_PRF_Default).main(false) @ &m : res] -
         Pr[PRF_SK.PRF(R_PRF_FLXMSSTWESInlineNOPRF(R_EFRMAFLXMSSTW_EFRMAFLXMSSTWES(Glue.R_EFRMA_IEFRMA(B))), PRF_SK.O_PRF_Default).main(true) @ &m : res]|
      + (w - 2)%r
        * `|Pr[F.SM_DT_UD_C(R_SMDTUDC_Game23WOTSTWES(R_MEFGCMAWOTSTWES_EFRMAFLXMSSTWESNOPRF(R_EFRMAFLXMSSTW_EFRMAFLXMSSTWES(Glue.R_EFRMA_IEFRMA(B)))), WOTS_TW.F.O_SMDTUD_Default, WOTS_TW.F.O_THFC_Default).main(false) @ &m : res]
            - Pr[F.SM_DT_UD_C(R_SMDTUDC_Game23WOTSTWES(R_MEFGCMAWOTSTWES_EFRMAFLXMSSTWESNOPRF(R_EFRMAFLXMSSTW_EFRMAFLXMSSTWES(Glue.R_EFRMA_IEFRMA(B)))), WOTS_TW.F.O_SMDTUD_Default, WOTS_TW.F.O_THFC_Default).main(true) @ &m : res]| 
      + Pr[F.SM_DT_TCR_C(R_SMDTTCRC_Game34WOTSTWES(R_MEFGCMAWOTSTWES_EFRMAFLXMSSTWESNOPRF(R_EFRMAFLXMSSTW_EFRMAFLXMSSTWES(Glue.R_EFRMA_IEFRMA(B)))), WOTS_TW.F.O_SMDTTCR_Default, WOTS_TW.F.O_THFC_Default).main() @ &m : res] 
      + Pr[F.SM_DT_PRE_C(R_SMDTPREC_Game4WOTSTWES(R_MEFGCMAWOTSTWES_EFRMAFLXMSSTWESNOPRF(R_EFRMAFLXMSSTW_EFRMAFLXMSSTWES(Glue.R_EFRMA_IEFRMA(B)))), F.O_SMDTPRE_Default, F.O_THFC_Default).main() @ &m : res]
      + Pr[PKCO.SM_DT_TCR_C(R_SMDTTCRCPKCO_EFRMAFLXMSSTWESNOPRF(R_EFRMAFLXMSSTW_EFRMAFLXMSSTWES(Glue.R_EFRMA_IEFRMA(B))), PKCO.O_SMDTTCR_Default, PKCO.O_THFC_Default).main() @ &m : res]
      + Pr[TRH.SM_DT_TCR_C(R_SMDTTCRCTRH_EFRMAFLXMSSTWESNOPRF(R_EFRMAFLXMSSTW_EFRMAFLXMSSTWES(Glue.R_EFRMA_IEFRMA(B))), TRH.O_SMDTTCR_Default, TRH.O_THFC_Default).main() @ &m : res]
      + n_efrma%r * prGuess
      + n_efrma%r * ((n_efrma + qH + 1)%r * (mu1 dr_t witness))
      + ((qH + n_efrma + 3) * (qH + n_efrma + 2))%r / 2%r * (mu1 dmsg witness).
proof.
move=> n_idx l_le_d.
move: (XMSS_Interactive &m _)=> // H.
move: (XMSS_from_FL_XMSS &m _)=> //.
have ^ -> ->: 
  forall b,
    Pr[F.SM_DT_UD_C(R_SMDTUDC_Game23WOTSTWES(R_MEFGCMAWOTSTWES_EFRMAFLXMSSTWESNOPRF(R_EFRMAFLXMSSTW_EFRMAFLXMSSTWES(Glue.R_EFRMA_IEFRMA(B)))), WOTS_TW.F.O_SMDTUD_Default, WOTS_TW.F.O_THFC_Default).main(b) @ &m : res]
  = Pr[F.SM_DT_UD_C(R_SMDTUDC_Game23WOTSTWES(R_MEFGCMAWOTSTWES_EFRMAFLXMSSTWESNOPRF(R_EFRMAFLXMSSTW_EFRMAFLXMSSTWES(R_EFRMA_IEFRMA(B)))), WOTS_TW.F.O_SMDTUD_Default, WOTS_TW.F.O_THFC_Default).main(b) @ &m : res].
+ by move=> b; byequiv=> //; sim.
have ->:
  Pr[F.SM_DT_TCR_C(R_SMDTTCRC_Game34WOTSTWES(R_MEFGCMAWOTSTWES_EFRMAFLXMSSTWESNOPRF(R_EFRMAFLXMSSTW_EFRMAFLXMSSTWES(Glue.R_EFRMA_IEFRMA(B)))), WOTS_TW.F.O_SMDTTCR_Default, WOTS_TW.F.O_THFC_Default).main() @ &m : res]
  =
  Pr[F.SM_DT_TCR_C(R_SMDTTCRC_Game34WOTSTWES(R_MEFGCMAWOTSTWES_EFRMAFLXMSSTWESNOPRF(R_EFRMAFLXMSSTW_EFRMAFLXMSSTWES(R_EFRMA_IEFRMA(B)))), WOTS_TW.F.O_SMDTTCR_Default, WOTS_TW.F.O_THFC_Default).main() @ &m : res].
+ by byequiv=> //; sim.
have ->:
  Pr[F.SM_DT_PRE_C(R_SMDTPREC_Game4WOTSTWES(R_MEFGCMAWOTSTWES_EFRMAFLXMSSTWESNOPRF(R_EFRMAFLXMSSTW_EFRMAFLXMSSTWES(Glue.R_EFRMA_IEFRMA(B)))), F.O_SMDTPRE_Default, F.O_THFC_Default).main() @ &m : res]
  =
  Pr[F.SM_DT_PRE_C(R_SMDTPREC_Game4WOTSTWES(R_MEFGCMAWOTSTWES_EFRMAFLXMSSTWESNOPRF(R_EFRMAFLXMSSTW_EFRMAFLXMSSTWES(R_EFRMA_IEFRMA(B)))), F.O_SMDTPRE_Default, F.O_THFC_Default).main() @ &m : res].
+ by byequiv=> //; sim.
have ^ -> ->:
  forall b,
    Pr[PRF_SK.PRF(R_PRF_FLXMSSTWESInlineNOPRF(R_EFRMAFLXMSSTW_EFRMAFLXMSSTWES(Glue.R_EFRMA_IEFRMA(B))), PRF_SK.O_PRF_Default).main(b) @ &m : res]
  =
    Pr[PRF_SK.PRF(R_PRF_FLXMSSTWESInlineNOPRF(R_EFRMAFLXMSSTW_EFRMAFLXMSSTWES(R_EFRMA_IEFRMA(B))), PRF_SK.O_PRF_Default).main(b) @ &m : res].
+ by move=> b; byequiv=> //; sim.
have ->: 
 Pr[PKCO.SM_DT_TCR_C(R_SMDTTCRCPKCO_EFRMAFLXMSSTWESNOPRF(R_EFRMAFLXMSSTW_EFRMAFLXMSSTWES(Glue.R_EFRMA_IEFRMA(B))), PKCO.O_SMDTTCR_Default, PKCO.O_THFC_Default).main() @ &m : res]
 =
 Pr[PKCO.SM_DT_TCR_C(R_SMDTTCRCPKCO_EFRMAFLXMSSTWESNOPRF(R_EFRMAFLXMSSTW_EFRMAFLXMSSTWES(R_EFRMA_IEFRMA(B))), PKCO.O_SMDTTCR_Default, PKCO.O_THFC_Default).main() @ &m : res].
+ by byequiv=> //; sim.
have ->: 
 Pr[TRH.SM_DT_TCR_C(R_SMDTTCRCTRH_EFRMAFLXMSSTWESNOPRF(R_EFRMAFLXMSSTW_EFRMAFLXMSSTWES(Glue.R_EFRMA_IEFRMA(B))), TRH.O_SMDTTCR_Default, TRH.O_THFC_Default).main() @ &m : res]
 =
 Pr[TRH.SM_DT_TCR_C(R_SMDTTCRCTRH_EFRMAFLXMSSTWESNOPRF(R_EFRMAFLXMSSTW_EFRMAFLXMSSTWES(R_EFRMA_IEFRMA(B))), TRH.O_SMDTTCR_Default, TRH.O_THFC_Default).main() @ &m : res].
+ by byequiv=> //; sim.
smt().
qed.
end section.
end Glue.
