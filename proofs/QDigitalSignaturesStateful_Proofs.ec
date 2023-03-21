require import AllCore List SmtMap FSet FinType Distr.
require (***) QDigitalSignatures_Proofs T_QPRF PRF.


type sk_s.
type pk_s.
type root_s.
op get_root_pk : pk_s -> root_s.
type msg_l.
type r_t.

type idx.

clone import QDigitalSignatures_Proofs as QDSP with
   type sk_s <- sk_s,
   type pk_s <- pk_s,
   type r_t <- r_t,
   type msg_l <- root_s * idx * msg_l.

clone import FinType as IDX with
   type t <-idx.

op nIndices : int = IDX.card.

clone import T_QPRF as PRF_ with type D <- idx, type R <- r_t.
clone import PseudoRF.
clone import RF with op dR <- (fun _ => dr_t).

module HS_idx(Sig : SS1.SI.Scheme_RO, PRF : PseudoRF, O : QRO_l_t) = {
  var used : int
  var k : K
  var pk : pk_s

  proc keygen(): pk_s * sk_s = {
    var sk;
    (pk,sk) <@ Sig(O_l2s(O)).keygen();
    k <$ dK;
    used <- 0;
    return (pk,sk);
  }  
  
  proc sign(sk : sk_l, m : msg_l): (sig_l * idx) option * sk_l = {
    var sig_sk, ms, r, sig, result,i;
    
    result <- (None, sk);
    if (used < nIndices) {
       i <- nth witness enum used;
       r <@ PRF.f(k,i); 
       ms <@ ROmsg(O).h{(r, (get_root_pk pk, i, m))};
       sig_sk <@ Sig(O_l2s(O)).sign(sk, ms);
       sig <- ((r,sig_sk.`1),i);
       used <- used + 1; 
       result <- (Some sig, sig_sk.`2);
    }
    return result;
  }
  
  (* Cannot use state! *)
  proc verify(pk : pk_l, m : msg_l, sig : (sig_l * idx) option): bool = {
    var b,ms;
    b <- false;
    if (sig<>None) {
       ms <@ ROmsg(O).h{((oget sig).`1.`1,  (get_root_pk pk, (oget sig).`2, m))};
       b <@ Sig(O_l2s(O)).verify(pk, ms, (oget sig).`1.`2);
    }
    return b;
  }
}.

(* -- The target: long input signature scheme -- *)   
clone QDigitalSignaturesRO as SSSt with
  type msg_t <- msg_l,
  type sig_t <- (sig_l * idx) option,
  type pk_t <- pk_l,
  type sk_t <- sk_l,
  type RO.from <= ro_in,
  type RO.hash <= ro_out,
  
  op RO.dhash <= ro_dhash,
  op KeyUpdating.q_efcma <- qS
    
  
  rename [theory] "KeyUpdating_RO" as "LIS".

module HS_idx_Red1(Sig : SS1.SI.Scheme_RO, F : PRF_Oracles, O : QRO_l_t) = {
  proc keygen(): pk_s * sk_s = {
    var sk;
    (HS_idx.pk,sk) <@ Sig(O_l2s(O)).keygen();
    HS_idx.used <- 0;
    return (HS_idx.pk,sk);
  }  

  proc sign(sk : sk_l, m : msg_l): (sig_l * idx) option * sk_l = {
    var sig_sk, ms, r, sig, result,i;
    
    result <- (None,sk);
    if (HS_idx.used < nIndices) {
       i <- nth witness enum HS_idx.used;
       r <@ F.f(i); 
       ms <@ ROmsg(O).h{(r, (get_root_pk HS_idx.pk, i, m))};
       sig_sk <@ Sig(O_l2s(O)).sign(sk, ms);
       sig <- ((r,sig_sk.`1),i);
       HS_idx.used <- HS_idx.used + 1; 
       result <- (Some sig, sig_sk.`2);
    }
    return result;
  }

  (* Cannot use state! *)
  proc verify(pk : pk_l, m : msg_l, sig : (sig_l * idx) option): bool = {
    var b : bool;
    var ms : msg_s;
    
    b <- false;
    if (sig<>None) {
       ms <@ ROmsg(O).h{((oget sig).`1.`1,  (get_root_pk pk, (oget sig).`2, m))};
       b <@ Sig(O_l2s(O)).verify(pk, ms, (oget sig).`1.`2);
    }
    return b;
  }

}.

module (B1(Sig : SS1.SI.Scheme_RO, A : SSSt.LIS.Adv_EFCMA_RO) : Distinguisher) (F : PRF_Oracles) = {


    proc distinguish(): bool = { 
       var pk,sk,sk_init,m,sig,is_valid,is_fresh,nrqs,is_inrngvalidfresh;
       SS2.RO.QRO.init();
       (pk, sk) <@ HS_idx_Red1(Sig,F,SS2.RO.QRO).keygen();
       sk_init <- sk;
       SSSt.KeyUpdating.O_CMA_Default.sk <- sk_init;
       SSSt.KeyUpdating.O_CMA_Default.qs <- ([])%List;
       (m, sig) <@ SSSt.KeyUpdating.EF_CMA(HS_idx_Red1(Sig,F,SS2.RO.QRO), A(SS2.RO.QRO), SSSt.KeyUpdating.O_CMA_Default).A.forge(pk);
       is_valid <@ HS_idx_Red1(Sig,F,SS2.RO.QRO).verify(pk, m, sig);
       is_fresh <@ SSSt.KeyUpdating.EF_CMA(HS_idx_Red1(Sig,F,SS2.RO.QRO), A(SS2.RO.QRO), SSSt.KeyUpdating.O_CMA_Default).O.fresh(m);
       nrqs <@ SSSt.KeyUpdating.EF_CMA(HS_idx_Red1(Sig,F,SS2.RO.QRO), A(SS2.RO.QRO), SSSt.KeyUpdating.O_CMA_Default).O.nr_queries();
       is_inrngvalidfresh <- nrqs <= qS /\ is_valid /\ is_fresh;
       return  is_inrngvalidfresh; 
    }
}.


module (B2(A : SSSt.LIS.Adv_EFCMA_RO): SS2.LI.Adv_EFCMA_RO) (R : SS2.RO.QRO, O : SS2.KeyUpdating.SOracle_CMA) = {
  module HS_idx_Red2 = {
     var _pk : pk_s

     proc keygen(): pk_s * sk_s = {
      HS_idx.k <- witness;
       return (_pk,witness);
    }  

    proc sign(ms : sk_l * msg_l):  (sig_l * idx) option * sk_l = {
      var sig_sk,  sig, i, result;
      result <- (None, witness);
      if (HS_idx.used < nIndices) {
         i <- nth witness enum HS_idx.used;
         sig_sk <@ O.sign((get_root_pk HS_idx.pk, i, ms.`2));
         sig <- (sig_sk,i);
         HS_idx.used <- HS_idx.used + 1;
         result <- (Some sig,witness);
    }
    return result;
  }

  proc verify(pk : pk_l, m : msg_l, sig : (sig_l * idx) option): bool = {
      return witness;
  }

  }

 proc forge(pk : pk_l): (root_s * idx * msg_l) * sig_l = { 
       var m,sig;
       HS_idx.used <- 0;
       HS_idx.pk <- pk;
       SSSt.KeyUpdating.O_CMA_Default.qs <- ([])%List;
       (m, sig) <@ SSSt.KeyUpdating.EF_CMA(HS_idx_Red2, A(R), SSSt.KeyUpdating.O_CMA_Default).A.forge(pk);
       return ((get_root_pk pk,(oget sig).`2,m),(oget sig).`1);
    }
}.

section.

(* For all adversaries A ... *)
declare module A <: SSSt.LIS.Adv_EFCMA_RO {-QRO_s, -QRO_l, -QROmsg, -OverwriteByQRO_s, -R_QRO.Wrapped_QRO, -SS2.KeyUpdating.O_CMA_Default, -O_CMA_Repro, -O_CMA_Game3_red, -R_QRO.RepO, -R_QRO.QROM.QRO, -O_CMA_Game3, -SS1.KeyUpdating.O_RMA_Default, -Game4, -Reduction, -O_CMA_Coll, -SSSt.KeyUpdating.O_CMA_Default, -HS_idx, -PRF, -RF (* , -B2 *)}.
declare module S1 <: SS1.SI.Scheme_RO {-A, -QRO_s, -QRO_l, -QROmsg, -OverwriteByQRO_s, -R_QRO.Wrapped_QRO, -SS2.KeyUpdating.O_CMA_Default, -O_CMA_Repro, -O_CMA_Game3_red, -R_QRO.QROM.QRO, -R_QRO.RepO, -O_CMA_Game3, -SS1.KeyUpdating.BaseOracle, -SS1.KeyUpdating.O_RMA_Default, -Game4, -Reduction, -O_CMA_Coll, -SSSt.KeyUpdating.O_CMA_Default, -HS_idx, -PRF, -RF (* , -B2 *)}.

lemma final_statement &m: 
  qS = IDX.card =>
  (forall (OO <: SS1.RO.QRO {-A}), islossless OO.h => islossless S1(OO).verify)  =>
  Pr [SSSt.LIS.EF_CMA_RO(HS_idx(S1,PseudoRF), A, QRO_l, SSSt.KeyUpdating.O_CMA_Default).main() @ &m : res] 
  <=  `| Pr [ IND(PRF, B1(S1,A)).main() @ &m : res ] -
         Pr [ IND(RF, B1(S1,A)).main() @ &m : res ] |  + 
      Pr [SS2.LI.EF_CMA_RO(HS(S1), B2(A), QRO_l, SS2.KeyUpdating.O_CMA_Default).main() @ &m : res] .
proof.
move => lcard verify_ll.
have -> : 
   Pr[SSSt.LIS.EF_CMA_RO(HS_idx(S1, PseudoRF), A, QRO_l, SSSt.KeyUpdating.O_CMA_Default).main() @ &m : res] = 
   Pr [ IND(PRF, B1(S1,A)).main() @ &m : res ].
+ byequiv => //.
  proc. 
  inline {2} 2; swap {2} 2 -1.
  inline {1} 2; inline {1} 3; inline {1} 2; inline {2} 2.
  inline {2} 3; swap {1} 3 -1.

  inline *;sim 10 10.
  call(_ : ={glob SS2.RO.QRO, glob S1, glob SSSt.KeyUpdating.O_CMA_Default,HS_idx.used,HS_idx.pk} /\ HS_idx.k{1} = PRF.k{2}). 
  + by proc; inline*; sim.
  + by sim. 
  wp; conseq />;call(_ : ={glob SS2.RO.QRO}). 
  + by sim.
  by auto => />. 

have : 
  Pr[IND(RF, B1(S1, A)).main() @ &m : res] <=
  Pr[SS2.LI.EF_CMA_RO(HS(S1), B2(A), QRO_l, SS2.KeyUpdating.O_CMA_Default).main() @ &m : res]; last by smt().

byequiv => //.
proc; inline *.
wp; conseq/>; 1: by smt(). 
seq 10 11 : (={glob SS2.RO.QRO, glob S1,pk,HS_idx.used} /\ pk{1} =pk0{2} /\ m{1} = m0{2} /\ sig{1} = sig0{2} /\ 
     size SS2.KeyUpdating.O_CMA_Default.qs{2} <= qS /\ 
        size SS2.KeyUpdating.O_CMA_Default.qs{2} <= size SSSt.KeyUpdating.O_CMA_Default.qs{1} /\
        (size SSSt.KeyUpdating.O_CMA_Default.qs{1} <= qS => 
           size SSSt.KeyUpdating.O_CMA_Default.qs{1} = size SS2.KeyUpdating.O_CMA_Default.qs{2}) /\ 
     forall mm, mm \in SS2.KeyUpdating.O_CMA_Default.qs{2} => mm.`3 \in SSSt.KeyUpdating.O_CMA_Default.qs{1}); last first. 
+ sp;if{1};last first.
  + call{2}(_: true ==> true); 1: by apply (verify_ll (O_l2s(SS2.RO.QRO)));islossless. 
    by auto => />.
  call(_: ={glob SS2.RO.QRO}); 1: by sim.
  by auto => /> /#. 
call(_: ={glob SS2.RO.QRO, glob S1,HS_idx.used,HS_idx.pk} /\  
        size SS2.KeyUpdating.O_CMA_Default.qs{2} <= qS /\ 
        size SS2.KeyUpdating.O_CMA_Default.qs{2} <= size SSSt.KeyUpdating.O_CMA_Default.qs{1} /\
        (size SSSt.KeyUpdating.O_CMA_Default.qs{1} <= qS => 
           size SSSt.KeyUpdating.O_CMA_Default.qs{1} = size SS2.KeyUpdating.O_CMA_Default.qs{2}) /\
        HS_idx.used{1} = size SS2.KeyUpdating.O_CMA_Default.qs{2} /\
        SSSt.KeyUpdating.O_CMA_Default.sk{1} = SS2.KeyUpdating.O_CMA_Default.sk{2} /\
        (forall mm, mm \in SS2.KeyUpdating.O_CMA_Default.qs{2} => mm.`3 \in SSSt.KeyUpdating.O_CMA_Default.qs{1}) /\
        perm_eq (take (size SS2.KeyUpdating.O_CMA_Default.qs{2}) enum) (elems (fdom RF.m{1}))
   ); first last.
+ by proc;inline*;conseq/>;sim.
+ wp;call(_: ={glob SS2.RO.QRO}); 1: by sim.
  auto => /> *; do split; 1: by smt(SSSt.KeyUpdating.ge0_qefcma). 
  by rewrite take0 fdom0 elems_fset0 /#.

proc;inline *;sp 2 2;if{2};last first.
+ rcondf{1} 2; 1: by move => *;auto=>/>.
  auto => /> &1 &2 *;do split. 
  + by rewrite size_rcons /#. search drop size. 
  + have : qS = (size SS2.KeyUpdating.O_CMA_Default.qs{2}); last by smt(size_rcons).
    by smt(drop_size size_drop SSSt.KeyUpdating.ge0_qefcma). 
  by smt(mem_rcons).
rcondt{1} 2; 1: by move => *;auto=>/>.
rcondt{1} 4.
+ move => &2;auto=>/> &1 ??????.
  have /= <- := nth_drop witness (size SS2.KeyUpdating.O_CMA_Default.qs{2}) enum  0; 1: by smt(size_ge0).
  pose xx := nth witness (drop (size SS2.KeyUpdating.O_CMA_Default.qs{2}) enum) 0. 
  have : !xx \in (elems (fdom RF.m{1})); last by smt(mem_fdom).
  have : !xx \in take (size SS2.KeyUpdating.O_CMA_Default.qs{2}) enum; last by smt(perm_eq_mem). 
  have : xx \in drop (size SS2.KeyUpdating.O_CMA_Default.qs{2}) enum by smt (size_ge0 mem_nth size_drop).
  by smt(enum_uniq cat_take_drop cat_uniq).
wp;call(_: ={glob SS2.RO.QRO}); 1: by sim.
auto => /> &1 &2 ??????rr?;split. 
+ by congr;congr => /=;rewrite get_set_eqE 1:/#. 
move => *; do split. 
+ by rewrite get_set_eqE 1:/#. 
+ by smt(size_rcons drop_size size_drop SSSt.KeyUpdating.ge0_qefcma). 
+ by rewrite !size_rcons /#.
+ by rewrite !size_rcons /#.
+ by rewrite size_rcons /=.
+ by move => mm; rewrite !mem_rcons /= /#. 
+ rewrite size_rcons /=.
  rewrite fdom_set /=. 
  have /= <- := nth_drop witness (size SS2.KeyUpdating.O_CMA_Default.qs{2}) enum  0; 1: by smt(size_ge0).
  pose xx := nth witness (drop (size SS2.KeyUpdating.O_CMA_Default.qs{2}) enum) 0. 
  have -> : (take (size SS2.KeyUpdating.O_CMA_Default.qs{2} + 1) enum) = 
     (take (size SS2.KeyUpdating.O_CMA_Default.qs{2}) enum) ++ [xx].
  + rewrite (take_nth witness); 1:smt(drop_size size_drop SSSt.KeyUpdating.ge0_qefcma).
    rewrite cats1 /= /xx; congr.
    by rewrite (drop_nth witness) /=; 1:smt(drop_size size_drop SSSt.KeyUpdating.ge0_qefcma).
  have  : perm_eq  (elems (fdom RF.m{1} `|` fset1 xx)) (elems (fdom RF.m{1}) ++ [xx]);
   last by  smt(perm_cat2r perm_eq_trans perm_eq_sym).
  have :! xx \in (take (size SS2.KeyUpdating.O_CMA_Default.qs{2}) enum).
  + have : xx \in drop (size SS2.KeyUpdating.O_CMA_Default.qs{2}) enum by smt (size_ge0 mem_nth size_drop).
    by smt(enum_uniq cat_take_drop cat_uniq).
  rewrite setUE /= elems_fset1 /=. 
  move => H; have := oflist_uniq  (elems (fdom RF.m{1}) ++ [xx]) _; last by rewrite perm_eq_sym. 
  rewrite cat_uniq uniq_elems /=.
  by smt (perm_eq_mem).
qed.
end section.

theory ROM_PROOF.

import ROM_PROOF.

module type Scheme_RO_C_Idx(R : SS2.RO.ROM_.POracle)  = {
  proc keygen(): pk_s * sk_s
  proc sign(sk : sk_s, m : msg_l):  (sig_l * idx) option * sk_l
  proc verify(pk : pk_s, m : msg_l, sig : (sig_l * idx) option): bool 
}.

(*
module (HS_idx_C(Sig : Scheme_RO_C, PRF : PseudoRF) : Scheme_RO_C_Idx) (O : SS2.RO.ROM_.POracle) = {
  proc keygen(): pk_s * sk_s = {
    var sk;
    (HS_idx.pk,sk) <@ Sig(O_l2s_C(O)).keygen();
    HS_idx.k <$ dK;
    HS_idx.used <- 0;
    return (HS_idx.pk,sk);
  }  
  
  proc sign(sk : sk_l, m : msg_l): (sig_l * idx) option * sk_l = {
    var sig_sk, ms, r, sig, result,i;
    
    result <- (None, sk);
    if (HS_idx.used < nIndices) {
       i <- nth witness enum HS_idx.used;
       r <@ PRF.f(HS_idx.k,i); 
       ms <@ ROmsg_C(O).o(r, (get_root_pk HS_idx.pk, i, m));
       sig_sk <@ Sig(O_l2s_C(O)).sign(sk, ms);
       sig <- ((r,sig_sk.`1),i);
       HS_idx.used <- HS_idx.used + 1; 
       result <- (Some sig, sig_sk.`2);
    }
    return result;
  }
  
  (* Cannot use state! *)
  proc verify(pk : pk_l, m : msg_l, sig : (sig_l * idx) option): bool = {
    var b,ms;
    b <- false;
    if (sig<>None) {
       ms <@ ROmsg_C(O).o((oget sig).`1.`1,  (get_root_pk pk, (oget sig).`2, m));
       b <@ Sig(O_l2s_C(O)).verify(pk, ms, (oget sig).`1.`2);
    }
    return b;
  }
}.
*)
module HS_idx_Red1(Sig : Scheme_RO_C, F : PRF_Oracles, O : SS2.RO.ROM_.POracle) = {
  proc keygen(): pk_s * sk_s = {
    var sk;
    (HS_idx.pk,sk) <@ Sig(O_l2s_C(O)).keygen();
    HS_idx.k <$ dK;
    HS_idx.used <- 0;
    return (HS_idx.pk,sk);
  }  

  proc sign(sk : sk_l, m : msg_l): (sig_l * idx) option * sk_l = {
    var sig_sk, ms, r, sig, result,i;
    
    result <- (None,sk);
    if (HS_idx.used < nIndices) {
       i <- nth witness enum HS_idx.used;
       r <@ F.f(i); 
       ms <@ ROmsg_C(O).o(r, (get_root_pk HS_idx.pk, i, m));
       sig_sk <@ Sig(O_l2s_C(O)).sign(sk, ms);
       sig <- ((r,sig_sk.`1),i);
       HS_idx.used <- HS_idx.used + 1; 
       result <- (Some sig, sig_sk.`2);
    }
    return result;
  }

  (* Cannot use state! *)
  proc verify(pk : pk_l, m : msg_l, sig : (sig_l * idx) option): bool = {
    var b : bool;
    var ms : msg_s;
    
    b <- false;
    if (sig<>None) {
       ms <@ ROmsg_C(O).o((oget sig).`1.`1,  (get_root_pk pk, (oget sig).`2, m));
       b <@ Sig(O_l2s_C(O)).verify(pk, ms, (oget sig).`1.`2);
    }
    return b;
  }

}.

(* Classical adversary *)
module type Adv_EFCMA_RO_C_Idx(R : SS2.RO.ROM_.POracle, O : SSSt.KeyUpdating.SOracle_CMA)  = {
  proc forge(pk : pk_l): msg_l * (sig_l * idx) option
}.

module (AWrap_Idx(A : Adv_EFCMA_RO_C_Idx) : SSSt.LIS.Adv_EFCMA_RO) (R : SS2.RO.QRO, O : SSSt.KeyUpdating.SOracle_CMA) = {

  module OC : SS2.RO.ROM_.POracle = {
    proc o(x : SS2.RO.from) : SS2.RO.hash = {
        var y;
        y <@ R.h{x};
        return y;
    }
  }

  proc forge(pk : pk_l): msg_l * (sig_l * idx) option = {
     var r;
     r <@ A(OC,O).forge(pk);
     return r;
  }
}.

module (SWrap_Idx(S : Scheme_RO_C_Idx) : SSSt.LIS.Scheme_RO) (R : SS2.RO.QRO) = {

  module OC : SS2.RO.ROM_.POracle = {
    proc o(x : SS2.RO.from) : SS2.RO.hash = {
        var y;
        y <@ R.h{x};
        return y;
    }
  }

  proc keygen(): pk_s * sk_s = {
     var r;
     r <@ S(OC).keygen();
     return r;
  }

  proc sign(sk : sk_s, m : msg_l): (sig_l * idx) option * sk_l = {
     var r;
     r <@ S(OC).sign(sk,m);
     return r;
  }

  proc verify(pk : pk_s, m : msg_l, sig : (sig_l * idx) option ): bool  = {
     var r;
     r <@ S(OC).verify(pk,m,sig);
     return r;

  }


}.
module (B2_C(A : Adv_EFCMA_RO_C_Idx): Adv_EFCMA_RO_C) (R : SS2.RO.ROM_.POracle, O : SS2.KeyUpdating.SOracle_CMA) = {
  module HS_idx_Red2 = {
     var _pk : pk_s

     proc keygen(): pk_s * sk_s = {
       return (_pk,witness);
    }  

    proc sign(ms : sk_l * msg_l):  (sig_l * idx) option * sk_l = {
      var sig_sk,  sig, i, result;
      result <- (None, witness);
      if (HS_idx.used < nIndices) {
         i <- nth witness enum HS_idx.used;
         sig_sk <@ O.sign((get_root_pk HS_idx.pk, i, ms.`2));
         sig <- (sig_sk,i);
         HS_idx.used <- HS_idx.used + 1;
         result <- (Some sig,witness);
    }
    return result;
  }

  proc verify(pk : pk_l, m : msg_l, sig : (sig_l * idx) option): bool = {
      return witness;
  }

  }

 proc forge(pk : pk_l): (root_s * idx * msg_l) * sig_l = { 
       var m,sig;
       HS_idx.k <- witness;
       HS_idx.used <- 0;
       HS_idx.pk <- pk;
       SSSt.KeyUpdating.O_CMA_Default.qs <- ([])%List;
       (m, sig) <@ SSSt.KeyUpdating.EF_CMA(HS_idx_Red2, A(R), SSSt.KeyUpdating.O_CMA_Default).A.forge(pk);
       return ((get_root_pk pk,(oget sig).`2,m),(oget sig).`1);
    }
}.

section.

(*
-SS1.KeyUpdating.O_RMA_Default, -SS1.RO.LE.ERO, -SS2.KeyUpdating.O_CMA_Default, -SS2.RO.ROM_.Lazy.LRO, -SS2.RO.LE.ERO, -QROm.ROM_.Lazy.LRO, -QROm.LE.ERO, -R_QRO.Wrapped_QRO, -R_QRO.RepO, -R_QRO.CLASSICAL.Wrapped_Oracle, -R_QRO.CLASSICAL.RepO, -R_QRO.QROM.QRO, -OverwriteByQRO_s, -QRO_l, -QRO_s, -QROmsg, -CountingA, -O_CMA_Repro, -Reduction, -O_CMA_Coll, -O_CMA_Coll_Simplified, -O_CMA_Game3, -O_CMA_Game3_red, -Game4, -R_QRO.QROM.LE.ERO
*)

(* For all adversaries A ... *)
declare module A <: Adv_EFCMA_RO_C_Idx {-SS1.KeyUpdating.O_RMA_Default, -SS2.KeyUpdating.O_CMA_Default, -R_QRO.Wrapped_QRO, -R_QRO.RepO, -R_QRO.QROM.QRO, -OverwriteByQRO_s, -QRO_l, -QRO_s, -QROmsg, -O_CMA_Repro, -Reduction, -O_CMA_Coll, -O_CMA_Game3, -O_CMA_Game3_red, -Game4, -PRF, -RF, -HS_idx, -SSSt.KeyUpdating.O_CMA_Default, -R_QRO.QROM.LE.ERO, -SS1.RO.LE.ERO, -QROm.ROM_.Lazy.LRO, -QROm.LE.ERO,-R_QRO.CLASSICAL.Wrapped_Oracle, -R_QRO.CLASSICAL.RepO,  -O_CMA_Coll_Simplified, -CountingA, -SS2.RO.ROM_.Lazy.LRO, -SS2.RO.LE.ERO}.
declare module S1 <: Scheme_RO_C {-A, -SS1.KeyUpdating.O_RMA_Default, -SS2.KeyUpdating.O_CMA_Default, -R_QRO.Wrapped_QRO, -R_QRO.RepO, -R_QRO.QROM.QRO, -OverwriteByQRO_s, -QRO_l, -QRO_s, -QROmsg, -O_CMA_Repro, -Reduction, -O_CMA_Coll, -O_CMA_Game3, -O_CMA_Game3_red, -Game4, -PRF, -RF, -HS_idx, -SSSt.KeyUpdating.O_CMA_Default, -R_QRO.QROM.LE.ERO, -SS1.RO.LE.ERO, -QROm.ROM_.Lazy.LRO, -QROm.LE.ERO,-R_QRO.CLASSICAL.Wrapped_Oracle, -R_QRO.CLASSICAL.RepO,  -O_CMA_Coll_Simplified, -CountingA, -SS2.RO.ROM_.Lazy.LRO, -SS2.RO.LE.ERO}.

(* How to express these ? *)
declare axiom forge_q  (O <: SS2.KeyUpdating.SOracle_CMA{-CountingA_C, -B2_C(A)} ) 
  (H0 <: SS2.RO.QRO {-CountingA_C, -B2_C(A)}):
  hoare[ AWrap(B2_C(A), CountingA(AWrap(B2_C(A)), H0, O).Ho, CountingA(AWrap(B2_C(A)), H0, O).S).forge :
          CountingA.cS = 0 /\ CountingA.cH = 0 ==> CountingA.cS <= qS /\ CountingA.cH <= qH].

declare axiom forge_q_C  (O <: SS2.KeyUpdating.SOracle_CMA{-CountingA_C, -B2_C(A)} ) 
  (H0 <: SS2.RO.ROM_.POracle {-CountingA_C, -B2_C(A)}):
  hoare[ B2_C(A, CountingA_C(B2_C(A), H0, O).Ho, CountingA_C(B2_C(A), H0, O).S).forge :
          CountingA.cS = 0 /\ CountingA.cH = 0 ==> CountingA.cS <= qS /\ CountingA.cH <= qH].

declare axiom S1_keygen_ll (O <: SS1.RO.ROM_.POracle {-S1}) : 
   islossless O.o => islossless S1(O).keygen.

declare axiom S1_sign_ll (O <: SS1.RO.ROM_.POracle {-S1}) : 
   islossless O.o => islossless S1(O).sign.

declare axiom S1_verify_ll (O <: SS1.RO.ROM_.POracle {-S1}) : 
   islossless O.o => islossless S1(O).verify.


declare axiom A_ll (RO <: SS2.RO.ROM_.POracle {-A}) (O <: SSSt.KeyUpdating.SOracle_CMA {-A}) : 
   islossless RO.o => islossless O.sign => islossless A(RO,O).forge.

module CA = AWrap_Idx(A).
module CS1 = SWrap(S1).

lemma final_statement_C_prelim &m: 
  qS = IDX.card =>
  (forall (OO <: SS1.RO.ROM_.POracle {-A}), islossless OO.o => islossless S1(OO).verify)  =>
  Pr[SSSt.LIS.EF_CMA_RO(HS_idx(CS1, PseudoRF), CA, SS2.RO.QRO, SSSt.KeyUpdating.O_CMA_Default).main() @ &m : res] 
  <=  `| Pr [ IND(PRF, B1(CS1,CA)).main() @ &m : res ] -
         Pr [ IND(RF, B1(CS1,CA)).main() @ &m : res ] |  + 
      Pr [SS2.LI.EF_CMA_RO(HS(CS1), AWrap(B2_C(A)), QRO_l, SS2.KeyUpdating.O_CMA_Default).main() @ &m : res] .
proof.
move => HqS Sll.
have := (final_statement CA CS1 &m HqS _).
by move => OO Hoo; proc; call(Sll (<:SWrap(S1, OO).OC)) => //; islossless.
have -> : Pr[SS2.LI.EF_CMA_RO(HS(CS1), B2(CA), SS2.RO.QRO, SS2.KeyUpdating.O_CMA_Default).main() @ &m : res] = Pr[SS2.LI.EF_CMA_RO(HS(CS1), AWrap(B2_C(A)), QRO_l, SS2.KeyUpdating.O_CMA_Default).main() @ &m : res]; last by smt().
byequiv => //.
proc;inline *.
wp; conseq  (_: _ ==> ={glob SS2.KeyUpdating.O_CMA_Default,r1,m}); 1: by smt().
call(_: ={glob SS2.RO.QRO}); 1: by sim. 
wp; conseq  (_: _ ==> ={pk,glob S1,glob SS2.RO.QRO,glob SS2.KeyUpdating.O_CMA_Default} /\ pk0{1} = pk2{2} /\ r0{1}.`1 = m2{2} /\ r0{1}.`2 = sig1{2}); 1: by smt().
call(_: ={glob SS2.RO.QRO, glob S1, glob SS2.KeyUpdating.O_CMA_Default, glob SSSt.KeyUpdating.O_CMA_Default, HS_idx.used, HS_idx.pk}); 1,2: by sim => />.  
auto => />.
call(_: ={glob SS2.RO.QRO}); 1: by sim. 
auto => />.
qed.

lemma final_statement_C_idx &m: 
  qS = IDX.card =>
  (forall (OO <: SS1.RO.ROM_.POracle {-A}), islossless OO.o => islossless S1(OO).verify)  =>
  Pr[SSSt.LIS.EF_CMA_RO(HS_idx(CS1, PseudoRF), CA, SS2.RO.QRO, SSSt.KeyUpdating.O_CMA_Default).main() @ &m : res] 
  <=  `| Pr [ IND(PRF, B1(CS1,CA)).main() @ &m : res ] -
         Pr [ IND(RF, B1(CS1,CA)).main() @ &m : res ] |  + 
  Pr[SS1.SI.I_EF_RMA_RO(SWrap(S1), Reduction(SS2.RO.QRO, AWrap(B2_C(A))), SS1.KeyUpdating.O_RMA_Default, SS1.RO.QRO).main() @ &m : res]
     + qS%r * ((qS + qH + 1)%r * mu1 dr_t witness)
     + ((qH + qS + 3) * (qH + qS + 2))%r / 2%r * mu1 dmsg_s witness.
proof.
move => HqS Sll.
have H := final_statement_C_prelim &m HqS Sll.
have H2 := final_statement_C (B2_C(A)) S1 forge_q forge_q_C S1_keygen_ll S1_sign_ll S1_verify_ll _ &m.
+ move => RO O HRO Hsign;proc;inline *.
  call (A_ll (RO) (<:SSSt.KeyUpdating.O_CMA_Default(B2_C(A, RO, O).HS_idx_Red2))).
  proc;inline *;wp;sp;if => //;wp; call  Hsign; by auto => />.
  by auto => />.
smt().
qed.

end section.
end ROM_PROOF.

