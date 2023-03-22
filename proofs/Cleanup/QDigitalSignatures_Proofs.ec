(************************************) 
(*  This file contains proofs for   *) 
(*  generic transforms of signature *)
(*  schemes.                        *)
(************************************) 


require import AllCore List Distr DProd RealExp StdOrder SmtMap.
require (*--*) QDigitalSignaturesRO.

(*-- query bounds --*)
op qS : { int | 0 <= qS } as ge0_qS.
op qH : { int | 0 <= qH } as ge0_qH.  

(*****************************************************)
(*** Definition for short-message signature scheme ***)
(*****************************************************)

(* -- Types -- *)
type msg_s.
type sig_s.
type pk_s.
type sk_s.


(* --- Distributions --- *)
op [lossless full uniform] dmsg_s : msg_s distr.

(* ---  signature scheme --- *)
clone QDigitalSignaturesRO as SS1 with
  type msg_t <- msg_s,
  type sig_t <- sig_s,
  type pk_t <- pk_s,
  type sk_t <- sk_s,
  
  op KeyUpdating.n_efrma <- qS,
  
  op dmsg <- dmsg_s
  
  proof dmsg_ll by exact: dmsg_s_ll 
  proof KeyUpdating.ge0_nefrma by exact: ge0_qS
   
  rename [theory] "KeyUpdating_RO" as "SI". 

(* -- short-hands for RO of SI -- *)  
module type QRO_s_t = { include SS1.RO.QRO }.
module QRO_s = SS1.RO.QRO.


(*****************************************************)
(*** Definition for long-message signature scheme  ***)
(*****************************************************)
    
(* -- Types -- *)
(* Types for long message signature scheme *)
type msg_l.
type r_t. (* "salt" == randomness for hashing *)
type sig_l = r_t * sig_s.
type pk_l = pk_s.
type sk_l = sk_s.

(* --- Distributions --- *)
op [lossless full uniform] dmsg_l : msg_l distr.
op [lossless full uniform] dr_t : r_t distr.


(* -- types for QRO_l -- *)
(* ----------------------
  This is more interesting as QRO_l will have to 
  be used for the message compression QROmsg as 
  well as for QRO_s 
  ------------------------- *)
(* There should be generic support for this -> redo SplitRO for QROM?  *)
type ro_in = bool * SS1.RO.from * r_t * msg_l.
type ro_out = SS1.RO.hash * msg_s.
op ro_dhash = SS1.RO.dhash `*` dmsg_s.

(* -- The target: long input signature scheme -- *)   
clone QDigitalSignaturesRO as SS2 with
  type msg_t <- msg_l,
  type sig_t <- sig_l,
  type pk_t <- pk_l,
  type sk_t <- sk_l,
  type RO.from <= ro_in,
  type RO.hash <= ro_out,
  type RO.ROM_.d_in_t <= int, 
  op RO.dhash <= ro_dhash,
  op KeyUpdating.q_efcma <- qS,
    
  op dmsg <- dmsg_l
  
  proof dmsg_ll by exact: dmsg_l_ll
  proof KeyUpdating.ge0_qefcma by exact: ge0_qS
  
  rename [theory] "KeyUpdating_RO" as "LI".

  (* -- shorthand for QRO of LI -- *)
module type QRO_l_t = { include SS2.RO.QRO }.
module QRO_l = SS2.RO.QRO.

(*****************************************************)
(*** More QROM tooling                             ***)
(*****************************************************)

(* -- Message compression QROM -- *)  
require T_QROM.
clone T_QROM as QROm with
  type from <= r_t * msg_l,
  type hash <= msg_s,
  op dhash <= dmsg_s.
  
module type QROmsg_t = { include QROm.QRO }.
module QROmsg = QROm.QRO.

clone QROm.Collision as Coll with
  op q <- (qH + qS + 1).

op coDom =  mu1 QROm.dhash witness.

op sample_dist (m: msg_l) =  
  (dmap 
    dr_t (fun r  => ((false, witness<:SS1.RO.from>, r, m), tt))).

(* -- Reprogrammable QROM -- *)  
require T_Repro.
clone T_Repro as R_QRO with
  op rep_ctr <= qS,
  op query_ctr <= qS + qH + 1,
  op p_max_bound <= mu1 dr_t witness, 
  theory QROM <= SS2.RO,
  type side <= unit
  proof rep_ctr_ge0, query_ctr_ge0.
realize rep_ctr_ge0 by apply ge0_qS.
realize query_ctr_ge0 by smt(Coll.ge0_q).

lemma p_max_val mm : R_QRO.p_max (dmap dr_t (fun (r0 : r_t) => ((false, witness, r0, mm), tt))) = mu1 dr_t witness.
proof.
have : R_QRO.p_max (dmap dr_t (fun (r0 : r_t) => ((false, witness, r0, mm), tt))) <= mu1 dr_t witness.
+ have := listmax_in Real.(<=) _ _ 0%r 
   (map
     (fun (x : SS2.RO.from) =>
        mu (dmap dr_t (fun (r0 : r_t) => ((false, witness, r0, mm), tt)))
          (fun (p : SS2.RO.from * unit) => x = p.`1)) SS2.RO.MUFF.FinT.enum).
  + by apply RealOrder.ler_trans. + by apply RealOrder.ler_total.
  rewrite size_map /p_max.
  have := SS2.RO.MUFF.FinT.enumP witness.
  case: SS2.RO.MUFF.FinT.enum => // x l _ /(_ _); 1: smt(size_ge0).
  move: (x :: l) => enum /mapP [x1] /= [ ? ->].
  rewrite dmapE /(\o) /= (dr_t_uni witness x1.`3) 1,2: dr_t_fu.
  by apply mu_le => />.
have /#: mu1 dr_t witness <= R_QRO.p_max (dmap dr_t (fun (r0 : r_t) => ((false, witness, r0, mm), tt))).
apply : RealOrder.ler_trans (R_QRO.p_maxE (dmap dr_t (fun (r0 : r_t) => ((false, witness, r0, mm), tt))) (false, witness, witness, mm)).
by rewrite dmapE /(\o) /= /pred1; apply mu_le => />.
qed.

lemma p_max_aux m m' : R_QRO.p_max (dmap dr_t (fun (r0 : r_t) => ((false, witness, r0, m), tt))) =
                       R_QRO.p_max (dmap dr_t (fun (r0 : r_t) => ((false, witness, r0, m'), tt))).
proof. by rewrite !p_max_val; smt(). qed.

module type QROrep_t = { include R_QRO.QROM.QRO }.
module QROrep = R_QRO.QROM.QRO.

(* -- wrapper that turns a QRO_l into a QRO_s -- *)  
module O_l2s (O: QRO_l_t) : QRO_s_t = {  
  quantum proc h { m: SS1.RO.from } = {
    quantum var out;
    out <@ O.h {(true, m, witness, witness)};
    return out.`1;
  }
}.

(* -- wrapper that turns a QRO_l into a ROmsg -- *)  
module ROmsg (O: QRO_l_t) : QROmsg_t = {  
  quantum proc h { rm: r_t * msg_l } = {
    quantum var out;
    out <@ O.h {(false, witness, rm.`1, rm.`2)};
    return out.`2;
  }
}.

(*-- RO Combiner that takes a QRO_l and a QRO1 and implements a QRO_l --*)
(* It overwrites the QRO_l on the function that O_l2s extracts with QRO1 *)
module OverwriteByQRO_s (Os : QRO_s_t, Ol: QRO_l_t) : QRO_l_t = {
  
  quantum proc h {m : ro_in} = {
    quantum var out : ro_out;
    quantum var outl : ro_out;
    quantum var outs : SS1.RO.hash;
    outs <@ Os.h {m.`2}; 
    outl <@ Ol.h {m};
    
    out <- if (m.`1 /\ m.`3 = witness /\ m.`4 = witness) then (outs, outl.`2) else outl;
    return out;
  }
}.

(*-- RO Combiner that takes a QRO_l and a QROmsg and implements a QRO_l --*)
(* It overwrites the QRO_l on the function that ROmsg extracts with QROmsg *)
module OverwriteByQROmsg (Os : QROmsg_t, Ol: QRO_l_t) : QRO_l_t = {
  
  quantum proc h {m : ro_in} = {
    quantum var out : ro_out;
    quantum var outl : ro_out;
    quantum var outs : msg_s;
    outs <@ Os.h {(m.`3, m.`4)}; 
    outl <@ Ol.h {m};
    
    out <- if (!m.`1 /\ m.`2 = witness) then (outl.`1, outs) else outl;
    return out;
  }
}.

(*****************************************************)
(*** RO DIstinguishing Game                        ***)
(*****************************************************)

(*-- Distinguisher for different ROs --*)
quantum module type RO_Distinguisher (G : QRO_l_t) = {
  proc distinguish( ): bool
}.

(*-- Distinguishing Game for QRO_s Overwrites --*)
module DistGameOverwriteS (D: RO_Distinguisher) = {
  (*-- case1: plain T2 oracle --*)
  proc left () : bool = {
    var out; 
    
    QRO_l.init();
    out <@ D(QRO_l).distinguish();
    return out;
  }
  
  (*-- case2: Overwrite T2 oracle --*)
  proc right () : bool = {
    var out;
    
    QRO_l.init();
    QRO_s.init();
    
    out <@ D(OverwriteByQRO_s(QRO_s, QRO_l)).distinguish();
    return out;
  }
}.


(*-- Distinguishing Game for QROmsg Overwrites --*)
module DistGameOverwriteM (D: RO_Distinguisher) = {
  (*-- case1: plain T2 oracle --*)
  proc left () : bool = {
    var out; 
    
    QRO_l.init();
    out <@ D(QRO_l).distinguish();
    return out;
  }
  
  (*-- case2: Overwrite T2 oracle --*)
  proc right () : bool = {
    var out;
    
    QRO_l.init();
    QROmsg.init();
    
    out <@ D(OverwriteByQROmsg(QROmsg, QRO_l)).distinguish();
    return out;
  }
}.

(************************************************************************************************)
(*-- Proof that OverwriteByQRO_s simulates a good QRO_l --*)
(************************************************************************************************)
section QRO_PROOFS.
  declare module D <: RO_Distinguisher { -QRO_s, -QRO_l, -QROmsg, -OverwriteByQRO_s }.
 
 (***------------------------- Proof for QRO_s-----------------------------------------------***)

  

  (*-- auxiliary module needed in the proof --*)
  module Aux = {
     var h : ro_in -> ro_out
   
     proc aux() = {
       SS2.RO.QRO.h <$ SS2.RO.dfhash;
       SS1.RO.QRO.h <$ SS1.RO.dfhash;
       h <- fun (_x : ro_in) => if _x.`1 /\ _x.`3 = witness /\ _x.`4 = witness then
        (SS1.RO.QRO.h _x.`2, (SS2.RO.QRO.h _x).`2)
          else SS2.RO.QRO.h _x;
    } 
  }.

   local clone import Dfun_sub as Dfun_sub1 with 
      type A <- ro_in,
      type C <- SS1.RO.from, 
      theory MA <= SS2.RO.MUFF,
      theory MC <= SS1.RO.MUFF.

  lemma fun_dist_equiv_s:
    dlet SS2.RO.dfhash
      (fun (h : ro_in -> ro_out) =>
         dmap SS1.RO.dfhash
           (fun (h0 : SS1.RO.from -> SS1.RO.hash) (_x : ro_in) =>
              if _x.`1 /\ _x.`3 = witness /\ _x.`4 = witness then
                (h0 _x.`2, (h _x).`2)
              else h _x))
    =
    dmap SS2.RO.dfhash (fun (h : ro_in -> ro_out) => h).  
  proof.
    rewrite dmap_id /SS2.RO.dfhash /ro_dhash.
    rewrite R_QRO.QROM.MUFF.dfun_prodE dlet_dmap dprodC dlet_dmap dmap_comp dprod_dlet dmap_dlet dlet_dlet.
    apply eq_dlet => //= f2.
    rewrite dlet_dlet dmap_dlet/=.
    have {2}-> : 
      (fun (_ : SS2.RO.from) => SS1.RO.dhash) = 
      (fun (x : ro_in) => if x.`1 /\ x.`3 = witness /\ x.`4 = witness then SS1.RO.dhash else SS1.RO.dhash) by done.
    rewrite -SS2.RO.MUFF.dfun_condE /= 1,2:SS1.RO.dhash_ll.
    rewrite dmap_dprodE_swap dlet_dlet; apply eq_dlet => //= ff.
    rewrite dlet_unit /= dlet_dmap /dmap  /(\o) /= /SS1.RO.dfhash.
    rewrite (dfun_extend (fun _ => SS1.RO.dhash) 
             (fun (x : ro_in) => x.`1 /\ x.`3 = witness /\ x.`4 = witness)
             (fun (x: ro_in) => x.`2) 
             (fun (x2:SS1.RO.from) => (true, x2, witness<:r_t>, witness<:msg_l>))) //= ?SS1.RO.dhash_ll // 1:/#.
    rewrite dlet_dmap; apply eq_dlet => // ft /=.
    rewrite dlet_unit /=; congr; apply fun_ext => x /= => /#. 
  qed.
 
  equiv RO_comb_s: 
    DistGameOverwriteS(D).left ~ DistGameOverwriteS(D).right : 
      ={glob D} ==> ={res, glob D}.

  proof.
    proc.      
    inline*.
    call(_ : SS2.RO.QRO.h{1} = fun (_x : ro_in) =>  if (_x.`1 /\ _x.`3 = witness /\ _x.`4 = witness) then (SS1.RO.QRO.h{2} (_x.`2), (SS2.RO.QRO.h{2} _x).`2) else SS2.RO.QRO.h{2} _x).
    proc. inline*. auto => />.
    conseq />. swap {2} 2 1. seq 1 2 : true. auto.
    transitivity{2} {Aux.aux();} (true ==> SS2.RO.QRO.h{1} = Aux.h{2})
      (true ==> Aux.h{1} = fun (_x : ro_in) =>
         if _x.`1 /\ _x.`3 = witness /\ _x.`4 = witness then
          (SS1.RO.QRO.h{2} _x.`2, (SS2.RO.QRO.h{2} _x).`2)
         else SS2.RO.QRO.h{2} _x).    
    + by auto.
    + by auto => />.
    + inline*. rnd : *0 *0. auto.
      rewrite fun_dist_equiv_s. by smt().   
    inline*. auto => />.    
    qed.      
   
  lemma pr_RO_comb_s &m: 
   Pr[DistGameOverwriteS(D).left() @ &m : res] = Pr[ DistGameOverwriteS(D).right() @ &m : res].
  proof. 
     by byequiv RO_comb_s. qed.    
     
     
  (***------------------------- Proof for QRO_msg-----------------------------------------------***)

  (*-- auxiliary module needed in the proof --*)
  module Aux_M = {
     var h : ro_in -> ro_out
   
     proc aux() = {
       SS2.RO.QRO.h <$ SS2.RO.dfhash;
       QROmsg.h <$ QROm.dfhash;
       h <- fun (_x : ro_in) => if (! _x.`1) /\ _x.`2 = witness then
        ((SS2.RO.QRO.h _x).`1, (QROm.QRO.h (_x.`3, _x.`4)))
          else SS2.RO.QRO.h _x;
    } 
  }.
  
   local clone import Dfun_sub as Dfun_sub2 with 
      type A <- ro_in,
      type C <- QROm.from, 
      theory MA <= SS2.RO.MUFF,
      theory MC <= QROm.MUFF.
        
  lemma fun_dist_equiv_m:
    dlet SS2.RO.dfhash
      (fun (h : ro_in -> ro_out) =>
         dmap QROm.dfhash
           (fun (h0 : QROm.from -> QROm.hash) (_x : ro_in) =>
              if ! _x.`1 /\ _x.`2 = witness then
                ((h _x).`1, h0 (_x.`3, _x.`4) )
              else h _x))
    =
    dmap SS2.RO.dfhash (fun (h : ro_in -> ro_out) => h).  
  proof.
    rewrite dmap_id /SS2.RO.dfhash /ro_dhash.
    rewrite R_QRO.QROM.MUFF.dfun_prodE dlet_dmap /dmap_comp dprod_dlet dmap_dlet dlet_dlet.
    apply eq_dlet => //= f2.
    rewrite dlet_dlet dmap_dlet/=.
    have {2}-> : 
      (fun (_ : SS2.RO.from) => dmsg_s) = 
      (fun (x : ro_in) => if !x.`1 /\ x.`2 = witness then dmsg_s else dmsg_s) by done.
    rewrite -SS2.RO.MUFF.dfun_condE /= 1,2:dmsg_s_ll.
    rewrite dmap_dprodE_swap dlet_dlet; apply eq_dlet => //= ff.
    rewrite dlet_unit /= dlet_dmap /dmap  /(\o) /= /QROm.dfhash.
    rewrite (dfun_extend (fun _ => dmsg_s) 
             (fun (x : ro_in) => !x.`1 /\ x.`2 = witness)
             (fun (x: ro_in) => (x.`3, x.`4)) 
             (fun (x2:QROm.from) => (false, witness<:SS1.RO.from>, x2.`1, x2.`2))) //= ?dmsg_s_ll // 1:/#.
    smt().
    rewrite dlet_dmap; apply eq_dlet => // ft /=.
    rewrite dlet_unit /=; congr; apply fun_ext => x /= => /#. 
  qed.  
   
  equiv RO_comb_m: 
    DistGameOverwriteM(D).left ~ DistGameOverwriteM(D).right : 
      ={glob D} ==> ={res, glob D}.

  proof.
    proc.      
    inline*.
    call(_ : SS2.RO.QRO.h{1} = fun (_x : ro_in) =>  if (!_x.`1 /\ _x.`2 = witness) 
                                   then ((SS2.RO.QRO.h{2} _x).`1, QROm.QRO.h{2} ((_x.`3, _x.`4))) else SS2.RO.QRO.h{2} _x).
    proc. inline*. auto => />.
    conseq />. swap {2} 2 1. seq 1 2 : true. auto.
    transitivity{2} {Aux_M.aux();} (true ==> SS2.RO.QRO.h{1} = Aux_M.h{2})
      (true ==> Aux_M.h{1} = fun (_x : ro_in) =>
         if ! _x.`1 /\ _x.`2 = witness then
           ((SS2.RO.QRO.h{2} _x).`1, QROm.QRO.h{2} (_x.`3, _x.`4))
         else SS2.RO.QRO.h{2} _x).    
    + by auto.
    + by auto => />.
    + inline*. rnd : *0 *0. auto.
      rewrite fun_dist_equiv_m. by smt().   
    inline*. auto => />.    
    qed.      
   
  lemma pr_RO_comb_m &m: 
   Pr[DistGameOverwriteM(D).left() @ &m : res] = Pr[ DistGameOverwriteM(D).right() @ &m : res].
  proof. 
     by byequiv RO_comb_m. qed.        
     
     
end section QRO_PROOFS.
(************************************************************************************************)


(******************************************************************************************)
(*** Constructing a long-message signature scheme from a short-message one: Hash & Sign ***)
(******************************************************************************************)
(* ----------------------------------------------
   Compresses long message to short message using 
   ROmsg, then uses short input length scheme Sig.
   ---------------------------------------------- *)
module (HS (Sig : SS1.SI.Scheme_RO) : SS2.LI.Scheme_RO) (O : QRO_l_t) : SS2.KeyUpdating.Scheme = {
 
  proc keygen = Sig(O_l2s(O)).keygen
  (* proc keygen () : pk_l * sk_l = {
    var sk_pk;
    sk_pk <@ Sig(O_l2s(O)).keygen();
    return sk_pk;
  } *) 
  proc sign(sk : sk_l, m : msg_l) : sig_l * sk_l = {
    var sig_sk, ms, r;
    
    r <$ dr_t;
    ms <@ ROmsg(O).h {(r,m)};
    sig_sk <@ Sig(O_l2s(O)).sign(sk, ms);
    
    return ((r, sig_sk.`1), sig_sk.`2);
  }
  
  proc verify(pk : pk_l, m : msg_l, sig : sig_l) : bool = {
     var b, ms;
     
     ms <@ ROmsg(O).h {(sig.`1, m)};
     b  <@ Sig(O_l2s(O)).verify(pk, ms, sig.`2); 
     return b;
  }
}.





(******************************************************************************************)
(*** Reduction from CMA to RMA                                                          ***)
(******************************************************************************************)

  (* Helper module to count queries made by A *)
  module (CountingA (A : SS2.LI.Adv_EFCMA_RO) : SS2.LI.Adv_EFCMA_RO) (H : SS2.RO.QRO) (O : SS2.KeyUpdating.SOracle_CMA) = {
    var cH : int
    var cS : int
    
    module Ho = {
      quantum proc h{x} = {
        quantum var r <- witness;

        r  <@ H.h{x};
        cH <- cH + 1;
        return r;
      }
    }

    module S = {
      proc sign(m) = {
        var r <- witness;

        r  <@ O.sign(m);
        cS <- cS + 1;
        return r;
      }
    }

    proc forge(pk) = {
      var r;

      cH <- 0;
      cS <- 0;
      r  <@ A(Ho,S).forge(pk);
      return r;
    }
  }.


(* 
  Reduction Oracle 
*)
module (O_CMA_Repro (O: R_QRO.QRO_r, SO: SS1.KeyUpdating.SOracle_RMA): SS2.KeyUpdating.SOracle_CMA) = {
  var qs : msg_l list
  var msgs: ( msg_s * (r_t*msg_l)) list
  
  (* Initialize *)
  proc init() : unit = {
    qs <- [];
    msgs <- [];
  }

  (* 
    Sign given message m using the list of message-signature pairs
    given at init time.
  *)
  proc sign(m : msg_l) : sig_l = {
    var r : r_t;
    var sig : sig_l;
    var s_sig : sig_s;
    var msg : msg_s;
    var tmp;
    
    r <$ dr_t;
    tmp <$ SS1.RO.dhash;
    (msg, s_sig) <@ SO.sign();
    
    O.set((false, witness,r,m), (tmp, msg));
    O.h{(false, witness,r,m)};
    sig <- (r, s_sig);

    qs <- rcons qs m;
    msgs <- rcons msgs (msg,(r,m));
            
    return sig;
  }

  proc fresh(m : msg_l) : bool = { return ! m \in qs; }
  proc nr_queries() : int = { return size qs;}
  proc msgs() :(msg_s * (r_t*msg_l)) list = { return msgs;} 
}.

(*-- Reduction that breaks I_EFRMA_RO given an adversary against EFCMA_RO.  --*)
(* 
   The reduction right now is with respect to a QRO_l_t oracle. This is not a 
   limitation as such an oracle can be simulated using a 2q-wise independent 
   hash function 
*)
module (Reduction (RO2 : SS2.RO.QRO_i, A: SS2.LI.Adv_EFCMA_RO) : SS1.SI.Adv_I_EFRMA_RO)  (RO1 : QRO_s_t, SO: SS1.KeyUpdating.SOracle_RMA) = {
   module R = OverwriteByQRO_s(RO1,R_QRO.Wrapped_QRO(RO2))
   module O = O_CMA_Repro(R_QRO.Wrapped_QRO(RO2), SO)
    
   var coll : bool
    
   proc forge(pk : pk_s) : msg_s * sig_s = {
     var msig, sig, m, msgs;
     
     RO2.init();
     R_QRO.Wrapped_QRO(RO2).init();
     O.init();
     
     msig <@ A(R,O).forge(pk);
     m <@ ROmsg(R_QRO.Wrapped_QRO(RO2)).h {(msig.`2.`1, msig.`1)};
     sig <- msig.`2.`2;
     
     msgs <@ O.msgs();
     coll <- (assoc msgs m <> None);
     return (m,sig);
   }
}.




(* ----------------------------------- The proof begins --------------------------------- *)
(*
Proof outline: 
  We want to prove that 
     Pr [EF_CMA_RO(HS(S1), A).main() @ &m : res] 
     = Pr [I_EF_RMA_RO(S1, Reduction(A)] - Pr[Coll in RO] - Pr[Dectecting Reprogramming].     
 The high level proof idea is as follows:
 * We first make a case distinction between forgeries that include a collision in the message hash and those that don't
 * In case there is a collision, we show how to use the forger to find collisions in a random oracle
 * In case there is no collison, we show how to use the forger to creat a forgery for S1. 
  
 Our proof proceeds in XXX Games:
 - Game0 = EF_CMA_RO
 - GameX is euqal to Game0 but adds a collision check. For that it uses a different oracle that keeps track 
   of the hashes computed during sign queries. The game then computes if the forgery collides with one of 
   these and puts it into a boolean coll. The switch here is information theoretically undetectable as it does not
   change the behavior towards the adversary in any way.
 * Here we split the probability and progress in two branches, one conditioned on coll and one conditioned on !coll
 * In the collision branch we proceed as follows:   
 - GameC1 takes a ROmsg oracle and "programs" it into the long-input RO as to later extract a collision for that external RO.
   We show that stepping from GameX to GameC1 is information theoretically undetectable by linking it to the 
   oracle-distinguishing game DistGameOverwriteM above   
 - CollisionFinder instead of returning true or false dependent on the success of the forger in GameC1 outputs 
   the found collision if one is found. Given that we are in the coll branch, this is always the case. Towards the adversary 
   the game does not change 
 * in the !coll branch we proceed as follows:
 - Game1 adds a reprogramming that replaces the S1-RO by an externally given RO. This follows the same argument as 
   the step to GameC1 above. The reason we are doing this is that in a later step we want to use an externally given S1 
   signature scheme that comes with its own RO which we have to be consistent with.
 - Game1Prime directly uses the externally given RO_s whenever we would use a projection to the S1 part of an oracle where 
   we programmed RO_s into the S1 part.  
 - Game2 wrapps the given combined random oracle (RO_l) into a reprogramming wrapper. This is unnoticeable if no programming happens.
 - Game3, instead of hashing in the signing oracle first samples a random element from the range of the RO and 
   then reprograms the RO to be consistent with it. We show this is unnoticable by the adversary up to a distinguishing bound 
   for the reprogramming game by linking it to that game.
 - Game4 does not use a secret key to sign messages anymore but an external I_EF_RMA oracle. As the messages signed by that 
   oracle are also uniformly random elements of the range of ROmsg, this change is perfectly indistinguishable by the adversary
 - Reduction when run in the I_EF_RMA_RO game does the same as Game4 but instead of outputting whether the adversary wins, 
   it outputs a forgery for S1. We show that whenever Game4 indicates a win of the adversary, and !coll, 
   Reduction will output a valid forgery.
*)

(*---------------------------- GameX -----------------------------------------------------*)
module (O_CMA_Coll (S1: SS1.SI.Scheme_RO, O: SS2.RO.QRO): SS2.KeyUpdating.SOracle_CMA)  = {
  var sk : sk_l
  var qs : msg_l list
  var msgs: ( msg_s * (r_t*msg_l)) list
  
  (* Initialize *)
  proc init (sk_init : sk_l) : unit = {
    sk <- sk_init;
    qs <- [];
    msgs <- [];
  }

  (* 
    Sign using sk but implementing the hash & sign scheme above as to be able to remember messages and hashes.
  *)
  proc sign(m : msg_l) : sig_l = {
    var r : r_t;
    var sig : sig_l;
    var msg_tmp;
    var sig_s;
    
    r <$ dr_t;
    msg_tmp <@ O.h{(false, witness,r,m)};
    (sig_s, sk) <@ S1(O_l2s(O)).sign(sk, msg_tmp.`2);
    sig <- (r, sig_s);

    qs <- rcons qs m;
    msgs <- rcons msgs (msg_tmp.`2,(r,m));
            
    return sig;
  }

  proc fresh(m : msg_l) : bool = { return ! m \in qs; }
  proc nr_queries() : int = { return size qs;}
  proc msgs() :(msg_s * (r_t*msg_l)) list = { return msgs;} 
}.

(*-- Helper Module that uses Reprogrammable Oracle --*)
module GameX(S : SS1.SI.Scheme_RO, A : SS2.LI.Adv_EFCMA_RO,
                 RO_l : SS2.RO.QRO_i) = {
  module S1 = S(O_l2s(RO_l))
  module O = O_CMA_Coll(S, RO_l)
  
  
  var coll: bool
     
  proc main(): bool = {
    
    var pk : pk_l;
    var sk : sk_l;
    var m : msg_l;
    var m_s : msg_s;
    var sig : sig_l;
    var nrqs : int;
    var is_valid, is_fresh : bool;
    var msgs;
      
    RO_l.init();
    
    (pk, sk) <@ S1.keygen();
      
    O.init(sk);
    (m, sig) <@ A(RO_l,O).forge(pk);

    m_s <@ ROmsg(RO_l).h{(sig.`1,m)};
    is_valid <@ S1.verify(pk, m_s, sig.`2);
    is_fresh <@ O.fresh(m);
    nrqs <@ O.nr_queries();
    
    msgs <@ O.msgs();
    coll <- (assoc msgs m_s <> None);      
    return nrqs <= qS /\ is_valid /\ is_fresh;
    
  }
}.

(* --- ************************************************
         Collision branch
       ************************************************ *)
         

(*-- Helper Module that uses Overwrite Oracle --*)
module GameC1(S : SS1.SI.Scheme_RO, A : SS2.LI.Adv_EFCMA_RO,
                 RO_l : SS2.RO.QRO_i, RO_m : QROm.QRO_i) = {
  module R = OverwriteByQROmsg(RO_m, RO_l)
  module S1 = S(O_l2s(R))
  module O = O_CMA_Coll(S, R)


  var coll: bool
       
  proc main(): bool = {
    
    var pk : pk_l;
    var sk : sk_l;
    var m : msg_l;
    var m_s : msg_s;
    var sig : sig_l;
    var nrqs : int;
    var is_valid, is_fresh : bool;
    var msgs;
    
    RO_m.init();  
    RO_l.init();
    
    (pk, sk) <@ S1.keygen();
      
    O.init(sk);
    (m, sig) <@ A(R,O).forge(pk);

    m_s <@ ROmsg(R).h{(sig.`1,m)};
    is_valid <@ S1.verify(pk, m_s, sig.`2);
    is_fresh <@ O.fresh(m);
    nrqs <@ O.nr_queries();
    
    msgs <@ O.msgs();
    coll <- (assoc msgs m_s <> None);      
    return nrqs <= qS /\ is_valid /\ is_fresh;
    
  }
}.


(* -- Reduction module that distinguishes the Overwrite 
      with probability |PR[GameX] - Pr[GameC1]|      --*)
module (R_Dist_m (S : SS1.SI.Scheme_RO, A : SS2.LI.Adv_EFCMA_RO) : RO_Distinguisher) (G: QRO_l_t) = {
 
 module S1 = S(O_l2s(G))
 module O = O_CMA_Coll(S, G)
  
 proc distinguish(): bool = {
    
    var pk : pk_l;
    var sk : sk_l;
    var m : msg_l;
    var m_s : msg_s;
    var sig : sig_l;
    var nrqs : int;
    var coll, is_valid, is_fresh : bool;
    var msgs;
      
    
    (pk, sk) <@ S1.keygen();
      
    O.init(sk);
    (m, sig) <@ A(G,O).forge(pk);

    m_s <@ ROmsg(G).h{(sig.`1,m)};
    is_valid <@ S1.verify(pk, m_s, sig.`2);
    is_fresh <@ O.fresh(m);
    nrqs <@ O.nr_queries();
    
    msgs <@ O.msgs();
    coll <- (assoc msgs m_s <> None);      
    return nrqs <= qS /\ is_valid /\ is_fresh /\ coll;
    
  }
}.

(*-- Adversary that finds a collision in a QROm --*)
module (CollisionFinderPrime(S : SS1.SI.Scheme_RO, A : SS2.LI.Adv_EFCMA_RO,
                 RO_l : SS2.RO.QRO_i) :  Coll.AdvCol) (RO_m : QROm.QRO) = {
  module R = OverwriteByQROmsg(RO_m, RO_l)
  module S1 = S(O_l2s(R))
  module O = O_CMA_Coll(S, R)

  var coll: bool
       
  proc main() = {
    
    var pk : pk_l;
    var sk : sk_l;
    var m : msg_l;
    var m_s : msg_s;
    var sig : sig_l;
    var nrqs : int;
    var is_valid, is_fresh : bool;
    var msgs;
    var x1, x2;
    
    RO_l.init();
    
    (pk, sk) <@ S1.keygen();
      
    O.init(sk);
    (m, sig) <@ CountingA(A,R,O).forge(pk);
    x1 <- (sig.`1,m);
    
    m_s <@ ROmsg(R).h{(sig.`1,m)};
    is_valid <@ S1.verify(pk, m_s, sig.`2);
    is_fresh <@ O.fresh(m);
    nrqs <@ O.nr_queries();
    
    msgs <@ O.msgs();    
    coll <- (assoc msgs m_s <> None);
    x2 <- oget (assoc msgs m_s);     
    return (x1, x2);
    
  }
}.

(*---------------------------- Collision oracle that hands S1 a dedicated QRO_s ------------------------------------------------*)
module (O_CMA_Coll_Simplified (S1: SS1.SI.Scheme_RO, O: SS2.RO.QRO, O_s: SS1.RO.QRO): SS2.KeyUpdating.SOracle_CMA)  = {
  var sk : sk_l
  var qs : msg_l list
  var msgs: ( msg_s * (r_t*msg_l)) list
  
  (* Initialize *)
  proc init (sk_init : sk_l) : unit = {
    sk <- sk_init;
    qs <- [];
    msgs <- [];
  }

  (* 
    Sign using sk but implementing the hash & sign scheme above as to be able to remember messages and hashes.
  *)
  proc sign(m : msg_l) : sig_l = {
    var r : r_t;
    var sig : sig_l;
    var msg_tmp;
    var sig_s;
    
    r <$ dr_t;
    msg_tmp <@ O.h{(false, witness,r,m)};
    (sig_s, sk) <@ S1(O_s).sign(sk, msg_tmp.`2);
    sig <- (r, sig_s);

    qs <- rcons qs m;
    msgs <- rcons msgs (msg_tmp.`2,(r,m));
            
    return sig;
  }

  proc fresh(m : msg_l) : bool = { return ! m \in qs; }
  proc nr_queries() : int = { return size qs;}
  proc msgs() :(msg_s * (r_t*msg_l)) list = { return msgs;} 
}.

(*-- Adversary that finds a collision in a QROm 
  -- this one actually replaces O_l2s(Overwrite(RO_m,RO_l)) by O_l2s(RO_l) which is equivalent  --*)
module (CollisionFinder(S : SS1.SI.Scheme_RO, A : SS2.LI.Adv_EFCMA_RO,
                 RO_l : SS2.RO.QRO_i) :  Coll.AdvCol) (RO_m : QROm.QRO) = {
  module R = OverwriteByQROmsg(RO_m, RO_l)
  module S1 = S(O_l2s(RO_l))
  module O = O_CMA_Coll_Simplified(S, R, O_l2s(RO_l))

  var coll: bool
       
  proc main() = {
    
    var pk : pk_l;
    var sk : sk_l;
    var m : msg_l;
    var m_s : msg_s;
    var sig : sig_l;
    var nrqs : int;
    var is_valid, is_fresh : bool;
    var msgs;
    var x1, x2;
    
    RO_l.init();
    
    (pk, sk) <@ S1.keygen();
      
    O.init(sk);
    (m, sig) <@ CountingA(A,R,O).forge(pk);
    x1 <- (sig.`1,m);
    
    m_s <@ ROmsg(R).h{(sig.`1,m)};
    is_valid <@ S1.verify(pk, m_s, sig.`2);
    is_fresh <@ O.fresh(m);
    nrqs <@ O.nr_queries();
    
    msgs <@ O.msgs();    
    coll <- (assoc msgs m_s <> None);
    x2 <- oget (assoc msgs m_s);     
    return (x1, x2);
    
  }
}.


(* --- **********************************************************************
        signature forgery branch
       ********************************************************************** *)


(*---------------------------- Game1 -----------------------------------------------------*)
  (*-- Game1 Helper Module that uses Overwrite Oracle --*)
module Game1(S : SS1.SI.Scheme_RO, A : SS2.LI.Adv_EFCMA_RO,
                 RO_l : SS2.RO.QRO_i, RO_s: SS1.RO.QRO_i) = {
  module S1 = S(O_l2s(OverwriteByQRO_s(RO_s, RO_l)))
  module O = O_CMA_Coll(S, OverwriteByQRO_s(RO_s, RO_l))
  
  
  var coll: bool
     
  proc main(): bool = {
    
    var pk : pk_l;
    var sk : sk_l;
    var m : msg_l;
    var m_s : msg_s;
    var sig : sig_l;
    var nrqs : int;
    var is_valid, is_fresh : bool;
    var msgs;

    RO_l.init();
    RO_s.init(); 

    
    (pk, sk) <@ S1.keygen();
      
    O.init(sk);
    (m, sig) <@ A(OverwriteByQRO_s(RO_s, RO_l),O).forge(pk);

    m_s <@ ROmsg(OverwriteByQRO_s(RO_s, RO_l)).h{(sig.`1,m)};
    is_valid <@ S1.verify(pk, m_s, sig.`2);
    is_fresh <@ O.fresh(m);
    nrqs <@ O.nr_queries();
    
    msgs <@ O.msgs();
    coll <- (assoc msgs m_s <> None);      
    return nrqs <= qS /\ is_valid /\ is_fresh;
    
  }
}. 
                 
                 
(* -- Reduction module that distinguishes the Overwrite 
      with probability |PR[Game2] - Pr[Game1]|      --*)
module (R_Dist_s (S : SS1.SI.Scheme_RO, A : SS2.LI.Adv_EFCMA_RO) : RO_Distinguisher) (G: QRO_l_t) = {
  module S1 = S(O_l2s(G))
  module O = O_CMA_Coll(S,G)
  
  
  var coll: bool
     
  proc distinguish(): bool = {
    
    var pk : pk_l;
    var sk : sk_l;
    var m : msg_l;
    var m_s : msg_s;
    var sig : sig_l;
    var nrqs : int;
    var is_valid, is_fresh : bool;
    var msgs;

    
    (pk, sk) <@ S1.keygen();
      
    O.init(sk);
    (m, sig) <@ A(G,O).forge(pk);

    m_s <@ ROmsg(G).h{(sig.`1,m)};
    is_valid <@ S1.verify(pk, m_s, sig.`2);
    is_fresh <@ O.fresh(m);
    nrqs <@ O.nr_queries();
    
    msgs <@ O.msgs();
    coll <- (assoc msgs m_s <> None);      
    return nrqs <= qS /\ is_valid /\ is_fresh /\ !coll;
    
  }
}.

  (*-- Game1Prime Helper Module that is identical to Game2 but replaces O_l2s(Overwrite(S,L)) by S --*)
module Game1Prime(S : SS1.SI.Scheme_RO, A : SS2.LI.Adv_EFCMA_RO,
                 RO_l : SS2.RO.QRO_i, RO_s: SS1.RO.QRO_i) = {
  module S1 = S(RO_s)
  module O = O_CMA_Coll_Simplified(S, RO_l, RO_s)
  
  
  var coll: bool
     
  proc main(): bool = {
    
    var pk : pk_l;
    var sk : sk_l;
    var m : msg_l;
    var m_s : msg_s;
    var sig : sig_l;
    var nrqs : int;
    var is_valid, is_fresh : bool;
    var msgs;

    RO_l.init();
    RO_s.init();    
    
    (pk, sk) <@ S1.keygen();
      
    O.init(sk);
    (m, sig) <@ A(OverwriteByQRO_s(RO_s, RO_l),O).forge(pk);

    m_s <@ ROmsg(RO_l).h{(sig.`1,m)};
    is_valid <@ S1.verify(pk, m_s, sig.`2);
    is_fresh <@ O.fresh(m);
    nrqs <@ O.nr_queries();
    
    msgs <@ O.msgs();
    coll <- (assoc msgs m_s <> None);      
    return nrqs <= qS /\ is_valid /\ is_fresh;
    
  }
}.       
       
       
       

(*---------------------------- Game2 -----------------------------------------------------*)
(*-- Helper Module that uses Reprogrammable Oracle --*)
module Game2(S : SS1.SI.Scheme_RO, A : SS2.LI.Adv_EFCMA_RO,
                 RO_l : SS2.RO.QRO_i, RO_s: SS1.RO.QRO_i) = {
  module S1 = S(RO_s)
  module O = O_CMA_Coll_Simplified(S, R_QRO.Wrapped_QRO(RO_l), RO_s)
  
  
  var coll: bool
     
  proc main(): bool = {
    
    var pk : pk_l;
    var sk : sk_l;
    var m : msg_l;
    var m_s : msg_s;
    var sig : sig_l;
    var nrqs : int;
    var is_valid, is_fresh : bool;
    var msgs;
      
    RO_l.init();
    RO_s.init();
    R_QRO.Wrapped_QRO(RO_l).init();

    
    (pk, sk) <@ S1.keygen();
      
    O.init(sk);
    (m, sig) <@ A(OverwriteByQRO_s(RO_s,R_QRO.Wrapped_QRO(RO_l)),O).forge(pk);

    m_s <@ ROmsg(R_QRO.Wrapped_QRO(RO_l)).h{(sig.`1,m)};
    is_valid <@ S1.verify(pk, m_s, sig.`2);
    is_fresh <@ O.fresh(m);
    nrqs <@ O.nr_queries();
    
    msgs <@ O.msgs();
    coll <- (assoc msgs m_s <> None);      
    return nrqs <= qS /\ is_valid /\ is_fresh;
    
  }
}.



(*---------------------------- Game3 -----------------------------------------------------*)
(*************************************************** CONTINUE HERE ***********************************************************)
(* 
  Signing Oracle that reprograms 
*)
module (O_CMA_Game3 (S1: SS1.SI.Scheme_RO, O: R_QRO.QRO_r, O_s : SS1.RO.QRO): SS2.KeyUpdating.SOracle_CMA) = {
  var sk : sk_l
  var qs : msg_l list
  var msgs: ( msg_s * (r_t*msg_l)) list
  
  (* Initialize *)
  proc init (sk_init : sk_l) : unit = {
    sk <- sk_init;
    qs <- [];
    msgs <- [];
  }

  (* 
    Sign given message m using the list of message-signature pairs
    given at init time.
  *)
  proc sign(m : msg_l) : sig_l = {
    var r : r_t;
    var sig : sig_l;
    var msg_tmp;
    var sig_s;
    
    r <$ dr_t;
    msg_tmp <$ SS2.RO.dhash;
    O.set((false, witness,r,m), (msg_tmp));
    O.h{(false, witness,r,m)};
    (sig_s, sk) <@ S1(O_s).sign(sk, msg_tmp.`2);
    sig <- (r, sig_s);

    qs <- rcons qs m;
    msgs <- rcons msgs (msg_tmp.`2,(r,m));
            
    return sig;
  }

  proc fresh(m : msg_l) : bool = { return ! m \in qs; }
  proc nr_queries() : int = { return size qs;}
  proc msgs() :(msg_s * (r_t*msg_l)) list = { return msgs;} 
}.

  (*-- Game3 Helper Module  --*)
module Game3(S : SS1.SI.Scheme_RO, A : SS2.LI.Adv_EFCMA_RO,
                 RO_l : SS2.RO.QRO_i, RO_s: SS1.RO.QRO_i) = {
  module S1 = S(RO_s)
  module O = O_CMA_Game3(S, R_QRO.Wrapped_QRO(RO_l), RO_s)
  
  
  var coll: bool
     
  proc main(): bool = {
    
    var pk : pk_l;
    var sk : sk_l;
    var m : msg_l;
    var m_s : msg_s;
    var sig : sig_l;
    var nrqs : int;
    var is_valid, is_fresh : bool;
    var msgs;
    
    RO_l.init();
    RO_s.init();    
    R_QRO.Wrapped_QRO(RO_l).init();  
    
    (pk, sk) <@ S1.keygen();
      
    O.init(sk);
    
    (m, sig) <@ A(OverwriteByQRO_s(RO_s, R_QRO.Wrapped_QRO(RO_l)),O).forge(pk);

    m_s <@ ROmsg(R_QRO.Wrapped_QRO(RO_l)).h{(sig.`1,m)};
    is_valid <@ S1.verify(pk, m_s, sig.`2);
    is_fresh <@ O.fresh(m);
    nrqs <@ O.nr_queries();
    
    msgs <@ O.msgs();
    coll <- (assoc msgs m_s <> None);      
    return nrqs <= qS /\ is_valid /\ is_fresh;
    
  }
}.  



(*-- Oracle for the reduction that distinguishes reprogramming --*)
module (O_CMA_Game3_red (S1 : SS1.SI.Scheme_RO, RO: R_QRO.QROM.QRO, O: R_QRO.RepO_t, RO_s: SS1.RO.QRO_i): SS2.KeyUpdating.SOracle_CMA) = {
  var sk : sk_l
  var qs : msg_l list
  var msgs: ( msg_s * (r_t*msg_l)) list

  
  (* Initialize *)
  proc init (sk_init : sk_l) : unit = {
    sk <- sk_init;
    qs <- [];
    msgs <- [];
  }

  (* 
    Sign given message m using the list of message-signature pairs
    given at init time.
  *)
  proc sign(m : msg_l) : sig_l = {
    var sig : sig_l;
    var sig_s;
    var xs;
    var msg_s; 
    var sample_dist;
    
    (*sample_dist <- (dmap dr_t (fun r => (false, witness, r, m))) `*` dunit tt;*)
    sample_dist <-  (dmap dr_t (fun r  => ((false, witness<:SS1.RO.from>, r, m), tt)));
    xs <@ O.repro(sample_dist);
    msg_s <@ RO.h{(xs.`1)};
    (sig_s, sk) <@ S1(RO_s).sign(sk, msg_s.`2);
    sig <- (xs.`1.`3, sig_s);

    qs <- rcons qs m;
    msgs <- rcons msgs (msg_s.`2,(xs.`1.`3,m));
            
    return sig;
  }

  proc fresh(m : msg_l) : bool = { return ! m \in qs; }
  proc nr_queries() : int = { return size qs;}
  proc msgs() :(msg_s * (r_t*msg_l)) list = { return msgs;} 
}.

(*-- Reduction that distinguishes Reprogramming --*)
module (R_D_Repro (S : SS1.SI.Scheme_RO, A : SS2.LI.Adv_EFCMA_RO, RO_s: SS1.RO.QRO_i) : R_QRO.DistA) (RO: R_QRO.QROM.QRO, RO_r: R_QRO.RepO_t) = {
  module S1 = S(RO_s)
  module O = O_CMA_Game3_red(S, RO, RO_r, RO_s)
  
  var coll: bool
     
  proc distinguish(): bool = {
    
    var pk : pk_l;
    var sk : sk_l;
    var m : msg_l;
    var m_s : msg_s;
    var sig : sig_l;
    var nrqs : int;
    var is_valid, is_fresh : bool;
    var msgs;
    
    RO_s.init();
    (pk, sk) <@ S1.keygen();
      
    O.init(sk);
    (m, sig) <@ CountingA(A,OverwriteByQRO_s(RO_s, RO),O).forge(pk);

    m_s <@ ROmsg(RO).h{(sig.`1,m)};
    is_valid <@ S1.verify(pk, m_s, sig.`2);
    is_fresh <@ O.fresh(m);
    nrqs <@ O.nr_queries();
    
    msgs <@ O.msgs();
    coll <- (assoc msgs m_s <> None);      
    return nrqs <= qS /\ is_valid /\ is_fresh /\ !coll;
    
  }
}.


(*---------------------------- Game4 ----------------------------------------------------- *)
 
 module Game4(S1 : SS1.SI.Scheme_RO, A : SS2.LI.Adv_EFCMA_RO,
                 RO_l : SS2.RO.QRO_i, RO_s: SS1.RO.QRO_i) = {   
     
    module SO = SS1.KeyUpdating.O_RMA_Default(S1(RO_s))
    module O = O_CMA_Repro(R_QRO.Wrapped_QRO(RO_l), SO)
        
     var coll: bool
      
    proc main() : bool = {
      var pk;
      var sk;
      var m';
      var m_s;
      var sig';
      var is_valid, is_fresh : bool;
      var nr;
      var msgs;
     
      
      coll <- false;

      RO_l.init();
      RO_s.init();    
      R_QRO.Wrapped_QRO(RO_l).init();
      
      (pk, sk) <@ S1(RO_s).keygen();
      SO.init(sk);  
      O.init();
      
      (m', sig') <@ A(OverwriteByQRO_s(RO_s,R_QRO.Wrapped_QRO(RO_l)),O).forge(pk);
      
      m_s <@ ROmsg(R_QRO.Wrapped_QRO(RO_l)).h{sig'.`1,m'};
      is_valid <@ S1(RO_s).verify(pk, m_s, sig'.`2);      
      is_fresh <@ O.fresh(m');
      nr <@ O.nr_queries();
      msgs <@ O.msgs();
      coll <- (assoc msgs m_s <> None);
      
      return nr <= qS /\ is_valid /\ is_fresh;
    }
  }.




section MAIN_PROOF.
(* For all adversaries A ... *)
declare module A <: SS2.LI.Adv_EFCMA_RO {-QRO_s, -QRO_l, -QROmsg, -OverwriteByQRO_s, -R_QRO.Wrapped_QRO, -SS2.KeyUpdating.O_CMA_Default, -O_CMA_Repro, -O_CMA_Game3_red, -R_QRO.RepO, -R_QRO.QROM.QRO, -O_CMA_Game3, -SS1.KeyUpdating.O_RMA_Default, -Game4, -Reduction, -O_CMA_Coll, -CountingA, -O_CMA_Coll_Simplified}.
declare module S1 <: SS1.SI.Scheme_RO {-A, -QRO_s, -QRO_l, -QROmsg, -QROm.QRO, -OverwriteByQRO_s, -R_QRO.Wrapped_QRO, -SS2.KeyUpdating.O_CMA_Default, -O_CMA_Repro, -O_CMA_Game3_red, -R_QRO.QROM.QRO, -R_QRO.RepO, -O_CMA_Game3, -SS1.KeyUpdating.BaseOracle, -SS1.KeyUpdating.O_RMA_Default, -Game4, -Reduction, -O_CMA_Coll, -CountingA, -O_CMA_Coll_Simplified}.

(* ... where A makes at most qS queries to its signing oracle and qH queries to its hash oracle ... *)
declare axiom forge_q (O <: SS2.KeyUpdating.SOracle_CMA { -A, -CountingA })
                      (H <: SS2.RO.QRO {-A, -CountingA}):
  hoare [A(CountingA(A,H,O).Ho,CountingA(A,H,O).S).forge:
              CountingA.cS = 0
           /\ CountingA.cH = 0
         ==>  CountingA.cS <= qS
           /\ CountingA.cH <= qH].

                   
           
(* Helper result to prove first game hop, may prove too much *)
equiv hopXcount:
  SS2.LI.EF_CMA_RO(HS(S1), A, QRO_l, SS2.KeyUpdating.O_CMA_Default).main ~ GameX(S1, A, QRO_l).main:
  ={glob S1, glob A, glob SS2.RO.QRO} ==>  ={SS2.RO.QRO.ch, res} /\ ={qs}(SS2.KeyUpdating.O_CMA_Default, O_CMA_Coll).
proof. 
proc. inline *. auto.  call ( : ={glob SS2.RO.QRO}).
+ by sim.
auto. call ( : ={glob SS2.RO.QRO, glob S1}
            /\ ={sk, qs}(SS2.KeyUpdating.O_CMA_Default, O_CMA_Coll)). 
+ proc; inline *; auto.
  call ( : ={glob SS2.RO.QRO}).
  + by sim. 
  by auto.
+ by sim. 
wp; call ( : ={glob SS2.RO.QRO}).
+ by sim.
by auto.
qed.

(* moving to a signing oracle and game 
   that can make the case-split between 
   collision for H and forgery for S *) 
   
lemma hopX &m:
  Pr [SS2.LI.EF_CMA_RO(HS(S1), A, QRO_l, SS2.KeyUpdating.O_CMA_Default).main() @ &m : res] 
  = Pr [GameX(S1, A, QRO_l).main() @ &m : res].
proof. 
by byequiv hopXcount.
qed.

(* Collision case hop 1: Introduce overwrite oracle for Hmsg *)
lemma hopC1 &m:
  Pr [GameX(S1, A, QRO_l).main() @ &m : res /\ GameX.coll]
  = Pr [GameC1(S1, A, QRO_l, QROmsg).main() @ &m : res /\ GameC1.coll].
proof. 
have -> // :  `|Pr [GameX(S1, A, QRO_l).main() @ &m : res /\ GameX.coll] 
   - Pr [GameC1(S1, A, QRO_l, QROmsg).main() @ &m : res /\ GameC1.coll]| = 0%r 
  => 
  Pr [GameX(S1, A, QRO_l).main() @ &m : res /\ GameX.coll] 
  = Pr [GameC1(S1, A, QRO_l, QROmsg).main() @ &m : res /\ GameC1.coll].
+ by smt().
(*-- left sides are equal --*)
have -> : Pr [GameX(S1, A, QRO_l).main() @ &m : res /\ GameX.coll]
  = Pr [DistGameOverwriteM(R_Dist_m(S1,A)).left() @ &m : res].
+ byequiv => //; proc; inline{2} 2; inline *; wp. 
  call(_ : ={SS2.RO.QRO.h}); first by sim.
  wp; call(_: ={glob S1, SS2.RO.QRO.h, glob O_CMA_Coll}); first 2 by sim.
  wp; call(_: ={SS2.RO.QRO.h}); first by sim.        
  by auto => />.

(*-- right sides are equal --*)
have -> // : Pr [GameC1(S1, A, QRO_l, QROmsg).main() @ &m : res  /\ GameC1.coll]
    = Pr [DistGameOverwriteM(R_Dist_m(S1,A)).right() @ &m : res].
+ byequiv => //; proc; inline *; wp. swap {2} [3..4] -2. 
  call(_ : ={SS2.RO.QRO.h, QROm.QRO.h}); first by sim.
  wp; call(_: ={glob S1, SS2.RO.QRO.h, QROm.QRO.h, glob O_CMA_Coll}); first 2 by sim.
  wp; call(_: ={SS2.RO.QRO.h, QROm.QRO.h}); first by sim.        
  by auto => />.
by rewrite (pr_RO_comb_m (R_Dist_m(S1,A))).
qed.  

(*
equiv equalOs: 
  O_l2s(QRO_l).h ~ O_l2s(OverwriteByQROmsg(QROmsg, QRO_l)).h: 
    ={glob QRO_l, m} ==> ={res, glob QRO_l}.
proof.
  by proc; inline*; auto.
qed.
*)

(*-- Breaking Coll --*)
lemma hopC2 &m:
  Pr [GameC1(S1, A, QRO_l, QROmsg).main() @ &m : res /\ GameC1.coll]
  <= Pr[Coll.Col(CollisionFinderPrime(S1, A, QRO_l)).main() @ &m : res].
proof. 
byequiv => //.
proc; inline *; auto.     
call (_: ={SS2.RO.QRO.h, QROm.QRO.h}); first by sim.
wp; call (_: ={glob S1, SS2.RO.QRO.h, QROm.QRO.h, glob O_CMA_Coll} 
             /\ (forall y r x, (y, (r,x)) \in O_CMA_Coll.msgs{1} 
                         => x \in O_CMA_Coll.qs{1}) 
             /\ (forall y r x, (y, (r,x)) \in O_CMA_Coll.msgs{1} 
                         => y = QROm.QRO.h{1} (r,x))). 
+ proc; inline *; auto. 
  call (_: ={SS2.RO.QRO.h, QROm.QRO.h}); first by sim.
  by auto => />; smt(mem_rcons).
+ by proc; inline *; auto.      
wp; call(_: ={SS2.RO.QRO.h, QROm.QRO.h}); first by sim.        
auto => />.
by smt (assocP assoc_none).
qed.

equiv hopC2prime:
  Coll.Col(CollisionFinderPrime(S1, A, QRO_l)).main ~ Coll.Col(CollisionFinder(S1, A, QRO_l)).main: 
  ={glob S1, glob A} ==> ={res}.
proof. 
proc; inline*; auto. 
call (_: ={SS2.RO.QRO.h, QROm.QRO.h}). 
+ by proc; inline*; auto.
wp. call (_: ={glob S1, SS2.RO.QRO.h, QROm.QRO.h} 
               /\ O_CMA_Coll.sk{1} = O_CMA_Coll_Simplified.sk{2}
               /\ O_CMA_Coll.msgs{1} = O_CMA_Coll_Simplified.msgs{2}
               /\ O_CMA_Coll.qs{1} = O_CMA_Coll_Simplified.qs{2}).
+ proc; inline*; auto.
  call(_: ={SS2.RO.QRO.h, QROm.QRO.h} 
            /\ O_CMA_Coll.sk{1} = O_CMA_Coll_Simplified.sk{2}
            /\ O_CMA_Coll.msgs{1} = O_CMA_Coll_Simplified.msgs{2}
            /\ O_CMA_Coll.qs{1} = O_CMA_Coll_Simplified.qs{2}
            ).
  + by proc; inline*; auto.
  + by auto => />.
  + by proc; inline*; auto => />.
auto => />. 
call(_: ={SS2.RO.QRO.h, QROm.QRO.h}).
+ by proc; inline*; auto.
by auto => />.
qed.

lemma hopC2pProb &m:
   Pr[Coll.Col(CollisionFinderPrime(S1, A, QRO_l)).main() @ &m : res]
   = Pr[Coll.Col(CollisionFinder(S1, A, QRO_l)).main() @ &m : res].
proof.
by byequiv hopC2prime.
qed.

(* Proving that Collision finder makes at most qH + qS + 1 queries to its RO *)
local hoare col_queries: 
  Coll.Col(CollisionFinder(S1, A, QRO_l)).main : 
  QROm.QRO.ch =0  ==> (QROm.QRO.ch <=  qH + qS + 1).
proof.
  proc; inline*; auto.  
  call (_: QROm.QRO.ch <= qH + qS + 1 ==>  QROm.QRO.ch <= qH + qS + 1). 
  proc (QROm.QRO.ch <= qH + qS + 1); first 2 by auto.
  + proc; inline*; auto. 
  wp.
  call (_: CountingA.cH + CountingA.cS = QROm.QRO.ch
          /\ CountingA.cH = 0 /\ CountingA.cS = 0
          ==>
          CountingA.cH + CountingA.cS = QROm.QRO.ch
          /\ CountingA.cH <= qH /\ CountingA.cS <= qS ).
    conseq(_ :  CountingA.cS = 0 /\ CountingA.cH = 0 ==>
            CountingA.cS <= qS /\ CountingA.cH <= qH)
            (_ : CountingA.cH + CountingA.cS = QROm.QRO.ch
             ==> CountingA.cH + CountingA.cS = QROm.QRO.ch); first 2 by smt().
    + proc(CountingA.cH + CountingA.cS = QROm.QRO.ch) => />. 
    + proc; inline*; auto. 
      call(_ : true). 
    + by proc; inline*; auto.
    by auto => />; smt().
  + by proc; inline*; auto => /#.
    apply (forge_q 
            (O_CMA_Coll_Simplified(S1, OverwriteByQROmsg(QROm.QRO, SS2.RO.QRO), O_l2s(SS2.RO.QRO)))
            (OverwriteByQROmsg(QROm.QRO, SS2.RO.QRO))
           ).  
  wp => /=.
  call (_: true).
  + by proc; inline*; auto.
auto => /> * /#. 
qed.   


(* -- ******************************************************************************************************  
                                     Reduction from EF-RMA of S1 (S1-forgery case)
  
      ******************************************************************************************************)  
  
(*-- bound hop using that overwrite is perfectly ind --*)        
lemma hop1 &m: 
  Pr [GameX(S1, A, QRO_l).main() @ &m : res /\ !GameX.coll]
  = Pr [Game1(S1, A, QRO_l, QRO_s).main() @ &m : res /\ ! Game1.coll].
proof. 
have -> // :  `| Pr [GameX(S1, A, QRO_l).main() @ &m : res /\ !GameX.coll]
  - Pr [Game1(S1, A, QRO_l, QRO_s).main() @ &m : res /\ ! Game1.coll]| = 0%r 
  => 
   Pr [GameX(S1, A, QRO_l).main() @ &m : res /\ !GameX.coll]
  = Pr [Game1(S1, A, QRO_l, QRO_s).main() @ &m : res /\ ! Game1.coll].
+ by smt().
(*-- left sides are equal --*)
have -> : Pr [GameX(S1, A, QRO_l).main() @ &m : res /\ !GameX.coll]
  = Pr [DistGameOverwriteS(R_Dist_s(S1,A)).left() @ &m : res].
+ byequiv => //; proc; inline *; wp. 
  call ( _ : ={SS2.RO.QRO.h}); first by sim.
  auto; call ( _ : ={SS2.RO.QRO.h, glob O_CMA_Coll, glob S1}).
  + proc; wp; call ( _ : ={SS2.RO.QRO.h}); first by sim.
  call ( _ : ={SS2.RO.QRO.h}); first by sim.
  by auto => />.      
+ by sim.
  auto => />.
  call ( _ : ={SS2.RO.QRO.h}); first by sim.
  by auto => />.  

(*-- right sides are equal --*)
have -> // : Pr [Game1(S1, A, QRO_l, QRO_s).main() @ &m : res /\ !Game1.coll]
    = Pr [DistGameOverwriteS(R_Dist_s(S1,A)).right() @ &m : res].
+ byequiv => //; proc; inline *; wp. 
  call ( _ : ={SS1.RO.QRO.h, SS2.RO.QRO.h}); first by sim.
  auto; call ( _ : ={SS1.RO.QRO.h, SS2.RO.QRO.h, glob O_CMA_Coll, glob S1}); first 2 by sim.
  by auto => />; sim.
by rewrite (pr_RO_comb_s (R_Dist_s(S1,A))).
qed.  
 
lemma hop1prime &m: 
  Pr [Game1(S1, A, QRO_l, QRO_s).main() @ &m : res /\ ! Game1.coll]
  = Pr [Game1Prime(S1, A, QRO_l, QRO_s).main() @ &m : res /\ ! Game1Prime.coll].
proof. 
byequiv => //. 
proc; inline*; auto.  
call(_ : ={SS1.RO.QRO.h, SS2.RO.QRO.h}). 
+ by proc; inline*; auto.
auto => //.
call(_ : ={SS1.RO.QRO.h, SS2.RO.QRO.h, glob S1} 
         /\ ={sk, qs, msgs}(O_CMA_Coll, O_CMA_Coll_Simplified)).
+ proc; inline*; auto.
  call(_ : ={SS1.RO.QRO.h, SS2.RO.QRO.h} 
         /\ ={sk, qs, msgs}(O_CMA_Coll, O_CMA_Coll_Simplified)).
  + by proc; inline*; auto.  
  by auto.
+ by sim.
auto => />.
call(_ : ={SS1.RO.QRO.h, SS2.RO.QRO.h}).
+ by proc; inline*; auto.
by auto.
qed.
  
  (*-- switch to reprogrammable oracle --*)
lemma hop2 &m: 
  Pr [Game1Prime(S1, A, QRO_l, QRO_s).main() @ &m : res /\ ! Game1Prime.coll]
  = Pr [Game2(S1, A, QRO_l, QRO_s).main() @ &m : res /\ !Game2.coll].
proof. 
byequiv => //.
proc; inline*; wp; call ( : ={SS2.RO.QRO.h, SS1.RO.QRO.h} /\R_QRO.Wrapped_QRO.prog_list{2} = []). 
+ by proc; inline*; auto. 
wp; call ( : ={glob S1, SS2.RO.QRO.h, SS1.RO.QRO.h, glob O_CMA_Coll_Simplified} /\R_QRO.Wrapped_QRO.prog_list{2} = []). 
+ proc; inline *; auto; call ( : ={SS2.RO.QRO.h, SS1.RO.QRO.h} /\R_QRO.Wrapped_QRO.prog_list{2} = []). 
  + by proc; inline*; auto.
+ by auto => />. 
+ by proc; inline*; auto. 
wp; call ( : ={SS2.RO.QRO.h, SS1.RO.QRO.h} /\R_QRO.Wrapped_QRO.prog_list{2} = []).     
+  by proc; inline*; auto. 
by auto => />.
qed.    


  (*-- switch to reprogramming sign oracle --*)
lemma hop3 &m: 
  `|Pr [Game2(S1, A, QRO_l, QRO_s).main() @ &m : res /\ !Game2.coll] -
  Pr [Game3(S1, A, QRO_l, QRO_s).main() @ &m : res /\ !Game3.coll]|
  =
 `|Pr[R_QRO.ReproGame(QROrep,R_D_Repro(S1,A, QRO_s)).main(false) @ &m:res]
 - Pr[R_QRO.ReproGame(QROrep,R_D_Repro(S1,A, QRO_s)).main(true) @ &m:res]|.
proof. 
congr.
congr.
(* -------- left side ---------*)
+ byequiv => //.  
  (*verify call*)
  proc; inline *; wp. 
  call( _ :  ={glob SS1.RO.QRO, glob SS2.RO.QRO}
             /\ (glob O_CMA_Coll_Simplified){1} = (glob O_CMA_Game3_red){2}
               ).  
  + by sim. 
  wp => />. 
  + by auto => /#.
  (* A forge call *)
  call( _ : ={glob S1, glob SS1.RO.QRO, glob SS2.RO.QRO, glob R_QRO.Wrapped_QRO} 
               /\ R_QRO.RepO.b{2} = false  
               /\ (glob O_CMA_Coll_Simplified){1} = (glob O_CMA_Game3_red){2}
               /\ R_QRO.Wrapped_QRO.prog_list{2} = []). 
    + proc; wp; inline{1} HS(S1, R_QRO.Wrapped_QRO(SS2.RO.QRO)).sign.
      inline{2} 2. 
     (*sign call*) 
      wp => /=.
      call(_ : ={glob SS1.RO.QRO} 
                      /\ (O_CMA_Coll_Simplified.sk){1} = (O_CMA_Game3_red.sk){2}).
      + by sim.
      inline{1} ROmsg(R_QRO.Wrapped_QRO(SS2.RO.QRO)).h; auto. 
      call(_ : ={glob SS2.RO.QRO, glob R_QRO.Wrapped_QRO} 
               /\R_QRO.Wrapped_QRO.prog_list{2} = []
               /\ (glob O_CMA_Coll_Simplified){1} = (glob O_CMA_Game3_red){2}
               ). 
      + sim />.         
      inline R_QRO.RepO(R_QRO.Wrapped_QRO(R_QRO.QROM.QRO)).repro => //. 
      rcondf{2} 8; first by auto.    
      wp. swap {2} -2. wp. sp. rnd (fun r => ((false, witness, r, m{1}), ())) (fun (x : (_*_*_*_)*_) => x.`1.`3).      
      auto => />. move => &2. split. 
      + by move => x /supp_dmap /= /> r ? ? /supp_dunit ? /#. 
      move => _. split. 
      + move => [x1 x2]  /supp_dmap /= /> ? ?. rewrite dmap1E => /= //.
      move => h1 rL x // />. 
      by rewrite supp_dmap /=; exists rL.    
    proc. auto => />. inline{2} 2. wp. inline*. auto.
  auto => //. 
  call( _ : ={glob SS1.RO.QRO, glob SS2.RO.QRO, glob R_QRO.Wrapped_QRO} /\ SS2.RO.QRO.h{1} = R_QRO.QROM.QRO.h{2}  /\ R_QRO.Wrapped_QRO.prog_list{2} = []).       
  + by proc; auto.
  by auto => />.
  
(* -------- right side ---------*)
have <- : Pr[Game3(S1, A, QRO_l, QRO_s).main() @ &m : res /\ !Game3.coll] =
 Pr[R_QRO.ReproGame(QROrep, R_D_Repro(S1, A, QRO_s)).main(true) @ &m : res]; last by smt().
byequiv => //.  
(*verify call*)
proc; inline *; wp. 
call( _ :  ={glob SS1.RO.QRO, glob SS2.RO.QRO, glob R_QRO.Wrapped_QRO}).
+ by sim.  
wp => /=. swap{2} [9..10] -4.
seq 6 6 : ( #pre /\ ={glob S1, glob SS1.RO.QRO, glob SS2.RO.QRO, glob R_QRO.Wrapped_QRO}).
+ by auto => />.
wp => />. 
+ by auto => /#.  
(* A forge call *)
call( _ : ={glob S1, glob SS1.RO.QRO, glob SS2.RO.QRO, glob R_QRO.Wrapped_QRO}
         /\ (glob O_CMA_Game3){1} = (glob O_CMA_Game3_red){2} 
         /\ R_QRO.RepO.b{2} = true). 
  + proc; inline{1} HS(S1, R_QRO.Wrapped_QRO(SS2.RO.QRO)).sign; inline{2} 2; wp.
    move => /=. 
    (*sign call*)
    call(_ : ={glob R_QRO.Wrapped_QRO, glob SS1.RO.QRO, glob SS2.RO.QRO}
         /\ (glob O_CMA_Game3){1} = (glob O_CMA_Game3_red){2}). 
    + by sim.
    wp => />. 
    inline*. wp.
    rcondt{2} 8; first by auto => //.
    wp.
    rnd. swap {2} -2. wp.
    rnd  (fun r => ((false, witness, r, m{2}), ())) (fun (x : (_*_*_*_)*_) => x.`1.`3).
    auto => />. move => &2. split. 
    + by move => x  /supp_dmap /= /> r ? ? ? /#. 
    move => ?. split. 
    + by move => [x1 x2]  /supp_dmap /= /> ? ?; rewrite dmap1E. 
    move => h1 rL x.   
    by rewrite supp_dmap /=; exists rL.
  proc; auto => />. inline{2} 2; wp. 
  call( _ : ={glob SS2.RO.QRO, glob R_QRO.Wrapped_QRO}) => //. 
  by sim.  
by auto => //; sp; inline *; auto => />. 
wp.
call( _ : ={glob SS1.RO.QRO, glob SS2.RO.QRO, glob R_QRO.Wrapped_QRO}). 
+ by sim.
by auto => />.   
qed.  



local hoare repro_queries: 
  R_QRO.ReproGame(QROrep, R_D_Repro(S1, A, QRO_s)).main :
  R_QRO.Wrapped_QRO.ch = 0 /\ R_QRO.RepO.ctr = 0 /\ R_QRO.RepO.se ==> 
    R_QRO.Wrapped_QRO.ch <= qS + qH + 1 /\ R_QRO.RepO.ctr <= qS /\ R_QRO.RepO.se.
proof.
  proc; inline*; auto.  
  call (_:  R_QRO.RepO.ctr <= qS 
         /\ R_QRO.Wrapped_QRO.ch <= qS + qH + 1). 
  + by proc; inline *; auto.
  wp.
  call (_: R_QRO.RepO.ctr = CountingA.cS
        /\ R_QRO.Wrapped_QRO.ch = CountingA.cH + CountingA.cS
        /\ CountingA.cH = 0 /\ CountingA.cS = 0
        /\ R_QRO.RepO.se
          ==>
          R_QRO.RepO.ctr = CountingA.cS
        /\ R_QRO.Wrapped_QRO.ch = CountingA.cH + CountingA.cS
        /\ CountingA.cH <= qH /\ CountingA.cS <= qS 
        /\ R_QRO.RepO.se).
  + conseq(_ :  CountingA.cS = 0 /\ CountingA.cH = 0 ==>
            CountingA.cS <= qS /\ CountingA.cH <= qH)
            (_ : R_QRO.RepO.ctr = CountingA.cS
              /\ R_QRO.Wrapped_QRO.ch = CountingA.cH + CountingA.cS
              /\ R_QRO.RepO.se); first 2 by smt().
    + proc(R_QRO.RepO.ctr = CountingA.cS
        /\ R_QRO.Wrapped_QRO.ch = CountingA.cH + CountingA.cS
        /\ R_QRO.RepO.se) => />. 
      + proc; wp; inline *; auto. 
      call(_ : true); auto.
      case R_QRO.RepO.b.
      + rcondt 8; 1: by auto => />. 
        auto => />; rewrite /sample_dist => // /> &hr *; split; 1: by smt(). 
        by rewrite p_max_val. 
      rcondf 8; 1: by auto => />. 
      auto => />; rewrite /sample_dist => // /> &hr *; split; 1: by smt(). 
      by rewrite p_max_val.
    by proc; inline*; auto => /#.
  + by apply (forge_q 
            (O_CMA_Game3_red(S1, R_QRO.Wrapped_QRO(SS2.RO.QRO), R_QRO.RepO(R_QRO.Wrapped_QRO(SS2.RO.QRO)), SS1.RO.QRO))
            (OverwriteByQRO_s(SS1.RO.QRO, R_QRO.Wrapped_QRO(SS2.RO.QRO)))
           ).  
  wp; call (_: true); auto => /> /#.
qed.   

(*-- switching to simulating sign with message signature pair list --*)        
lemma hop4 &m: 
  Pr [Game3(S1, A, QRO_l, QRO_s).main() @ &m : res /\ !Game3.coll] 
  = Pr [Game4(S1, A, QRO_l, QRO_s).main() @ &m : res /\ !Game4.coll].
proof. 
byequiv => //. proc. 
inline *. wp. call( _ : ={glob SS1.RO.QRO}); first by sim.
wp. 
call( _ : ={glob S1, glob SS2.RO.QRO, glob SS1.RO.QRO,
            glob R_QRO.Wrapped_QRO}
       /\ ={sk}(O_CMA_Game3,SS1.KeyUpdating.O_RMA_Default)
       /\ ={qs, msgs}(O_CMA_Game3, O_CMA_Repro)). 
  + proc. inline {2} SS1.KeyUpdating.O_RMA_Default(S1(SS1.RO.QRO)).sign. auto. inline *. 
    (* clearing the sampling *)
    seq 2 3 : (#pre /\ ={r} /\ msg_tmp{1} = (tmp{2},m0{2})).
    + rnd : *1 *1. auto => />. move => rL HrL. split.
      + move => tmp d_tmp; rewrite /SS2.RO.dhash /ro_dhash /dmsg_s; congr; rewrite /dmap /(\o) dprod_dlet => />.
        by rewrite  dlet_d_unit => />.
      move => tmp prod H // />; split.  
      + rewrite supp_dlet => />; exists prod.`1; rewrite SS1.RO.dhash_fu => />; rewrite supp_dmap. 
        by exists prod.`2; rewrite dmsg_s_fu =>  /> /#.
      by rewrite supp_dlet => />; move => a Ha; rewrite supp_dmap => />. 
    (* swapping the signing *)
    swap {1} 11 -10.    
    wp => />. 
    exlim r{1} => salt; exlim m{1} => msg; exlim msg_tmp{1} => mt.
    call ( _ : ={glob SS2.RO.QRO, glob SS1.RO.QRO,
            glob R_QRO.Wrapped_QRO}
       /\ ={sk}(O_CMA_Game3,SS1.KeyUpdating.O_RMA_Default)
       /\ ={qs, msgs}(O_CMA_Game3, O_CMA_Repro)). 
    + by sim.  
    by auto => /#.   
  by auto => />; sim.    
auto => />.  
call( _ : ={R_QRO.Wrapped_QRO.prog_list, glob SS1.RO.QRO, glob SS2.RO.QRO}); first by auto => />; sim. 
by auto => />. 
qed.

lemma no_coll_then_forge &m: 
 Pr [Game4(S1, A, QRO_l, QRO_s).main() @ &m : res /\ !Game4.coll]
  <= Pr [SS1.SI.I_EF_RMA_RO(S1, Reduction(QRO_l, A), SS1.KeyUpdating.O_RMA_Default, QRO_s).main() @ &m : res].
proof. 
byequiv ( : ={glob S1, glob A} ==> _ ) => //. 
proc. inline *. wp.

(* call verify *)
call(_ : ={glob SS1.RO.QRO} 
         /\ (forall x, x \in R_QRO.Wrapped_QRO.prog_list{1} => !x.`1.`1)). 
+ by proc; inline *; auto => />. 
wp. 
(* call adversary *)
call( _ : ={glob S1,SS2.RO.QRO.h, glob SS1.RO.QRO, glob O_CMA_Repro,
            glob SS1.KeyUpdating.O_RMA_Default, R_QRO.Wrapped_QRO.prog_list, SS1.KeyUpdating.BaseOracle.qs}
         /\ (forall x, x \in R_QRO.Wrapped_QRO.prog_list{2} => !x.`1.`1)
         /\ (forall x, exists r y, 
                  x \in O_CMA_Repro.qs{1} => (y, (r,x)) \in O_CMA_Repro.msgs{1} /\ y \in SS1.KeyUpdating.BaseOracle.qs{1})
         /\ (forall y, y \in SS1.KeyUpdating.BaseOracle.qs{1} => exists x r, 
                 (y, (r,x)) \in O_CMA_Repro.msgs{1} /\ x \in O_CMA_Repro.qs{1})
         /\ size SS1.KeyUpdating.BaseOracle.qs{1} = size O_CMA_Repro.qs{1}). 
+ proc. inline *. auto.
  call( _ : ={SS2.RO.QRO.h, glob SS1.RO.QRO, glob O_CMA_Repro,
            glob SS1.KeyUpdating.O_RMA_Default, R_QRO.Wrapped_QRO.prog_list, SS1.KeyUpdating.BaseOracle.qs}
          /\ (forall x, x \in R_QRO.Wrapped_QRO.prog_list{2} => !x.`1.`1)
          /\ (forall x, exists r y, 
                  x \in O_CMA_Repro.qs{1} => (y, (r,x)) \in O_CMA_Repro.msgs{1} /\ y \in SS1.KeyUpdating.BaseOracle.qs{1})
         /\ (forall y, y \in SS1.KeyUpdating.BaseOracle.qs{1} => exists x r, 
                 (y, (r,x)) \in O_CMA_Repro.msgs{1} /\ x \in O_CMA_Repro.qs{1})
          /\ size SS1.KeyUpdating.BaseOracle.qs{1} = size O_CMA_Repro.qs{1}). 
  + by proc; inline *; auto => // /> => &2 *. 
  auto => /> *. split. by smt(mem_rcons size_rcons). smt(mem_rcons size_rcons).
+ proc. inline*. auto => />. 
swap{2} [8..9] -7; swap{2} [10..11] -5. wp.
(* keygen *)
call(_ : ={glob SS1.RO.QRO} 
         /\ (forall x, x \in R_QRO.Wrapped_QRO.prog_list{1} => !x.`1.`1)). 
proc; auto.  
auto => /> *.           
by smt(assoc_none).
qed.

                        
lemma final_statement &m: 
  Pr [SS2.LI.EF_CMA_RO(HS(S1), A, QRO_l, SS2.KeyUpdating.O_CMA_Default).main() @ &m : res] 
  <= Pr [SS1.SI.I_EF_RMA_RO(S1, Reduction(QRO_l, A), SS1.KeyUpdating.O_RMA_Default, QRO_s).main() @ &m : res]
     +  `|Pr[R_QRO.ReproGame(QROrep,R_D_Repro(S1,A, QRO_s)).main(false) @ &m:res]
             - Pr[R_QRO.ReproGame(QROrep,R_D_Repro(S1,A, QRO_s)).main(true) @ &m:res]|
     + Pr[Coll.Col(CollisionFinder(S1, A, QRO_l)).main() @ &m : res].
proof. 
rewrite hopX Pr[mu_split GameX.coll] hop1 hopC1. 
smt(hopC2 hopC2pProb hop1 hop1prime hop2 hop3 hop4 no_coll_then_forge).
qed.


lemma final_statement_w_coll_bound &m: 
  Pr [SS2.LI.EF_CMA_RO(HS(S1), A, QRO_l, SS2.KeyUpdating.O_CMA_Default).main() @ &m : res] 
  <= Pr [SS1.SI.I_EF_RMA_RO(S1, Reduction(QRO_l, A), SS1.KeyUpdating.O_RMA_Default, QRO_s).main() @ &m : res]
     +  `|Pr[R_QRO.ReproGame(QROrep,R_D_Repro(S1,A,QRO_s)).main(false) @ &m:res]
             - Pr[R_QRO.ReproGame(QROrep,R_D_Repro(S1,A,QRO_s)).main(true) @ &m:res]|
     + (27 *(qS+qH +3)^3)%r * coDom.
proof. 
rewrite (RealOrder.ler_trans
  (Pr [SS1.SI.I_EF_RMA_RO(S1, Reduction(QRO_l, A), SS1.KeyUpdating.O_RMA_Default, QRO_s).main() @ &m : res]
     +  `|Pr[R_QRO.ReproGame(QROrep,R_D_Repro(S1,A, QRO_s)).main(false) @ &m:res]
             - Pr[R_QRO.ReproGame(QROrep,R_D_Repro(S1,A,QRO_s)).main(true) @ &m:res]|
     + Pr[Coll.Col(CollisionFinder(S1, A, QRO_l)).main() @ &m : res])).
apply final_statement.
apply RealOrder.ler_add => />. 
move : (Coll.pr_col  (CollisionFinder(S1, A, QRO_l)) &m) => /> /(_ _).
move : col_queries => />.
smt().
qed.


lemma final_statement_w_bounds &m: 
  Pr [SS2.LI.EF_CMA_RO(HS(S1), A, QRO_l, SS2.KeyUpdating.O_CMA_Default).main() @ &m : res] 
  <= Pr [SS1.SI.I_EF_RMA_RO(S1, Reduction(QRO_l, A), SS1.KeyUpdating.O_RMA_Default, QRO_s).main() @ &m : res]
     + (3%r/2%r) * qS%r * sqrt((qS + qH+1)%r*mu1 dr_t witness)
     + (27 *(qS+qH +3)^3)%r * coDom.
proof. 
rewrite (RealOrder.ler_trans
  (Pr [SS1.SI.I_EF_RMA_RO(S1, Reduction(QRO_l, A), SS1.KeyUpdating.O_RMA_Default, QRO_s).main() @ &m : res]
     +  `|Pr[R_QRO.ReproGame(QROrep,R_D_Repro(S1,A,QRO_s)).main(false) @ &m:res]
             - Pr[R_QRO.ReproGame(QROrep,R_D_Repro(S1,A,QRO_s)).main(true) @ &m:res]|
     + (27 *(qS+qH +3)^3)%r * coDom)).
apply final_statement_w_coll_bound.
do 2!(apply RealOrder.ler_add => />).
apply : (R_QRO.qrom_reprogramming &m (R_D_Repro(S1,A,QRO_s)) _).
by apply repro_queries.
qed.


end section MAIN_PROOF.

(*****************)

theory ROM_PROOF.

import R_QRO.CLASSICAL.

(* Classical adversary *)
module type Adv_EFCMA_RO_C(R : SS2.RO.ROM_.POracle, O : SS2.KeyUpdating.SOracle_CMA)  = {
  proc forge(pk : pk_l): msg_l * sig_l
}.


module (AWrap(A : Adv_EFCMA_RO_C) : SS2.LI.Adv_EFCMA_RO) (R : SS2.RO.QRO, O : SS2.KeyUpdating.SOracle_CMA) = {

  module OC : SS2.RO.ROM_.POracle = {
    proc o(x : SS2.RO.from) : SS2.RO.hash = {
        var y;
        y <@ R.h{x};
        return y;
    }
  }

  proc forge(pk : pk_l): msg_l * sig_l = {
     var r;
     r <@ A(OC,O).forge(pk);
     return r;
  }
}.

(* Classical signature *)

module type Scheme_RO_C(R : SS1.RO.ROM_.POracle)  = {
  proc keygen(): pk_s * sk_s
  proc sign(sk : sk_s, m : msg_s): sig_s * sk_s 
  proc verify(pk : pk_s, m : msg_s, sig : sig_s): bool 
}.


module (SWrap(S : Scheme_RO_C) : SS1.SI.Scheme_RO) (R : SS1.RO.QRO) = {

  module OC : SS1.RO.ROM_.POracle = {
    proc o(x : SS1.RO.from) : SS1.RO.hash = {
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

  proc sign(sk : sk_s, m : msg_s): sig_s * sk_s = {
     var r;
     r <@ S(OC).sign(sk,m);
     return r;
  }

  proc verify(pk : pk_s, m : msg_s, sig : sig_s): bool  = {
     var r;
     r <@ S(OC).verify(pk,m,sig);
     return r;

  }


}.


module O_l2s_C(O : SS2.RO.ROM_.POracle) = {
  proc o(m : SS1.RO.from): SS1.RO.hash = {
    var out : ro_out;
    
    out <@ O.o(true, m, witness, witness);
    
    return out.`1;
  }
}.

module ROmsg_C(O : SS2.RO.ROM_.POracle) = {
  proc o(rm : r_t * msg_l): msg_s = {
    var out : ro_out;
    
    out <@ O.o(false, witness, rm.`1, rm.`2);
    
    return out.`2;
  }
}.

module O_CMA_Game3_red_C(S1 : Scheme_RO_C, RO : R_QRO.QROM.ROM_.POracle, O : R_QRO.CLASSICAL.RepO_t, RO_s : SS1.RO.ROM_.Oracle) = {
  proc init(sk_init : sk_l): unit = {
    O_CMA_Game3_red.sk <- sk_init;
    O_CMA_Game3_red.qs <- [];
    O_CMA_Game3_red.msgs <- [];
  }
  
  proc sign(m : msg_l): sig_l = {
    var sig : sig_l;
    var sig_s : sig_s;
    var xs : SS2.RO.from * unit;
    var msg_s : ro_out;
    var sample_dist : ((bool * SS1.RO.from * r_t * msg_l) * unit) distr;
    
    sample_dist <- dmap dr_t (fun (r : r_t) => ((false, witness, r, m), tt));
    xs <@ O.repro(sample_dist);
    msg_s <@ RO.o(xs.`1);
    (sig_s, O_CMA_Game3_red.sk) <@ S1(RO_s).sign(O_CMA_Game3_red.sk, msg_s.`2);
    sig <- (xs.`1.`3, sig_s);
    O_CMA_Game3_red.qs <- rcons O_CMA_Game3_red.qs m;
    O_CMA_Game3_red.msgs <- rcons O_CMA_Game3_red.msgs (msg_s.`2, (xs.`1.`3, m));
    
    return sig;
  }
  
  proc fresh(m : msg_l): bool = {
    return ! (m \in O_CMA_Game3_red.qs);
  }
  
  proc nr_queries(): int = {
    return size O_CMA_Game3_red.qs;
  }
  
  proc msgs(): (msg_s * (r_t * msg_l)) list = {
    return O_CMA_Game3_red.msgs;
  }
}.

module OverwriteByQRO_s_C(Os : SS1.RO.ROM_.POracle, Ol : SS2.RO.ROM_.POracle) = {
  proc o(m : ro_in): ro_out = {
    var out : ro_out;
    var outl : ro_out;
    var outs : SS1.RO.hash;
    
    outs <@ Os.o(m.`2);
    outl <@ Ol.o(m);
    out <- if m.`1 /\ m.`3 = witness /\ m.`4 = witness then (outs, outl.`2) else outl;
    
    return out;
  }
}.

module CountingA_C(A : Adv_EFCMA_RO_C, H : SS2.RO.ROM_.POracle, O : SS2.KeyUpdating.SOracle_CMA) = {
  
  module Ho = {
    proc o(x : ro_in): ro_out = {
      var r : ro_out;
      
      r <- witness;
      r <@ H.o(x);
      CountingA.cH <- CountingA.cH + 1;
      
      return r;
    }
  }
  
  module S = {
    proc sign(m : msg_l): sig_l = {
      var r : sig_l;
      
      r <- witness;
      r <@ O.sign(m);
      CountingA.cS <- CountingA.cS + 1;
      
      return r;
    }
  }
  
  proc forge(pk : pk_l): msg_l * sig_l = {
    var r : msg_l * sig_l;
    
    CountingA.cH <- 0;
    CountingA.cS <- 0;
    r <@ A(Ho, S).forge(pk);
    
    return r;
  }
}.

module R_D_Repro_C(S : Scheme_RO_C, A : Adv_EFCMA_RO_C, RO_s : SS1.RO.ROM_.Oracle, RO : R_QRO.QROM.ROM_.POracle,
                 RO_r : R_QRO.CLASSICAL.RepO_t) = {
  module S1 = S(RO_s)
  
  module O = O_CMA_Game3_red_C(S, RO, RO_r, RO_s)
  
  var coll : bool
  
  proc distinguish(): bool = {
    var pk : pk_l;
    var sk : sk_l;
    var m : msg_l;
    var m_s : msg_s;
    var sig : sig_l;
    var nrqs : int;
    var is_valid : bool;
    var is_fresh : bool;
    var msgs : (msg_s * (r_t * msg_l)) list;
    
    RO_s.init();
    (pk, sk) <@ S1.keygen();
    O.init(sk);
    (m, sig) <@ CountingA_C(A, OverwriteByQRO_s_C(RO_s, RO), O).forge(pk);
    m_s <@ ROmsg_C(RO).o(sig.`1, m);
    is_valid <@ S1.verify(pk, m_s, sig.`2);
    is_fresh <@ O.fresh(m);
    nrqs <@ O.nr_queries();
    msgs <@ O.msgs();
    R_D_Repro.coll <- assoc msgs m_s <> None;
    
    return nrqs <= qS /\ is_valid /\ is_fresh /\ !R_D_Repro.coll;
  }
}.

import Coll.CLASSICAL.

module OverwriteByQROmsg_C(Os : QROm.ROM_.POracle, Ol : SS2.RO.ROM_.POracle) : SS2.RO.ROM_.POracle = {
  proc o(m : ro_in): ro_out = {
    var out : ro_out;
    var outl : ro_out;
    var outs : msg_s;
    
    outs <@ Os.o(m.`3, m.`4);
    outl <@ Ol.o(m);
    out <- if ! m.`1 /\ m.`2 = witness then (outl.`1, outs) else outl;
    
    return out;
  }
}.

module O_CMA_Coll_Simplified_C(S1 : Scheme_RO_C, O : SS2.RO.ROM_.POracle, O_s : SS1.RO.ROM_.POracle) = {
  
  proc init(sk_init : sk_l): unit = {
    O_CMA_Coll_Simplified.sk <- sk_init;
    O_CMA_Coll_Simplified.qs <- [];
    O_CMA_Coll_Simplified.msgs <- [];
  }
  
  proc sign(m : msg_l): sig_l = {
    var r : r_t;
    var sig : sig_l;
    var msg_tmp : ro_out;
    var sig_s : sig_s;
    
    r <$ dr_t;
    msg_tmp <@ O.o(false, witness, r, m);
    (sig_s, O_CMA_Coll_Simplified.sk) <@ S1(O_s).sign(O_CMA_Coll_Simplified.sk, msg_tmp.`2);
    sig <- (r, sig_s);
    O_CMA_Coll_Simplified.qs <- rcons O_CMA_Coll_Simplified.qs m;
    O_CMA_Coll_Simplified.msgs <- rcons O_CMA_Coll_Simplified.msgs (msg_tmp.`2, (r, m));
    
    return sig;
  }
  
  proc fresh(m : msg_l): bool = {
    return ! (m \in O_CMA_Coll_Simplified.qs);
  }
  
  proc nr_queries(): int = {
    return size O_CMA_Coll_Simplified.qs;
  }
  
  proc msgs(): (msg_s * (r_t * msg_l)) list = {
    return O_CMA_Coll_Simplified.msgs;
  }
}.

module CollisionFinder_C(S : Scheme_RO_C, A : Adv_EFCMA_RO_C, RO_l : SS2.RO.ROM_.Oracle, RO_m : QROm.ROM_.POracle) = {
  module R = OverwriteByQROmsg_C(RO_m, RO_l)
  
  module S1 = S(O_l2s_C(RO_l))
  
  module O = O_CMA_Coll_Simplified_C(S, R, O_l2s_C(RO_l))
  
  proc main(): (r_t * msg_l) * (r_t * msg_l) = {
    var pk : pk_l;
    var sk : sk_l;
    var m : msg_l;
    var m_s : msg_s;
    var sig : sig_l;
    var nrqs : int;
    var is_valid : bool;
    var is_fresh : bool;
    var msgs : (msg_s * (r_t * msg_l)) list;
    var x1 : r_t * msg_l;
    var x2 : r_t * msg_l;
    
    RO_l.init();
    (pk, sk) <@ S1.keygen();
    O.init(sk);
    (m, sig) <@ CountingA_C(A, R, O).forge(pk);
    x1 <- (sig.`1, m);
    m_s <@ ROmsg_C(R).o(sig.`1, m);
    is_valid <@ S1.verify(pk, m_s, sig.`2);
    is_fresh <@ O.fresh(m);
    nrqs <@ O.nr_queries();
    msgs <@ O.msgs();
    CollisionFinder.coll <- assoc msgs m_s <> None;
    x2 <- oget (assoc msgs m_s);
    
    return (x1, x2);
  }
}.

module TranslateH(H : SS2.RO.QRO) : SS2.RO.ROM_.POracle = {
     proc o(x : SS2.RO.from) : SS2.RO.hash = {
        var r;
        r <@ H.h{x};
        return r;
     }
}.

section. 

import R_QRO.QROM.ROM_.
import R_QRO.QROM.LE.

print rom_reprogramming.

declare module A <: Adv_EFCMA_RO_C {-QRO_s, -QRO_l, -QROmsg, -OverwriteByQRO_s, -R_QRO.Wrapped_QRO, -SS2.KeyUpdating.O_CMA_Default, -O_CMA_Repro, -O_CMA_Game3_red, -R_QRO.RepO, -R_QRO.QROM.QRO, -O_CMA_Game3, -SS1.KeyUpdating.O_RMA_Default, -Game4, -Reduction, -O_CMA_Coll, -CountingA, -O_CMA_Coll_Simplified, -ERO, -Wrapped_Oracle, -RepO, -QROm.LE.ERO, -SS1.RO.LE.ERO, -QROm.ROM_.Lazy.LRO, -SS2.RO.ROM_.Lazy.LRO, -SS2.RO.LE.ERO}.
declare module S1 <: Scheme_RO_C {-A, -QRO_s, -QRO_l, -QROmsg, -QROm.QRO, -OverwriteByQRO_s, -R_QRO.Wrapped_QRO, -SS2.KeyUpdating.O_CMA_Default, -O_CMA_Repro, -O_CMA_Game3_red, -R_QRO.QROM.QRO, -R_QRO.RepO, -O_CMA_Game3, -SS1.KeyUpdating.BaseOracle, -SS1.KeyUpdating.O_RMA_Default, -Game4, -Reduction, -O_CMA_Coll, -CountingA, -O_CMA_Coll_Simplified, -ERO, -Wrapped_Oracle, -RepO, -QROm.LE.ERO, -SS1.RO.LE.ERO, -QROm.QRO, -QROm.ROM_.Lazy.LRO, -SS2.RO.ROM_.Lazy.LRO, -SS2.RO.LE.ERO}.

module CA = AWrap(A).
module CS1 = SWrap(S1).

declare axiom forge_qQ (O <: SS2.KeyUpdating.SOracle_CMA { -A, -CountingA_C })
                      (H <: SS2.RO.QRO {-A, -CountingA_C}):
  hoare [CA(CountingA(CA, H, O).Ho, CountingA(CA, H, O).S).forge:
              CountingA.cS = 0
           /\ CountingA.cH = 0
         ==>  CountingA.cS <= qS
           /\ CountingA.cH <= qH].

declare axiom forge_q (O <: SS2.KeyUpdating.SOracle_CMA { -A, -CountingA_C })
                      (H <: SS2.RO.ROM_.POracle {-A, -CountingA_C}):
  hoare [A(CountingA_C(A, H, O).Ho, CountingA_C(A, H, O).S).forge:
              CountingA.cS = 0
           /\ CountingA.cH = 0
         ==>  CountingA.cS <= qS
           /\ CountingA.cH <= qH].

(* FIXME : I WOULD LIKE TO HAVE ONLY ONE OF THE ABOVE  and prove an implication, 
   but the module restrictions make this hard 

equiv translate_count (O <: SS2.KeyUpdating.SOracle_CMA { -CountingA, -A}) (H <: SS2.RO.QRO {-A, -CountingA, -O}):
  CA(CountingA(CA, H, O).Ho, CountingA(CA, H, O).S).forge ~
     A(CountingA_C(A, TranslateH(H), O).Ho, CountingA_C(A, TranslateH(H), O).S).forge
    : ={arg,glob CountingA, glob A, glob H, glob O} ==> ={glob CountingA}.
proof. 
proc*; inline {1} 1;wp;call(_: ={glob CountingA,glob O, glob H});1: by sim.
+ by proc *;inline *; wp; call(_: ={glob CountingA, glob O}); auto => />.  
auto => />. 
qed.

lemma wrap_count (O <: SS2.KeyUpdating.SOracle_CMA { -CountingA, -A}) (H <: SS2.RO.ROM_.Oracle {-A, -CountingA, -O}):
  hoare[ A(CountingA_C(A, H, O).Ho, CountingA_C(A, H, O).S).forge :
          CountingA.cS = 0 /\ CountingA.cH = 0 ==> CountingA.cS <= qS /\ CountingA.cH <= qH].  *)

declare axiom S1_keygen_ll (O <: SS1.RO.ROM_.POracle {-S1}) : 
   islossless O.o => islossless S1(O).keygen.

declare axiom S1_sign_ll (O <: SS1.RO.ROM_.POracle {-S1}) : 
   islossless O.o => islossless S1(O).sign.

declare axiom S1_verify_ll (O <: SS1.RO.ROM_.POracle {-S1}) : 
   islossless O.o => islossless S1(O).verify.

declare axiom A_ll (RO <: SS2.RO.ROM_.POracle {-A}) (O <: SS2.KeyUpdating.SOracle_CMA {-A}) : 
   islossless RO.o => islossless O.sign => islossless A(RO,O).forge.

lemma classical_repro &m b : 
   Pr[R_QRO.ReproGame(QROrep,R_D_Repro(CS1,CA, QRO_s)).main(b) @ &m:res]
             = Pr[ReproGame(ERO,R_D_Repro_C(S1,A,SS1.RO.LE.ERO)).main(b) @ &m:res].
proof. 
byequiv => //.
proc.
seq 1 1 : (#pre /\ forall x, ERO.m{2}.[x] <> None /\
     SS2.RO.QRO.h{1} x = oget (ERO.m{2}.[x])); 1: by
  call(SS2.RO.CLASSICAL.init_eager); auto => /> /#.
inline {1} 1; inline {2} 1.
inline {1} 3; inline {2} 3.
inline {1} 7; inline {2} 7.
swap {1} 7 -6; swap {2} 7 -6.
seq 1 1 : (#pre /\ forall x, SS1.RO.LE.ERO.m{2}.[x] <> None /\
     SS1.RO.QRO.h{1} x = oget (SS1.RO.LE.ERO.m{2}.[x])); 1: by
  call(SS1.RO.CLASSICAL.init_eager); auto => /> /#.
inline *.
wp;conseq  (_: _ ==> ={glob O_CMA_Game3_red,m_s,m} /\ r1{1} = is_valid{2}); 1: by smt().
call (_: 
    R_QRO.Wrapped_QRO.prog_list{1} = Wrapped_Oracle.prog_list{2} /\
   forall x, SS1.RO.LE.ERO.m{2}.[x] <> None /\
     SS1.RO.QRO.h{1} x = oget (SS1.RO.LE.ERO.m{2}.[x])); 
 1: by proc;inline *; auto => /#.
wp;  conseq (_: 
={glob O_CMA_Game3_red, pk, glob S1} /\ r2{1} = r{2} /\ R_QRO.Wrapped_QRO.prog_list{1} = Wrapped_Oracle.prog_list{2} /\
(forall x, SS1.RO.LE.ERO.m{2}.[x] <> None /\
     SS1.RO.QRO.h{1} x = oget (SS1.RO.LE.ERO.m{2}.[x])) );1: by smt(). 
call(_: ={glob S1, glob O_CMA_Game3_red} /\ (glob R_QRO.RepO){1} = (glob RepO){2} /\
    R_QRO.Wrapped_QRO.prog_list{1} = Wrapped_Oracle.prog_list{2} /\
 (forall x, SS1.RO.LE.ERO.m{2}.[x] <> None /\
     SS1.RO.QRO.h{1} x = oget (SS1.RO.LE.ERO.m{2}.[x])) /\
   (forall x, ERO.m{2}.[x] <> None /\
     SS2.RO.QRO.h{1} x = oget (ERO.m{2}.[x]))).
+ proc;inline *; auto => />.
call (_: 
    R_QRO.Wrapped_QRO.prog_list{1} = Wrapped_Oracle.prog_list{2} /\
   forall x, SS1.RO.LE.ERO.m{2}.[x] <> None /\
     SS1.RO.QRO.h{1} x = oget (SS1.RO.LE.ERO.m{2}.[x])); 
 1: by proc;inline *; auto => /#.

  wp;sp;conseq />;1: smt().
  seq 1 1 : (#pre /\ ={x,s}); 1: by auto => />.
  by if;auto =>/> /#.
by proc;inline *; auto => /> /#.

wp;call (_: 
    R_QRO.Wrapped_QRO.prog_list{1} = Wrapped_Oracle.prog_list{2} /\
  (forall x, SS1.RO.LE.ERO.m{2}.[x] <> None /\
     SS1.RO.QRO.h{1} x = oget (SS1.RO.LE.ERO.m{2}.[x])) /\
  (forall x, ERO.m{2}.[x] <> None /\
     SS2.RO.QRO.h{1} x = oget (ERO.m{2}.[x]))); 
    1: by proc;inline *; auto => /#.

by auto => />.
qed.

lemma classical_coll &m : 
   Pr[Coll.Col(CollisionFinder(CS1, CA, QRO_l)).main() @ &m : res]
    = Pr[Coll.CLASSICAL.Col_C(CollisionFinder_C(S1, A, ERO)).main() @ &m : res].
byequiv => //.
proc. 
seq 1 1 : (#pre /\ forall x, QROm.LE.ERO.m{2}.[x] <> None /\
     QROm.QRO.h{1} x = oget (QROm.LE.ERO.m{2}.[x])); 1: by
  call(QROm.CLASSICAL.init_eager_ctr); auto => /> /#.
inline {1} 1; inline {2} 1.
seq 1 1 : (#pre /\ forall x, SS2.RO.LE.ERO.m{2}.[x] <> None /\
     SS2.RO.QRO.h{1} x = oget (SS2.RO.LE.ERO.m{2}.[x])); 1: by
  call(SS2.RO.CLASSICAL.init_eager); auto => /> /#.
inline *.
wp; conseq  (_: _ ==> ={x1,m_s,glob O_CMA_Coll_Simplified} /\ 
     forall x, QROm.LE.ERO.m{2}.[x] <> None /\
     QROm.QRO.h{1} x = oget (QROm.LE.ERO.m{2}.[x])); 1: by smt().
call (_: 
    forall x, SS2.RO.LE.ERO.m{2}.[x] <> None /\
     SS2.RO.QRO.h{1} x = oget (SS2.RO.LE.ERO.m{2}.[x])); 
 1: by proc;inline *; auto => /#.
wp;conseq(_: _ ==> ={glob O_CMA_Coll_Simplified,pk, glob S1} /\ r2{1} = r{2} /\ 
     forall x, QROm.LE.ERO.m{2}.[x] <> None /\
     QROm.QRO.h{1} x = oget (QROm.LE.ERO.m{2}.[x]) /\
    (forall x, SS2.RO.LE.ERO.m{2}.[x] <> None /\
     SS2.RO.QRO.h{1} x = oget (SS2.RO.LE.ERO.m{2}.[x]))); 1: by smt().
call(_: ={glob O_CMA_Coll_Simplified,glob S1} /\
     (forall x, QROm.LE.ERO.m{2}.[x] <> None /\
     QROm.QRO.h{1} x = oget (QROm.LE.ERO.m{2}.[x])) /\
    (forall x, SS2.RO.LE.ERO.m{2}.[x] <> None /\
     SS2.RO.QRO.h{1} x = oget (SS2.RO.LE.ERO.m{2}.[x]))).
+ proc;inline *;wp;conseq />.
  call (_: 
    forall x, SS2.RO.LE.ERO.m{2}.[x] <> None /\
     SS2.RO.QRO.h{1} x = oget (SS2.RO.LE.ERO.m{2}.[x])); 
      1: by proc;inline *; auto => /#.
  by auto => /> /#.
+ by proc;inline*;auto =>/> /#.

wp;conseq />.
call (_: 
    forall x, SS2.RO.LE.ERO.m{2}.[x] <> None /\
     SS2.RO.QRO.h{1} x = oget (SS2.RO.LE.ERO.m{2}.[x])); 
 1: by proc;inline *; auto => /#.
by auto => />.
qed.

lemma repro_count :
  hoare [ R_D_Repro_C(S1, A, SS1.RO.LE.ERO, Wrapped_Oracle(SS2.RO.LE.ERO), RepO(Wrapped_Oracle(SS2.RO.LE.ERO))).distinguish :
   Wrapped_Oracle.ch = 0 /\ RepO.ctr = 0 /\ RepO.se ==>
   Wrapped_Oracle.ch <= qS + qH + 1 /\ RepO.ctr <= qS /\ RepO.se ].
  proc; inline*; auto.  
  call (_:  RepO.ctr <= qS 
         /\ Wrapped_Oracle.ch <= qS + qH + 1). 
  proc; inline *; auto.
  wp.
  call (_: RepO.ctr = CountingA.cS
        /\ Wrapped_Oracle.ch = CountingA.cH + CountingA.cS
        /\ CountingA.cH = 0 /\ CountingA.cS = 0
        /\ RepO.se
          ==>
          RepO.ctr = CountingA.cS
        /\ Wrapped_Oracle.ch = CountingA.cH + CountingA.cS
        /\ CountingA.cH <= qH /\ CountingA.cS <= qS 
        /\ RepO.se).
    conseq(_ :  CountingA.cS = 0 /\ CountingA.cH = 0 ==>
            CountingA.cS <= qS /\ CountingA.cH <= qH)
            (_ : RepO.ctr = CountingA.cS
              /\ Wrapped_Oracle.ch = CountingA.cH + CountingA.cS
              /\ RepO.se); first 2 by smt().
    + proc(RepO.ctr = CountingA.cS
        /\ Wrapped_Oracle.ch = CountingA.cH + CountingA.cS
        /\ RepO.se) => />.
    + proc; wp; inline *; auto. 
      call(_ : true). 
    + by proc; inline*; auto.
    auto.
    case RepO.b.
    rcondt 8.
    by auto => />. 
    auto => />; rewrite /sample_dist => // /> &hr *; split; 1: by smt(). 
    by rewrite p_max_val.

    rcondf 8.
    by auto => />. 
    auto => />; rewrite /sample_dist => // /> &hr *; split; 1: by smt(). 
    by rewrite p_max_val.

  + by proc; inline*; auto => /#.
    apply (forge_q 
            (O_CMA_Game3_red_C(S1, Wrapped_Oracle(SS2.RO.LE.ERO), RepO(Wrapped_Oracle(SS2.RO.LE.ERO)), SS1.RO.LE.ERO))
            (OverwriteByQRO_s_C(SS1.RO.LE.ERO, Wrapped_Oracle(SS2.RO.LE.ERO)))
           ).  
  wp => /=.
  call (_: true).
  + by proc; inline*; auto.
by while (#post); auto => /> /#.
qed.   

local module OO = O_CMA_Coll_Simplified_C(S1, OverwriteByQROmsg_C(D(CollisionFinder_C(S1, A, SS2.RO.LE.ERO), QROm.ROM_.Lazy.LRO).HC, SS2.RO.LE.ERO), O_l2s_C(SS2.RO.LE.ERO)).
local module HH = OverwriteByQROmsg_C(D(CollisionFinder_C(S1, A, SS2.RO.LE.ERO), QROm.ROM_.Lazy.LRO).HC, SS2.RO.LE.ERO).

lemma coll_count : 
   hoare [ CollisionFinder_C(S1, A, SS2.RO.LE.ERO, D(CollisionFinder_C(S1, A, SS2.RO.LE.ERO), QROm.ROM_.Lazy.LRO).HC).main : QROm.QRO.ch = 0 ==>  QROm.QRO.ch <= qH + qS + 1 ].
  proc; inline*; auto.  
  wp;call(_ :QROm.QRO.ch <= qH + qS + 1 ==> QROm.QRO.ch <= qH + qS + 1); 1: by auto=>/>.
  wp;rnd;wp;conseq(_: _ ==> QROm.QRO.ch <= qH + qS); 1: by smt().
  call (_: CountingA.cH + CountingA.cS = QROm.QRO.ch
          /\ CountingA.cH = 0 /\ CountingA.cS = 0
          ==>
          CountingA.cH + CountingA.cS = QROm.QRO.ch
          /\ CountingA.cH <= qH /\ CountingA.cS <= qS ).
    conseq(_ :  CountingA.cS = 0 /\ CountingA.cH = 0 ==>
            CountingA.cS <= qS /\ CountingA.cH <= qH)
            (_ : CountingA.cH + CountingA.cS = QROm.QRO.ch
             ==> CountingA.cH + CountingA.cS = QROm.QRO.ch); first 2 by smt().
    + proc(CountingA.cH + CountingA.cS = QROm.QRO.ch) => />. 
    + proc; inline*; auto. 
      call(_ : true). 
    + by proc; inline*; auto.
    by auto => />; smt().
  + by proc; inline*; auto => /#. 
    by apply (forge_q OO HH). (* FIXME: Internal modules cannode be parsed *)
  wp => /=.
  call (_: true).
  + by proc; inline*; auto.
  by while(true); auto => /> /#.
qed.

lemma final_statement_C &m: 
  Pr [SS2.LI.EF_CMA_RO(HS(CS1), CA, QRO_l, SS2.KeyUpdating.O_CMA_Default).main() @ &m : res] 
  <= Pr [SS1.SI.I_EF_RMA_RO(CS1, Reduction(QRO_l, CA), SS1.KeyUpdating.O_RMA_Default, QRO_s).main() @ &m : res]
     + qS%r * ((qS + qH + 1)%r * mu1 dr_t witness)
     + ((qH + qS + 3) * (qH + qS + 2))%r / 2%r * mu1 dmsg_s witness.
proof.
have qrom_statement := final_statement CA CS1 _ &m.
+ by move => O H; apply (forge_qQ O H). (* We should not need this axiom *)
rewrite !(classical_repro &m) in qrom_statement.
rewrite (classical_coll &m) in qrom_statement.

have rom_repro_bound := rom_reprogramming (R_D_Repro_C(S1, A, SS1.RO.LE.ERO)) &m repro_count.

have /= classical_col := Coll.CLASSICAL.pr_col (CollisionFinder_C(S1, A, SS2.RO.LE.ERO)) &m _ _. 
+ move => O Ho ; proc. inline 10. inline 9. inline 8. wp.
  call(_:true); 1: by move => R HR; apply (S1_verify_ll R HR).
  + by islossless. 
  inline 6. inline 7.
  wp; call(_: true); 1: by islossless.
  call Ho.
  wp;call(_: true).
  + islossless.
    apply (A_ll (<:CountingA_C(A, OverwriteByQROmsg_C(O, SS2.RO.LE.ERO), O_CMA_Coll_Simplified_C(S1, OverwriteByQROmsg_C(O, SS2.RO.LE.ERO), O_l2s_C(SS2.RO.LE.ERO))).Ho)
                (<: CountingA_C(A, OverwriteByQROmsg_C(O, SS2.RO.LE.ERO), O_CMA_Coll_Simplified_C(S1, OverwriteByQROmsg_C(O, SS2.RO.LE.ERO), O_l2s_C(SS2.RO.LE.ERO))).S)).
    + by islossless.
    by islossless; apply (S1_sign_ll (O_l2s_C(SS2.RO.LE.ERO))); islossless.
  inline 3. 
  wp; conseq />.
  call(_:true); 1: by move => R HR; apply (S1_keygen_ll R HR).
  + by islossless. 
  call(SS2.RO.LE.ERO_init_ll) => //.
  by move => *;rewrite SS2.RO.dhash_ll.
  
+ by apply coll_count.
  
move : qrom_statement rom_repro_bound classical_col.
by smt().
qed.

end section.
end ROM_PROOF.
