(* --- Require/Import --- *)
(* -- Built-In (Standard Library) -- *)
require import AllCore List Distr DList IntDiv RealExp StdOrder SmtMap BitEncoding FinType.
require (*--*) Word Subtype ROM.
(*---*) import RField IntOrder RealOrder BS2Int.

(* -- Local -- *)
require import Reprogramming.
require (*--*) DigitalSignatures.





(* --- Types --- *)
(* -- Fixed-length digital signature scheme -- *) 
type pk_fl_t.

type sk_fl_t.

type msg_fl_t.

clone import FinType as MSG_FL with
  type t <= msg_fl_t.

type sig_fl_t.


(* -- Arbitrary-length digital signature scheme -- *) 
type rco_t.

clone import FinType as RCO with
  type t <= rco_t.

type pk_al_t = pk_fl_t.

type sk_al_t = sk_fl_t.

type msg_al_t.

clone import FinType as MSG_AL with
  type t <= msg_al_t.

type sig_al_t = rco_t * sig_fl_t.

clone import FinProdType as RCOMSGAL with
  type t1 <= rco_t,
  type t2 <= msg_al_t,
  theory FT1 <= RCO,
  theory FT2 <= MSG_AL.

print RCOMSGAL.

(* --- Distributions --- *)
op [lossless] dmsg_fl : msg_fl_t distr.

op [lossless] dmsg_al : msg_al_t distr.

op [lossless] drco : rco_t distr.



(* --- Clones --- *)
clone import DigitalSignatures as DSS1 with
  type pk_t <- pk_fl_t,
  type sk_t <- sk_fl_t,
  type msg_t <- msg_fl_t,
  type sig_t <- sig_fl_t
  
  rename [theory] "Stateless" as "FL_SL"
  rename [theory] "KeyUpdating" as "FL_KU".

clone import DigitalSignatures as DSS2 with
  type pk_t <- pk_al_t,
  type sk_t <- sk_al_t,
  type msg_t <- msg_al_t,
  type sig_t <- sig_al_t
  
  rename [theory] "Stateless" as "AL_SL"
  rename [theory] "KeyUpdating" as "AL_KU".

clone import ROM as MCORO with
  type in_t <- rco_t * msg_al_t,
  type out_t <- msg_fl_t,
  op dout <- fun _ => dmsg_fl,
  type d_in_t <- int,
  type d_out_t <- bool.

clone import MCORO.LazyEager as MCOROLE with 
  theory FinType <= RCOMSGAL.
  
module MCO = ERO.

clone import Reprogramming as Repro with
    type from <- rco_t * msg_al_t,
    type hash <- msg_fl_t,
  
      op dhash <- dmsg_fl,
      
  theory MUFF.FinT <= RCOMSGAL,
  theory MUFFH.FinT <= MSG_FL,
  theory ROM_ <= MCORO,
  theory LE <= MCOROLE
  
  proof dhash_ll by exact: dmsg_fl_ll.

  
(* --- Properties --- *)
(* -- EF-CMA -- *)
(* - Oracle Interfaces - *)
module type Oracle_CMA(S : AL_KU.Scheme) = {
  proc init(sk_init : sk_al_t) : unit {}
  proc sign(m : msg_al_t) : sig_al_t {S.sign}
  proc fresh(m : msg_al_t) : bool {}
  proc nr_queries() : int {}
}.

module type SOracle_CMA = {
  proc sign(m : msg_al_t) : sig_al_t
}.

  
(* - Adversary Classes - *)
module type Adv_EFCMA_RO(SO : SOracle_CMA, HO : POracle) = {
  proc forge(pk : pk_al_t) : msg_al_t * sig_al_t 
}.


(* - Oracles - *)
module (O_CMA : Oracle_CMA) (S : AL_KU.Scheme) = {
    var sk : sk_al_t
    var qs : msg_al_t list
    
    (* Initialize secret/signing key and oracle query list qs *)
    proc init(sk_init : sk_al_t) : unit = {
      sk <- sk_init;
      qs <- [];
    }

    (* 
      Sign given message m using the considered signature scheme with the
      secret/signing key sk and append m to the list of oracle queries qs
    *)
    proc sign(m : msg_al_t) : sig_al_t = {
      var sig : sig_al_t;
      
      (sig, sk) <@ S.sign(sk, m);

      qs <- rcons qs m;
            
      return sig;
    }

    (* 
      Check whether given message m is fresh, i.e., whether m is not contained in
      the list of oracle queries qs 
    *)
    proc fresh(m : msg_al_t) : bool = {
      return ! m \in qs;
    }
    
    (* Get the number of oracle queries, i.e., the size of the oracle query list qs *)
    proc nr_queries() : int = {
      return size qs;
    }
}.

(* - - *)
module EF_CMA_RO(S : AL_KU.Scheme, A : Adv_EFCMA_RO, SO : Oracle_CMA, HO : Oracle) = {
  proc main() = {
    var pk : pk_al_t;
    var sk : sk_al_t;
    var m : msg_al_t;
    var sig : sig_al_t;
    var is_valid, is_fresh : bool;
    
    (* Initialize (hash) random oracle *)
    HO.init();
    
    (* Generate a key pair using the considered signature scheme *)
    (pk, sk) <@ S.keygen();

    (* Initialize the signing oracle with the generated secret key *)
    SO(S).init(sk);

    (*
      Ask the adversary to forge a signature for any message (and provide both the
      message and the signature) given the public key pk and access to a signing oracle 
      that it can query an unlimited number of times
    *)
    (m, sig) <@ A(SO(S), HO).forge(pk);

    (* 
      Verify (w.r.t. message m) the signature sig provided by the adversary 
      using the verification algorithm of the considered signature scheme 
    *)
    is_valid <@ S.verify(pk, m, sig);

    (* 
      Check whether message for which the adversary forged a signature is fresh 
      (i.e., check whether message is not included in the list of messages for which 
      the adversary received signatures through an oracle query)
    *)
    is_fresh <@ SO(S).fresh(m);

    (* 
      Success iff
      (1) "is_valid": the forged signature provided by the adversary is valid, and
      (2) "is_fresh": the message for which the adversary forged a signature is fresh.
    *)
    return is_valid /\ is_fresh;
  }
}.


(* -- CR (for a random oracle) -- *)
module type Adv_CR_RO(HO : POracle) = {
  proc find() : (rco_t * msg_al_t) * (rco_t * msg_al_t)
}.

module CR_RO(A : Adv_CR_RO, HO : Oracle) = {
  proc main() = {
    var kx, kx' : rco_t * msg_al_t;
    var y, y' : msg_fl_t;
    
    HO.init();
    
    (kx, kx') <@ A(HO).find();
    
    y <@ HO.o(kx);
    y' <@ HO.o(kx');
    
    return kx <> kx' /\ y = y';
  }
}.


(* -- M-eTCR (for a random oracle) -- *)
(* Type for oracles used in M_ETCR game *)
module type Oracle_METCR = {
  proc init() : unit
  proc query(x : msg_al_t) : rco_t
  proc get(i : int) : rco_t * msg_al_t
  proc nr_targets() : int
}.

module type TOracle_METCR = {
  proc query(x : msg_al_t) : rco_t
}.

(* Implementation of an oracle for M_ETCR *)
module O_METCR : Oracle_METCR = {
  var ts : (rco_t * msg_al_t) list
  
  proc init() : unit = {
    ts <- [];
  }
  
  proc query(m : msg_al_t) : rco_t = {
    var rco : rco_t;
    
    rco <$ drco;
    
    ts <- rcons ts (rco, m);
      
    return rco;
  }
  
  (* Gets i-th element in list of targets; returns witness if index is out of bounds *)
  proc get(i : int) : rco_t * msg_al_t = {
    return nth witness ts i;
  }
  
  (* Returns the number of elements in the list of targets *)
  proc nr_targets() : int = {
    return size ts; 
  }
}.


(* Class of adversaries against M_ETCR *)
module type Adv_METCR_RO(O : TOracle_METCR, HO : POracle) = {
  proc find() : int * rco_t * msg_al_t
}.

module M_ETCR_RO(A : Adv_METCR_RO, O : Oracle_METCR, HO : Oracle) = {
  proc main() = {
    var k, k' : rco_t;
    var x, x' : msg_al_t;
    var y, y' : msg_fl_t;
    var i, nrts : int;
    
    O.init();
    HO.init();
    
    (i, k', x') <@ A(O, HO).find();
    
    (k, x) <@ O.get(i);
    
    y <@ HO.o((k, x));
    y' <@ HO.o((k', x'));
    
    nrts <@ O.nr_targets();
    
    return 0 <= i < nrts /\ x <> x' /\ y = y';
  }
}.

 
(* --- Scheme --- *)
module AL_KU_DSS(FL_KU_DSS : FL_KU.Scheme) : AL_KU.Scheme = {
  proc keygen = FL_KU_DSS.keygen
  
  proc sign(sk : sk_al_t, m : msg_al_t) : sig_al_t * sk_al_t = {
    var rco : rco_t;
    var cm : msg_fl_t;
    var sigfl : sig_fl_t;
    var sig : sig_al_t;
    
    rco <$ drco;
    
    cm <@ MCO.o((rco, m));
    
    (sigfl, sk) <@ FL_KU_DSS.sign(sk, cm);
    
    sig <- (rco, sigfl);
    
    return (sig, sk);
  }
  
  proc verify(pk : pk_al_t, m : msg_al_t, sig : sig_al_t) : bool = {
    var rco : rco_t;
    var cm : msg_fl_t;
    var sigfl : sig_fl_t;
    var ver : bool;
    
    rco <- sig.`1;
    
    cm <@ MCO.o((rco, m));
    
    sigfl <- sig.`2;
    
    ver <@ FL_KU_DSS.verify(pk, cm, sigfl);
    
    return ver;
  }
}.



(* --- Reduction Adversaries --- *)
module (R_EFCMARO_CRRO (FL_KU_DSS : FL_KU.Scheme, A : Adv_EFCMA_RO) : Adv_CR_RO) (HO : POracle) = {
  module O_CMA_R_EFCMARO_CRRO : SOracle_CMA  = {
    var sk : sk_al_t
    var comps : (msg_fl_t * (rco_t * msg_al_t)) list
    
    proc init(sk_init : sk_al_t) = {
      sk <- sk_init;
      comps <- [];
    }
    
    proc sign(m : msg_al_t) : sig_al_t = {
      var rco : rco_t;
      var cm : msg_fl_t;
      var sigfl : sig_fl_t;
      var sig : sig_al_t;
      
      rco <$ drco;

      cm <@ HO.o((rco, m));

      (sigfl, sk) <@ FL_KU_DSS.sign(sk, cm);

      sig <- (rco, sigfl);

      comps <- rcons comps (cm, (rco, m));
            
      return sig;
    }
  }
  
  proc find() : (rco_t * msg_al_t) * (rco_t * msg_al_t) = {
    var pk : pk_al_t;
    var sk : sk_al_t;
    var rco, rco' : rco_t;
    var mal, mal' : msg_al_t;
    var sig' : sig_al_t;
    var mfl' : msg_fl_t;
    
    (pk, sk) <@ AL_KU_DSS(FL_KU_DSS).keygen();
    
    O_CMA_R_EFCMARO_CRRO.init(sk);
    
    (mal', sig') <@ A(O_CMA_R_EFCMARO_CRRO, HO).forge(pk);
    
    rco' <- sig'.`1;
    
    mfl' <@ HO.o((rco', mal'));
    
    (rco, mal) <- oget (assoc O_CMA_R_EFCMARO_CRRO.comps mfl');
    
    return ((rco, mal), (rco', mal'));
  }
}.  

search assoc onth. search map zip.
module (R_EFCMARO_METCRRO (FL_KU_DSS : FL_KU.Scheme, A : Adv_EFCMA_RO) : Adv_METCR_RO) (O : TOracle_METCR, HO : POracle) = {
  module O_CMA_R_EFCMARO_METCRRO : SOracle_CMA  = {
    var sk : sk_al_t
    var comps : (msg_fl_t * (rco_t * msg_al_t)) list
    
    proc init(sk_init : sk_al_t) = {
      sk <- sk_init;
      comps <- [];
    }
    
    proc sign(m : msg_al_t) : sig_al_t = {
      var rco : rco_t;
      var cm : msg_fl_t;
      var sigfl : sig_fl_t;
      var sig : sig_al_t;
      
      rco <@ O.query(m);

      cm <@ HO.o((rco, m));

      (sigfl, sk) <@ FL_KU_DSS.sign(sk, cm);

      sig <- (rco, sigfl);

      comps <- rcons comps (cm, (rco, m));
            
      return sig;
    }
  }
  
  proc find() : int * rco_t * msg_al_t = {
    var pk : pk_al_t;
    var sk : sk_al_t;
    var rco, rco' : rco_t;
    var mal, mal' : msg_al_t;
    var sig' : sig_al_t;
    var mfl' : msg_fl_t;
    var i : int;
    
    (pk, sk) <@ AL_KU_DSS(FL_KU_DSS).keygen();
    
    O_CMA_R_EFCMARO_METCRRO.init(sk);
    
    (mal', sig') <@ A(O_CMA_R_EFCMARO_METCRRO, HO).forge(pk);
    
    rco' <- sig'.`1;
    
    mfl' <@ HO.o((rco', mal'));
    
    i <- index mfl' (unzip1 O_CMA_R_EFCMARO_METCRRO.comps);
    
    return (i, rco', mal');
  }
}.  



section Proof_EFCMA_RO_ALKUDSS.

declare module FL_KU_DSS <: FL_KU.Scheme{-ERO, -O_CMA, -O_METCR, -R_EFCMARO_CRRO, -R_EFCMARO_METCRRO}.
declare axiom FL_KU_DSS_verify_ll : islossless FL_KU_DSS.verify. 

declare module A <: Adv_EFCMA_RO{-FL_KU_DSS, -ERO, -O_CMA, -O_METCR, -R_EFCMARO_CRRO, -R_EFCMARO_METCRRO}.

(* Signature queries *)
declare op qS : { int | 0 <= qS } as ge0_qS.

(* Random Oracle (Hash) queries *)
declare op qH : { int | 0 <= qH } as ge0_qH.  


local module O_CMA_Coll = {
    var sk : sk_al_t
    var qs : msg_al_t list
    var comps : (msg_fl_t * (rco_t * msg_al_t)) list 
        
    (* Initialize secret/signing key and oracle query list qs *)
    proc init(sk_init : sk_al_t) : unit = {
      sk <- sk_init;
      qs <- [];
      comps <- [];
    }

    (* 
      Sign given message m using the considered signature scheme with the
      secret/signing key sk and append m to the list of oracle queries qs
    *)
    proc sign(m : msg_al_t) : sig_al_t = {
      var rco : rco_t;
      var cm : msg_fl_t;
      var sigfl : sig_fl_t;
      var sig : sig_al_t;

      rco <$ drco;

      cm <@ MCO.o((rco, m));

      (sigfl, sk) <@ FL_KU_DSS.sign(sk, cm);

      sig <- (rco, sigfl);

      comps <- rcons comps (cm, (rco, m));
      qs <- rcons qs m;
      
      return sig;
    }

    (* 
      Check whether given message m is fresh, i.e., whether m is not contained in
      the list of oracle queries qs 
    *)
    proc fresh(m : msg_al_t) : bool = {
      return ! m \in qs;
    }
    
    (* Get the number of oracle queries, i.e., the size of the oracle query list qs *)
    proc nr_queries() : int = {
      return size qs;
    }
    
    proc compressions() : (msg_fl_t * (rco_t * msg_al_t)) list = {
      return comps;
    }
}.

local module EF_CMA_RO_Coll = {
  var coll : bool
  
  proc main() = {
    var pk : pk_al_t;
    var sk : sk_al_t;
    var m : msg_al_t;
    var sig : sig_al_t;
    var is_valid, is_fresh : bool;
    var rco : rco_t;
    var cm : msg_fl_t;
    var comps : (msg_fl_t * (rco_t * msg_al_t)) list;
    
    (* Initialize (hash) random oracle *)
    MCO.init();
    
    (* Generate a key pair using the considered signature scheme *)
    (pk, sk) <@ AL_KU_DSS(FL_KU_DSS).keygen();

    (* Initialize the signing oracle with the generated secret key *)
    O_CMA_Coll.init(sk);

    (*
      Ask the adversary to forge a signature for any message (and provide both the
      message and the signature) given the public key pk and access to a signing oracle 
      that it can query an unlimited number of times
    *)
    (m, sig) <@ A(O_CMA_Coll, MCO).forge(pk);

    (* 
      Verify (w.r.t. message m) the signature sig provided by the adversary 
      using the verification algorithm of the considered signature scheme 
    *)
    is_valid <@ AL_KU_DSS(FL_KU_DSS).verify(pk, m, sig);

    (* 
      Check whether message for which the adversary forged a signature is fresh 
      (i.e., check whether message is not included in the list of messages for which 
      the adversary received signatures through an oracle query)
    *)
    is_fresh <@ O_CMA_Coll.fresh(m);
    
    (* Collision check *)
    rco <- sig.`1;
    cm <@ MCO.o(rco, m);
    comps <@ O_CMA_Coll.compressions();
    
    coll <- assoc comps cm <> None;
    
    (* 
      Success iff
      (1) "is_valid": the forged signature provided by the adversary is valid, and
      (2) "is_fresh": the message for which the adversary forged a signature is fresh.
    *)
    return is_valid /\ is_fresh;
  }
}.

local equiv Equiv_EFCMARO_EFCMAROColl :
  EF_CMA_RO(AL_KU_DSS(FL_KU_DSS), A, O_CMA, MCO).main ~ EF_CMA_RO_Coll.main : ={glob FL_KU_DSS, glob A} ==> ={res}.
proof.
proc; inline *.
seq 19 20 : (={is_valid, is_fresh}); last by wp.
seq 8 9 : (={glob FL_KU_DSS, pk, m, sig, ERO.m} /\ ={qs}(O_CMA, O_CMA_Coll)); last by sim.
call (: ={glob FL_KU_DSS, ERO.m} /\ ={sk, qs}(O_CMA, O_CMA_Coll)); first by proc.
+ proc; inline{1} 1. 
  by wp; call (: true); call (: ={ERO.m}); auto.
by wp; call (: true); while (={w, ERO.m}); auto.
qed.

local lemma EFCMAROColl_CRRO &m:
  Pr[EF_CMA_RO_Coll.main() @ &m : res /\ EF_CMA_RO_Coll.coll]
  <=
  Pr[CR_RO(R_EFCMARO_CRRO(FL_KU_DSS, A), MCO).main() @ &m : res].
proof.
byequiv => //.
proc; inline{1} 6; inline{2} 2.
conseq (: _ ==> is_fresh{1} /\ EF_CMA_RO_Coll.coll{1} => kx{2} <> kx'{2} /\ y{2} = y'{2}); 1: by smt().
seq 4 4 : (   ={sk, comps}(O_CMA_Coll, R_EFCMARO_CRRO.O_CMA_R_EFCMARO_CRRO) 
           /\ (glob MCO){1} = (glob ERO){2}
           /\ m{1} = mal'{2}
           /\ sig{1} = sig'{2}
           /\ (forall (mfl : msg_fl_t) (rmal : rco_t * msg_al_t), (mfl, rmal) \in O_CMA_Coll.comps{1}
                 => mfl = oget (MCO.m{1}.[rmal]))
           /\ (forall (msg : msg_fl_t), assoc O_CMA_Coll.comps{1} msg <> None 
                 => (oget (assoc O_CMA_Coll.comps{1} msg)).`2 \in O_CMA_Coll.qs{1})).
+ call (:   ={glob FL_KU_DSS}   
         /\ ={sk, comps}(O_CMA_Coll, R_EFCMARO_CRRO.O_CMA_R_EFCMARO_CRRO)
         /\ (glob MCO){1} = (glob ERO){2}
         /\ (forall (mfl : msg_fl_t) (rmal : rco_t * msg_al_t), (mfl, rmal) \in O_CMA_Coll.comps{1}
              => mfl = oget (MCO.m{1}.[rmal]))
         /\ (forall (msg : msg_fl_t), assoc O_CMA_Coll.comps{1} msg <> None
              => (oget (assoc O_CMA_Coll.comps{1} msg)).`2 \in O_CMA_Coll.qs{1})).
  - by proc; skip.
  - proc; inline *.
    wp; call (: true); wp; rnd; skip => /> &1 &2 comps_def compsqs_rel rco _.
    split => [mfl rmal | mfl]; rewrite mem_rcons /=.
    * by move=> -[[-> <-] //|]; apply comps_def.
    rewrite -cats1 assoc_cat.
    case (mfl \in unzip1 R_EFCMARO_CRRO.O_CMA_R_EFCMARO_CRRO.comps{2}) => assin.
    * by move/compsqs_rel => ->.
    by move/assocTP => /= ->; rewrite assoc_cons.
  inline{1} 3; inline{2} 3.
  wp; call (: true).
  call (: true ==> (glob MCO){1} = (glob ERO){2}); last by skip.
  proc.
  by while (={w, ERO.m}); auto.
inline *; wp.
call{1} (: true ==> true); 1: by apply FL_KU_DSS_verify_ll.
wp; skip => /> &1 &2 comps_def compsqs_rel malnin assnnone.
split; 1: by rewrite negb_and; right => /#.
pose cm := oget ERO.m{2}.[sig'{2}.`1, mal'{2}].
move: (comps_def cm (oget (assoc R_EFCMARO_CRRO.O_CMA_R_EFCMARO_CRRO.comps{2} cm)) _).
+ by move/assocTP: assnnone; apply assoc_get_mem. 
by move=> {3}-> /#.
qed.


local lemma EFCMAROColl_METCRRO &m:
  Pr[EF_CMA_RO_Coll.main() @ &m : res /\ EF_CMA_RO_Coll.coll]
  <=
  Pr[M_ETCR_RO(R_EFCMARO_METCRRO(FL_KU_DSS, A), O_METCR, MCO).main() @ &m : res].
proof.
byequiv => //.
proc; inline{2} 3.
conseq (: _ ==> is_fresh{1} /\ EF_CMA_RO_Coll.coll{1} => 0 <= i{2} < nrts{2} /\ x{2} <> x'{2} /\ y{2} = y'{2}); 1: by smt().
seq 4 5 : (   ={sk, comps}(O_CMA_Coll, R_EFCMARO_METCRRO.O_CMA_R_EFCMARO_METCRRO) 
           /\ (glob MCO){1} = (glob ERO){2}
           /\ m{1} = mal'{2}
           /\ sig{1} = sig'{2}
           /\ unzip2 R_EFCMARO_METCRRO.O_CMA_R_EFCMARO_METCRRO.comps{2} = O_METCR.ts{2}
           /\ (forall (mfl : msg_fl_t) (rmal : rco_t * msg_al_t), (mfl, rmal) \in O_CMA_Coll.comps{1}
                 => mfl = oget (MCO.m{1}.[rmal]))
           /\ (forall (msg : msg_fl_t), assoc O_CMA_Coll.comps{1} msg <> None 
                 => (oget (assoc O_CMA_Coll.comps{1} msg)).`2 \in O_CMA_Coll.qs{1})).
+ call (:   ={glob FL_KU_DSS}   
         /\ ={sk, comps}(O_CMA_Coll, R_EFCMARO_METCRRO.O_CMA_R_EFCMARO_METCRRO)
         /\ (glob MCO){1} = (glob ERO){2}
         /\ unzip2 R_EFCMARO_METCRRO.O_CMA_R_EFCMARO_METCRRO.comps{2} = O_METCR.ts{2}
         /\ (forall (mfl : msg_fl_t) (rmal : rco_t * msg_al_t), (mfl, rmal) \in O_CMA_Coll.comps{1}
              => mfl = oget (MCO.m{1}.[rmal]))
         /\ (forall (msg : msg_fl_t), assoc O_CMA_Coll.comps{1} msg <> None
              => (oget (assoc O_CMA_Coll.comps{1} msg)).`2 \in O_CMA_Coll.qs{1})).
  - by proc; skip.
  - proc; inline *.
    wp; call (: true); wp; rnd; wp; skip => /> &1 &2 comps_def compsqs_rel rco _.
    split; last split => [ mfl rmal | mfl].
    * by rewrite map_rcons.
    * by rewrite mem_rcons /= => -[[-> <-] // |]; apply comps_def.
    rewrite mem_rcons -cats1 assoc_cat /=.
    case (mfl \in unzip1 R_EFCMARO_METCRRO.O_CMA_R_EFCMARO_METCRRO.comps{2}) => assin.
    * by move/compsqs_rel => ->.
    by move/assocTP => /= ->; rewrite assoc_cons.
  inline *.
  wp; call (: true).
  by while (={w, ERO.m}); auto.
inline *; wp.
call{1} (: true ==> true); 1: by apply FL_KU_DSS_verify_ll.
wp; skip => /> &1 &2 comps_def compsqs_rel malnin assnnone.
split; 1: split => [| _]; 1: by rewrite index_ge0.
+ have ->:
    size (unzip2 R_EFCMARO_METCRRO.O_CMA_R_EFCMARO_METCRRO.comps{2})
    =
    size (unzip1 R_EFCMARO_METCRRO.O_CMA_R_EFCMARO_METCRRO.comps{2}).
  - by rewrite 2!size_map.
  by rewrite index_mem -assocTP.
split; 1: by rewrite nth_onth -assoc_zip 1:2!size_map // zip_unzip /#.
pose cm := oget ERO.m{2}.[sig'{2}.`1, mal'{2}].
move: (comps_def cm (oget (assoc R_EFCMARO_METCRRO.O_CMA_R_EFCMARO_METCRRO.comps{2} cm)) _).
+ by move/assocTP: assnnone; apply assoc_get_mem. 
move=> {3}->; congr; congr.
rewrite eq_sym -{1}(zip_unzip R_EFCMARO_METCRRO.O_CMA_R_EFCMARO_METCRRO.comps{2}).
by rewrite assoc_zip 1:2!size_map // nth_onth /oget /#.
qed.

end section Proof_EFCMA_RO_ALKUDSS.
