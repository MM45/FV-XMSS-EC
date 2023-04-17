(* --- Require/Import --- *)
(* -- Built-In (Standard Library) -- *)
require import AllCore List Distr DList IntDiv RealExp StdOrder SmtMap BitEncoding FinType.
require (*--*) Word Subtype ROM.
(*---*) import RField IntOrder RealOrder BS2Int.

(* -- Local -- *)
require (*--*) DigitalSignatures Reprogramming EFRMA_Interactive_Equiv.



(* Signature queries *)
op qS : { int | 0 <= qS } as ge0_qS.

(* Random oracle (hash) queries *)
op qH : { int | 0 <= qH } as ge0_qH.  



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


(* --- Distributions --- *)
op [lossless] dmsg_fl : msg_fl_t distr.

op [lossless] dmsg_al : msg_al_t distr.

op [lossless] drco : rco_t distr.



(* --- Clones --- *)
clone import DigitalSignatures as DSS_FL with
  type pk_t <= pk_fl_t,
  type sk_t <= sk_fl_t,
  type msg_t <= msg_fl_t,
  type sig_t <= sig_fl_t.
  
clone import DigitalSignatures as DSS_AL with
  type pk_t <= pk_al_t,
  type sk_t <= sk_al_t,
  type msg_t <= msg_al_t,
  type sig_t <= sig_al_t.

clone import DSS_FL.KeyUpdating.EFRMA as DSS_FL_EFRMA with
  op n_efrma <= qS,
  op dmsg <= dmsg_fl
  
  proof *.
  
  realize dmsg_ll by exact: dmsg_fl_ll.
  realize ge0_nefrma by exact: ge0_qS. 
  
   
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

clone import EFRMA_Interactive_Equiv as EFRMAEqv with
  type msg_t <= msg_fl_t,
  type sig_t <= sig_fl_t,
  type pk_t <= pk_fl_t,
  type sk_t <= sk_fl_t,
  
  op dmsg <= dmsg_fl,
  op n_efrma <= qS,
  
  theory ClassDS <= DSS_FL
  
  rename [theory] "Class_EFRMA" as "DSS_FL_EFRMA"
  
  proof *.

  realize dmsg_ll by exact: dmsg_fl_ll.
  realize ge0_nefrma by exact: ge0_qS.


(* --- Properties --- *)
(* -- EF-CMA -- *)
(* - Oracle Interfaces - *)
module type Oracle_CMA(S : DSS_AL.KeyUpdating.Scheme) = {
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
module (O_CMA : Oracle_CMA) (S : DSS_AL.KeyUpdating.Scheme) = {
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
module EF_CMA_RO(S : DSS_AL.KeyUpdating.Scheme, A : Adv_EFCMA_RO, SO : Oracle_CMA, HO : Oracle) = {
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
module AL_KU_DSS(FL_KU_DSS : DSS_FL.KeyUpdating.Scheme) : DSS_AL.KeyUpdating.Scheme = {
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
module (R_EFCMARO_CRRO (FL_KU_DSS : DSS_FL.KeyUpdating.Scheme, A : Adv_EFCMA_RO) : Adv_CR_RO) (HO : POracle) = {
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


module (R_EFCMARO_METCRRO (FL_KU_DSS : DSS_FL.KeyUpdating.Scheme, A : Adv_EFCMA_RO) : Adv_METCR_RO) (O : TOracle_METCR, HO : POracle) = {
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


module (R_EFCMARO_IEFRMA(A : Adv_EFCMA_RO) : Adv_I_EFRMA) (O : SOracle_RMA) = {
  module O_CMA_R_EFCMARO_IEFRMA : SOracle_CMA = {
    var qs : msg_al_t list
    var comps : (msg_fl_t * (rco_t * msg_al_t)) list 
    
    proc init() = {
      qs <- [];
      comps <- [];
    }
    
    proc sign(m : msg_al_t) : sig_al_t = {
      var rco : rco_t;
      var cm : msg_fl_t;
      var sigfl : sig_fl_t;
      var sig : sig_al_t;

      rco <$ drco;

      (cm, sigfl) <@ O.sign();
     
      Wrapped_Oracle(MCO).set((rco, m), cm);
      
      cm <@ Wrapped_Oracle(MCO).o((rco, m));

      sig <- (rco, sigfl);
      
      comps <- rcons comps (cm, (rco, m));
      qs <- rcons qs m;
      
      return sig;
    }
  }
  
  proc forge(pk : pk_fl_t) : msg_fl_t * sig_fl_t = {
    var m : msg_al_t;
    var sig : sig_al_t;
    var rco : rco_t;
    var cm : msg_fl_t;
    var sigfl : sig_fl_t;
        
    MCO.init();
    Wrapped_Oracle(MCO).init();
    O_CMA_R_EFCMARO_IEFRMA.init();
    
    (m, sig) <@ A(O_CMA_R_EFCMARO_IEFRMA, Wrapped_Oracle(MCO)).forge(pk); 
    
    rco <- sig.`1;
    sigfl <- sig.`2;
    
    cm <@ Wrapped_Oracle(MCO).o((rco, m));
    
    return (cm, sigfl);
  }
}.
(*
module QC_RO (O : POracle) : POracle = {
  var cH : int
  
  proc o(x : rco_t * msg_al_t) : msg_fl_t = {
    var cm : msg_fl_t;
    
    cH <- cH + 1;
    
    cm <@ O.o(x);
    
    return cm; 
  }
}.

module QC_SO (O : SOracle_CMA) : SOracle_CMA = {
  var cS : int
    
  proc sign(m : msg_al_t) : sig_al_t = {
    var sig : sig_al_t;
    
    cS <- cS + 1;
    
    sig <@ O.sign(m);
    
    return sig;
  }
}.


module QC_O (SO : SOracle_CMA) (PO : POracle)  : SOracle_CMA, POracle = {
  var cS : int
  var cH : int
  
  proc o(x : rco_t * msg_al_t) : msg_fl_t = {
    var cm : msg_fl_t;
    
    cH <- cH + 1;
    
    cm <@ PO.o(x);
    
    return cm; 
  }
  
  proc sign(m : msg_al_t) : sig_al_t = {
    var sig : sig_al_t;
    
    cS <- cS + 1;
    
    sig <@ SO.sign(m);
    
    return sig;
  }
}.
*)


module (QC_A(A : Adv_EFCMA_RO) : Adv_EFCMA_RO) (SO : SOracle_CMA) (RO : POracle) = {
  var cS : int
  var cH : int
  
  module QC_SO : SOracle_CMA = {
    proc sign(m : msg_al_t) : sig_al_t = {
      var sig : sig_al_t;

      cS <- cS + 1;

      sig <@ SO.sign(m);

      return sig;
    }
  }
  
  module QC_RO : POracle = {
    proc o(x : rco_t * msg_al_t) : msg_fl_t = {
      var cm : msg_fl_t;

      cH <- cH + 1;

      cm <@ RO.o(x);

      return cm; 
    }
  }
  
  proc forge(pk : pk_al_t) : msg_al_t * sig_al_t = {
    var m : msg_al_t;
    var sig : sig_al_t;
    
    cS <- 0;
    cH <- 0;
    
    (m, sig) <@ A(QC_SO, QC_RO).forge(pk);
    
    return (m, sig); 
  }
}.



section Proof_EFCMA_RO_ALKUDSS.

declare module FL_KU_DSS <: DSS_FL.KeyUpdating.Scheme{-ERO, -O_CMA, -O_METCR, -R_EFCMARO_CRRO, -R_EFCMARO_METCRRO, -Wrapped_Oracle, -RepO, -O_RMA_Default, -R_EFCMARO_IEFRMA, -QC_A}.
declare axiom FL_KU_DSS_verify_ll : islossless FL_KU_DSS.verify. 

declare module A <: Adv_EFCMA_RO{-FL_KU_DSS, -ERO, -O_CMA, -O_METCR, -R_EFCMARO_CRRO, -R_EFCMARO_METCRRO, -Wrapped_Oracle, -RepO, -O_RMA_Default, -R_EFCMARO_IEFRMA, -QC_A}.

(*
declare axiom A_forge_queries (RO <: POracle {-A, -QC_RO, -QC_SO}) (SO <: SOracle_CMA{-A, -QC_RO, -QC_SO}) : 
  hoare[A(QC_SO(SO), QC_RO(RO)).forge : QC_SO.cS = 0 /\ QC_RO.cH = 0 ==> QC_SO.cS <= qS /\ QC_RO.cH <= qH].
*)
declare axiom A_forge_queries (SO <: SOracle_CMA{-A, -QC_A}) (RO <: POracle{-A, -QC_A}):
  hoare[QC_A(A, SO, RO).forge : true ==> QC_A.cS <= qS /\ QC_A.cH <= qH].

local module O_CMA_CC = {
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

local module EF_CMA_RO_CC = {
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
    O_CMA_CC.init(sk);

    (*
      Ask the adversary to forge a signature for any message (and provide both the
      message and the signature) given the public key pk and access to a signing oracle 
      that it can query an unlimited number of times
    *)
    (m, sig) <@ A(O_CMA_CC, MCO).forge(pk);

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
    is_fresh <@ O_CMA_CC.fresh(m);
    
    (* Collision check *)
    rco <- sig.`1;
    cm <@ MCO.o(rco, m);
    comps <@ O_CMA_CC.compressions();
    
    coll <- assoc comps cm <> None;
    
    (* 
      Success iff
      (1) "is_valid": the forged signature provided by the adversary is valid, and
      (2) "is_fresh": the message for which the adversary forged a signature is fresh.
    *)
    return is_valid /\ is_fresh;
  }
}.

local equiv Equiv_EFCMARO_EFCMAROCC :
  EF_CMA_RO(AL_KU_DSS(FL_KU_DSS), A, O_CMA, MCO).main ~ EF_CMA_RO_CC.main : ={glob FL_KU_DSS, glob A} ==> ={res}.
proof.
proc; inline *.
seq 19 20 : (={is_valid, is_fresh}); last by wp.
seq 8 9 : (={glob FL_KU_DSS, pk, m, sig, ERO.m} /\ ={qs}(O_CMA, O_CMA_CC)); last by sim.
call (: ={glob FL_KU_DSS, ERO.m} /\ ={sk, qs}(O_CMA, O_CMA_CC)); first by proc.
+ proc; inline{1} 1. 
  by wp; call (: true); call (: ={ERO.m}); auto.
by wp; call (: true); while (={w, ERO.m}); auto.
qed.

local lemma EFCMAROCC_CRRO &m:
  Pr[EF_CMA_RO_CC.main() @ &m : res /\ EF_CMA_RO_CC.coll]
  <=
  Pr[CR_RO(R_EFCMARO_CRRO(FL_KU_DSS, A), MCO).main() @ &m : res].
proof.
byequiv => //.
proc; inline{1} 6; inline{2} 2.
conseq (: _ ==> is_fresh{1} /\ EF_CMA_RO_CC.coll{1} => kx{2} <> kx'{2} /\ y{2} = y'{2}); 1: by smt().
seq 4 4 : (   ={sk, comps}(O_CMA_CC, R_EFCMARO_CRRO.O_CMA_R_EFCMARO_CRRO) 
           /\ (glob MCO){1} = (glob ERO){2}
           /\ m{1} = mal'{2}
           /\ sig{1} = sig'{2}
           /\ (forall (mfl : msg_fl_t) (rmal : rco_t * msg_al_t), (mfl, rmal) \in O_CMA_CC.comps{1}
                 => mfl = oget (MCO.m{1}.[rmal]))
           /\ (forall (msg : msg_fl_t), assoc O_CMA_CC.comps{1} msg <> None 
                 => (oget (assoc O_CMA_CC.comps{1} msg)).`2 \in O_CMA_CC.qs{1})).
+ call (:   ={glob FL_KU_DSS}   
         /\ ={sk, comps}(O_CMA_CC, R_EFCMARO_CRRO.O_CMA_R_EFCMARO_CRRO)
         /\ (glob MCO){1} = (glob ERO){2}
         /\ (forall (mfl : msg_fl_t) (rmal : rco_t * msg_al_t), (mfl, rmal) \in O_CMA_CC.comps{1}
              => mfl = oget (MCO.m{1}.[rmal]))
         /\ (forall (msg : msg_fl_t), assoc O_CMA_CC.comps{1} msg <> None
              => (oget (assoc O_CMA_CC.comps{1} msg)).`2 \in O_CMA_CC.qs{1})).
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


local lemma EFCMAROCC_METCRRO &m:
  Pr[EF_CMA_RO_CC.main() @ &m : res /\ EF_CMA_RO_CC.coll]
  <=
  Pr[M_ETCR_RO(R_EFCMARO_METCRRO(FL_KU_DSS, A), O_METCR, MCO).main() @ &m : res].
proof.
byequiv => //.
proc; inline{2} 3.
conseq (: _ ==> is_fresh{1} /\ EF_CMA_RO_CC.coll{1} => 0 <= i{2} < nrts{2} /\ x{2} <> x'{2} /\ y{2} = y'{2}); 1: by smt().
seq 4 5 : (   ={sk, comps}(O_CMA_CC, R_EFCMARO_METCRRO.O_CMA_R_EFCMARO_METCRRO) 
           /\ (glob MCO){1} = (glob ERO){2}
           /\ m{1} = mal'{2}
           /\ sig{1} = sig'{2}
           /\ unzip2 R_EFCMARO_METCRRO.O_CMA_R_EFCMARO_METCRRO.comps{2} = O_METCR.ts{2}
           /\ (forall (mfl : msg_fl_t) (rmal : rco_t * msg_al_t), (mfl, rmal) \in O_CMA_CC.comps{1}
                 => mfl = oget (MCO.m{1}.[rmal]))
           /\ (forall (msg : msg_fl_t), assoc O_CMA_CC.comps{1} msg <> None 
                 => (oget (assoc O_CMA_CC.comps{1} msg)).`2 \in O_CMA_CC.qs{1})).
+ call (:   ={glob FL_KU_DSS}   
         /\ ={sk, comps}(O_CMA_CC, R_EFCMARO_METCRRO.O_CMA_R_EFCMARO_METCRRO)
         /\ (glob MCO){1} = (glob ERO){2}
         /\ unzip2 R_EFCMARO_METCRRO.O_CMA_R_EFCMARO_METCRRO.comps{2} = O_METCR.ts{2}
         /\ (forall (mfl : msg_fl_t) (rmal : rco_t * msg_al_t), (mfl, rmal) \in O_CMA_CC.comps{1}
              => mfl = oget (MCO.m{1}.[rmal]))
         /\ (forall (msg : msg_fl_t), assoc O_CMA_CC.comps{1} msg <> None
              => (oget (assoc O_CMA_CC.comps{1} msg)).`2 \in O_CMA_CC.qs{1})).
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

local module O_CMA_CC_NoRepro = {
  include var O_CMA_CC [-sign]

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
    cm <$ dmsg_fl;
    
    cm <@ Wrapped_Oracle(MCO).o((rco, m));

    (sigfl, sk) <@ FL_KU_DSS.sign(sk, cm);

    sig <- (rco, sigfl);

    comps <- rcons comps (cm, (rco, m));
    qs <- rcons qs m;

    return sig;
  }
}.


local module EF_CMA_RO_CC_NoRepro = {
  var coll : bool
  
  proc main() = {
    var pk : pk_al_t;
    var sk : sk_al_t;
    var m : msg_al_t;
    var sig : sig_al_t;
    var is_valid, is_fresh : bool;
    var rco : rco_t;
    var cm : msg_fl_t;
    var sigfl : sig_fl_t;
    var comps : (msg_fl_t * (rco_t * msg_al_t)) list;
    
    (* Initialize (hash) random oracle *)
    MCO.init();
    Wrapped_Oracle(MCO).init();
    
    (* Generate a key pair using the considered signature scheme *)
    (pk, sk) <@ AL_KU_DSS(FL_KU_DSS).keygen();

    (* Initialize the signing oracle with the generated secret key *)
    O_CMA_CC_NoRepro.init(sk);

    (*
      Ask the adversary to forge a signature for any message (and provide both the
      message and the signature) given the public key pk and access to a signing oracle 
      that it can query an unlimited number of times
    *)
    (m, sig) <@ A(O_CMA_CC_NoRepro, Wrapped_Oracle(MCO)).forge(pk);

    (* 
      Verify (w.r.t. message m) the signature sig provided by the adversary 
      using the verification algorithm of the considered signature scheme 
    *)
    rco <- sig.`1;
    sigfl <- sig.`2;
    cm <@ Wrapped_Oracle(MCO).o(rco, m);
    
    is_valid <@ FL_KU_DSS.verify(pk, cm, sigfl);

    (* 
      Check whether message for which the adversary forged a signature is fresh 
      (i.e., check whether message is not included in the list of messages for which 
      the adversary received signatures through an oracle query)
    *)
    is_fresh <@ O_CMA_CC_NoRepro.fresh(m);
    
    (* Collision check *)
    comps <@ O_CMA_CC_NoRepro.compressions();
    
    coll <- assoc comps cm <> None;
    
    (* 
      Success iff
      (1) "is_valid": the forged signature provided by the adversary is valid, and
      (2) "is_fresh": the message for which the adversary forged a signature is fresh.
    *)
    return is_valid /\ is_fresh;
  }
}.


local lemma EFCMAROCC_EFCMAROCCNoRepro &m :
  Pr[EF_CMA_RO_CC.main() @ &m : res /\ !EF_CMA_RO_CC.coll] =
  Pr[EF_CMA_RO_CC_NoRepro.main() @ &m : res /\ !EF_CMA_RO_CC_NoRepro.coll].
proof.
byequiv => //.
proc. inline *. wp => /=.
call (: true).
wp.
call (: ={glob O_CMA_CC, glob MCO} /\ Wrapped_Oracle.prog_list{2} = []).
proc. inline *. wp. skip. by progress.
proc. inline *. wp. call (: true). wp. rnd{2}. rnd. skip. progress.
wp.
call (: true).
wp. 
while (={w, ERO.m}).
sim.
wp.
by skip.
qed.
  
local module O_CMA_CC_ReproSample = {
  include var O_CMA_CC [-sign]

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
    cm <$ dmsg_fl;
    
    Wrapped_Oracle(MCO).set((rco, m), cm);
    cm <@ Wrapped_Oracle(MCO).o((rco, m));

    (sigfl, sk) <@ FL_KU_DSS.sign(sk, cm);

    sig <- (rco, sigfl);

    comps <- rcons comps (cm, (rco, m));
    qs <- rcons qs m;

    return sig;
  }
}.


local module EF_CMA_RO_CC_ReproSample = {
  var coll : bool
  
  proc main() = {
    var pk : pk_al_t;
    var sk : sk_al_t;
    var m : msg_al_t;
    var sig : sig_al_t;
    var is_valid, is_fresh : bool;
    var rco : rco_t;
    var cm : msg_fl_t;
    var sigfl : sig_fl_t;
    var comps : (msg_fl_t * (rco_t * msg_al_t)) list;
    
    (* Initialize (hash) random oracle *)
    MCO.init();
    Wrapped_Oracle(MCO).init();
    
    (* Generate a key pair using the considered signature scheme *)
    (pk, sk) <@ AL_KU_DSS(FL_KU_DSS).keygen();

    (* Initialize the signing oracle with the generated secret key *)
    O_CMA_CC_ReproSample.init(sk);

    (*
      Ask the adversary to forge a signature for any message (and provide both the
      message and the signature) given the public key pk and access to a signing oracle 
      that it can query an unlimited number of times
    *)
    (m, sig) <@ A(O_CMA_CC_ReproSample, Wrapped_Oracle(MCO)).forge(pk);

    (* 
      Verify (w.r.t. message m) the signature sig provided by the adversary 
      using the verification algorithm of the considered signature scheme 
    *)
    rco <- sig.`1;
    sigfl <- sig.`2;
    cm <@ Wrapped_Oracle(MCO).o(rco, m);
    
    is_valid <@ FL_KU_DSS.verify(pk, cm, sigfl);

    (* 
      Check whether message for which the adversary forged a signature is fresh 
      (i.e., check whether message is not included in the list of messages for which 
      the adversary received signatures through an oracle query)
    *)
    is_fresh <@ O_CMA_CC_ReproSample.fresh(m);
    
    (* Collision check *)
    comps <@ O_CMA_CC_ReproSample.compressions();
    
    coll <- assoc comps cm <> None;
    
    (* 
      Success iff
      (1) "is_valid": the forged signature provided by the adversary is valid, and
      (2) "is_fresh": the message for which the adversary forged a signature is fresh.
    *)
    return is_valid /\ is_fresh;
  }
}.

local module (R_Repro_EFCMARORepro : DistA) (WMCO : POracle, RepWMCO : RepO_t) = {
  module O_R_Repro_EFCMARORepro = {
    include var O_CMA_CC [-sign]
    
    proc sign(m : msg_al_t) : sig_al_t = {
      var rco : rco_t;
      var cm : msg_fl_t;
      var sigfl : sig_fl_t;
      var sig : sig_al_t;
      
      (rco, m) <@ RepWMCO.repro(dmap drco (fun (rco : rco_t) => (rco, m)));
      
      cm <@ WMCO.o((rco, m));
      
      (sigfl, sk) <@ FL_KU_DSS.sign(sk, cm);
      
      sig <- (rco, sigfl);
      
      comps <- rcons comps (cm, (rco, m));
      qs <- rcons qs m;
      
      return sig;
    } 
  }
  
  proc distinguish() : bool = {
    var pk : pk_al_t;
    var sk : sk_al_t;
    var m : msg_al_t;
    var sig : sig_al_t;
    var is_valid, is_fresh : bool;
    var rco : rco_t;
    var cm : msg_fl_t;
    var sigfl : sig_fl_t;
    var comps : (msg_fl_t * (rco_t * msg_al_t)) list;
    var coll : bool;
    
    (pk, sk) <@ AL_KU_DSS(FL_KU_DSS).keygen();
    
    O_R_Repro_EFCMARORepro.init(sk);
    
    (m, sig) <@ QC_A(A, O_R_Repro_EFCMARORepro, WMCO).forge(pk);
    
    rco <- sig.`1;
    sigfl <- sig.`2;
    cm <@ WMCO.o(rco, m);
    
    is_valid <@ FL_KU_DSS.verify(pk, cm, sigfl);

    is_fresh <@ O_R_Repro_EFCMARORepro.fresh(m);
    
    comps <@ O_R_Repro_EFCMARORepro.compressions();
    
    coll <- assoc comps cm <> None;

    return is_valid /\ is_fresh /\ !coll;
  }
}.

local lemma EFCMARORepro_ReproGame &m:
  `| Pr[EF_CMA_RO_CC_NoRepro.main() @ &m : res /\ !EF_CMA_RO_CC_NoRepro.coll] -
     Pr[EF_CMA_RO_CC_ReproSample.main() @ &m : res /\ !EF_CMA_RO_CC_ReproSample.coll] |
  =
  `| Pr[ReproGame(MCO, R_Repro_EFCMARORepro).main(false) @ &m : res] -
     Pr[ReproGame(MCO, R_Repro_EFCMARORepro).main(true) @ &m : res] |.
proof.
do 2! congr; last congr.
+ byequiv => //.
  proc; inline *.
  wp; call (: true); wp => /=.
  call (:   ={glob FL_KU_DSS, glob O_CMA_CC, Wrapped_Oracle.prog_list} 
         /\ RepO.b{2} = false
         /\ Wrapped_Oracle.prog_list{2} = []).
  - proc; inline *. 
    by wp; skip.
  - proc; inline *.
    rcondf{2} 7; 1: by auto.
    wp; call (: true); wp => /=.
    rnd{1}.
    rnd (fun (rco : rco_t) => (rco, m{2})) 
        (fun (kx : rco_t * msg_al_t) => kx.`1).
    wp; skip => /> &1.
    split => [rcom | rcomeq].
    * by move/supp_dmap => [rco] [_ ->].
    split => [rcom rcomin | rcom_mu1 rco rcoin].
    * by rewrite (in_dmap1E_can _ _ (fun (x : _ * _) => x.`1)) //= /#.
    by rewrite supp_dmap; exists rco; rewrite rcoin.
  wp; call (: true); wp; while (={w, ERO.m}).
  - by wp; rnd; wp; skip.
  by wp; skip.
byequiv => //.
proc; inline *.
wp; call (: true); wp => /=.
call (:   ={glob FL_KU_DSS, glob O_CMA_CC, Wrapped_Oracle.prog_list} 
       /\ RepO.b{2} = true).
+ proc; inline *. 
  by wp; skip.
+ proc; inline *.
  rcondt{2} 7; 1: by auto.
  wp; call (: true); wp => /=.
  rnd.
  rnd (fun (rco : rco_t) => (rco, m{2})) 
      (fun (kx : rco_t * msg_al_t) => kx.`1).
  wp; skip => /> &1.
  split => [rcom | rcomeq].
  * by move/supp_dmap => [rco] [_ ->].
  split => [rcom rcomin | rcom_mu1 rco rcoin].
  * by rewrite (in_dmap1E_can _ _ (fun (x : _ * _) => x.`1)) //= /#.
  by rewrite supp_dmap; exists rco; rewrite rcoin.
wp; call (: true); wp; while (={w, ERO.m}).
+ by wp; rnd; wp; skip.
by wp; skip.
qed.

local module T = R_Repro_EFCMARORepro(Wrapped_Oracle(ERO), RepO(Wrapped_Oracle(ERO))).

local hoare test :
  R_Repro_EFCMARORepro(Wrapped_Oracle(MCO), RepO(Wrapped_Oracle(MCO))).distinguish :
    Wrapped_Oracle.ch = 0 /\ RepO.ctr = 0 /\ RepO.se 
    ==> 
    Wrapped_Oracle.ch <= qS + qH + 1 /\ RepO.ctr <= qS /\ RepO.se.
proof.
proc.
wp.
do 3! (call (: true) => //).
inline 6; inline 7.
wp => /=.
call (: Wrapped_Oracle.ch = 0 /\ RepO.ctr = 0 /\ RepO.se
        ==>
           QC_A.cS <= qS /\ QC_A.cH <= qH
        /\ Wrapped_Oracle.ch = QC_A.cH + QC_A.cS /\ RepO.ctr = QC_A.cS /\ RepO.se). 
conseq (: Wrapped_Oracle.ch = 0 /\ RepO.ctr = 0 /\ RepO.se
          ==>
          Wrapped_Oracle.ch = QC_A.cH + QC_A.cS /\ RepO.ctr = QC_A.cS /\ RepO.se)
       (: true ==>  QC_A.cS <= qS /\ QC_A.cH <= qH) => //.
       apply: (A_forge_queries (T.O_R_Repro_EFCMARORepro) (Wrapped_Oracle(ERO))).

proc.
wp. 
call (: Wrapped_Oracle.ch = QC_A.cH + QC_A.cS /\ RepO.ctr = QC_A.cS /\ RepO.se).
proc.
inline *.
wp. 
by skip => /#.
proc.
inline *.
auto.
call (: true).
auto.
case RepO.b.
+ rcondt 7; 1: auto.
  wp.
  rnd. rnd.
  wp. skip.
  progress ; 1: smt().
  admit.
rcondf 7; 1 : auto.
rnd.
wp.
skip.
progress.
smt().
admit.
wp.
skip. 
progress.
call(: true) => //.
call(: true) => //.
skip => /#.
qed.

local module O_CMA_CC_ReproQuery = {
  include var O_CMA_CC [-init, sign]

  proc init() = {
    qs <- [];
    comps <- [];
  }

  proc sign(m : msg_al_t) : sig_al_t = {
    var rco : rco_t;
    var cm : msg_fl_t;
    var sigfl : sig_fl_t;
    var sig : sig_al_t;

    rco <$ drco;
    
    (cm, sigfl) <@ O_RMA_Default(FL_KU_DSS).sign();

    Wrapped_Oracle(MCO).set((rco, m), cm);
    cm <@ Wrapped_Oracle(MCO).o((rco, m));

    sig <- (rco, sigfl);

    comps <- rcons comps (cm, (rco, m));
    qs <- rcons qs m;

    return sig;
  }
}.


local module EF_CMA_RO_CC_ReproQuery = {
  var coll : bool
  
  proc main() = {
    var pk : pk_al_t;
    var sk : sk_al_t;
    var m : msg_al_t;
    var sig : sig_al_t;
    var is_valid, is_fresh : bool;
    var rco : rco_t;
    var cm : msg_fl_t;
    var sigfl : sig_fl_t;
    var comps : (msg_fl_t * (rco_t * msg_al_t)) list;
    var nrqs : int;
    
    (* Initialize (hash) random oracle *)
    MCO.init();
    Wrapped_Oracle(MCO).init();
    
    (* Generate a key pair using the considered signature scheme *)
    (pk, sk) <@ AL_KU_DSS(FL_KU_DSS).keygen();

    (* Initialize the signing oracle with the generated secret key *)
    O_RMA_Default(FL_KU_DSS).init(sk);
    O_CMA_CC_ReproQuery.init();

    (*
      Ask the adversary to forge a signature for any message (and provide both the
      message and the signature) given the public key pk and access to a signing oracle 
      that it can query an unlimited number of times
    *)
    (m, sig) <@ QC_A(A, O_CMA_CC_ReproQuery, Wrapped_Oracle(MCO)).forge(pk);

    (* 
      Verify (w.r.t. message m) the signature sig provided by the adversary 
      using the verification algorithm of the considered signature scheme 
    *)
    rco <- sig.`1;
    sigfl <- sig.`2;
    cm <@ Wrapped_Oracle(MCO).o(rco, m);
    
    is_valid <@ FL_KU_DSS.verify(pk, cm, sigfl);

    (* 
      Check whether message for which the adversary forged a signature is fresh 
      (i.e., check whether message is not included in the list of messages for which 
      the adversary received signatures through an oracle query)
    *)
    is_fresh <@ O_CMA_CC_ReproQuery.fresh(m);
    
    (* Collision check *)
    comps <@ O_CMA_CC_ReproSample.compressions();
    
    coll <- assoc comps cm <> None;
    
    (* Get number of signing queries *)
    nrqs <@ O_CMA_CC_ReproQuery.nr_queries();
    
    (* 
      Success iff
      (1) "is_valid": the forged signature provided by the adversary is valid, and
      (2) "is_fresh": the message for which the adversary forged a signature is fresh.
    *)
    return nrqs <= qS /\ is_valid /\ is_fresh;
  }
}.

local lemma EFRMAROCCReproSample_Query &m:
  Pr[EF_CMA_RO_CC_ReproSample.main() @ &m : res /\ !EF_CMA_RO_CC_ReproSample.coll]
  =
  Pr[EF_CMA_RO_CC_ReproQuery.main() @ &m : res /\ !EF_CMA_RO_CC_ReproQuery.coll].
proof.
byequiv => //.
proc.
seq 5 6 : (   ={glob FL_KU_DSS, O_CMA_CC.comps, O_CMA_CC.qs, MCO.m, Wrapped_Oracle.prog_list, pk, m, sig}
           /\ QC_A.cS{2} = size O_CMA_CC.qs{2}
           /\ QC_A.cS{2} <= qS).
+ call (:   ={glob FL_KU_DSS, glob A, O_CMA_CC.comps, O_CMA_CC.qs, MCO.m, Wrapped_Oracle.prog_list, pk} 
         /\ ={sk}(O_CMA_CC, O_RMA_Default)
         /\ O_CMA_CC.qs{2} = []
           ==> 
            ={res, glob FL_KU_DSS, O_CMA_CC.comps, O_CMA_CC.qs, MCO.m, Wrapped_Oracle.prog_list}
         /\ ={sk}(O_CMA_CC, O_RMA_Default)
         /\ QC_A.cS{2} = size O_CMA_CC.qs{2}
         /\ QC_A.cS{2} <= qS).
  - conseq (:   ={arg, glob FL_KU_DSS, glob A, O_CMA_CC.comps, O_CMA_CC.qs, MCO.m, Wrapped_Oracle.prog_list} 
             /\ ={sk}(O_CMA_CC, O_RMA_Default)
             /\ O_CMA_CC.qs{2} = []
               ==> 
                ={res, glob FL_KU_DSS, O_CMA_CC.comps, O_CMA_CC.qs, MCO.m, Wrapped_Oracle.prog_list} 
             /\ ={sk}(O_CMA_CC, O_RMA_Default)
             /\ QC_A.cS{2} = size O_CMA_CC.qs{2})
           _
           (: true ==> QC_A.cS <= qS /\ QC_A.cH <= qH) => //.
    * by apply (A_forge_queries O_CMA_CC_ReproQuery (Wrapped_Oracle(MCO))).
    proc *; inline *.
    wp.
    call (:   ={glob FL_KU_DSS, O_CMA_CC.comps, O_CMA_CC.qs, MCO.m, Wrapped_Oracle.prog_list}
           /\ ={sk}(O_CMA_CC, O_RMA_Default)
           /\ QC_A.cS{2} = size O_CMA_CC.qs{2}).
    * proc; inline *.
      by wp; skip.
    * proc; inline *.
      wp; call (: true); wp => /=.
      rnd; rnd.
      by wp; skip => />; smt(size_rcons).
    by wp; skip => /> /#.
  inline *.
  wp; call (: true); wp => /=. 
  while (={w, ERO.m}); 1: by auto.
  by wp; skip.
inline *.
wp; call(: true); wp => /=.  
by skip => />. 
qed.

local lemma EFRMAROCCReproQuery_IEFRMA &m :
  Pr[EF_CMA_RO_CC_ReproQuery.main() @ &m : res /\ !EF_CMA_RO_CC_ReproQuery.coll]
  <=
  Pr[I_EF_RMA(FL_KU_DSS, R_EFCMARO_IEFRMA(A), O_RMA_Default).main() @ &m : res].
proof.
byequiv => //.
proc; inline *.
wp => /=. call (: true); wp => /=. print R_EFCMARO_IEFRMA. print O_RMA_Default.
call (:    ={glob FL_KU_DSS, MCO.m, Wrapped_Oracle.prog_list, O_RMA_Default.sk}
        /\ ={qs, comps}(O_CMA_CC, R_EFCMARO_IEFRMA.O_CMA_R_EFCMARO_IEFRMA)
        /\ size R_EFCMARO_IEFRMA.O_CMA_R_EFCMARO_IEFRMA.qs{2} = size DSS_FL.O_Base_Default.qs{2}
        /\ (forall (cm : msg_fl_t), 
              (! exists (m : msg_al_t) (rco : rco_t), (cm, (rco, m)) \in R_EFCMARO_IEFRMA.O_CMA_R_EFCMARO_IEFRMA.comps{2}) 
              =>
              ! cm \in DSS_FL.O_Base_Default.qs{2})).
+ proc; inline *.
  by wp; skip.
+ proc; inline *.
  wp; call (: true) => /=.
  rnd; rnd.
  wp; skip => /> &2 eqsz ninqs rco rcoin cm cmin.
  rewrite 2!size_rcons eqsz assoc_cons /= => cm'.
  rewrite mem_rcons /= negb_or => nex; split.
  - move: nex; apply contra => ->.
    by exists m{2} rco; rewrite mem_rcons. 
  apply ninqs; rewrite negb_exists => m /=; rewrite negb_exists => rco' /=.
  move: nex; rewrite negb_exists => /(_ m) /=; rewrite negb_exists => /(_ rco') /=.
  by rewrite mem_rcons /= negb_or => [#].
swap{1} 6 -5.
wp.
while (={w, ERO.m}); 1: by auto.
wp; call(:true); wp => /=.
skip => /> cmap msig comps' qs qs' plist eqsz ninqsp ver ltqS_szqs verT ninqs.
pose ifte := if _ then _ else _; move=> eqnone.
rewrite -eqsz ltqS_szqs /=; apply: ninqsp.
rewrite negb_exists /= => m; rewrite negb_exists /= => rco.
move/iffRL /contra: (assoc_none comps' ifte) => /= /(_ eqnone).
by rewrite negb_exists /= => /(_ (rco, m)).
qed.


lemma iefrma_cr_lemma_test &m :
  Pr[EF_CMA_RO(AL_KU_DSS(FL_KU_DSS), A, O_CMA, MCO).main() @ &m : res]
  <=
  Pr[CR_RO(R_EFCMARO_CRRO(FL_KU_DSS, A), MCO).main() @ &m : res]
  +
  `| Pr[ReproGame(MCO, R_Repro_EFCMARORepro).main(false) @ &m : res] -
     Pr[ReproGame(MCO, R_Repro_EFCMARORepro).main(true) @ &m : res] |
  +
  Pr[I_EF_RMA(FL_KU_DSS, R_EFCMARO_IEFRMA(A), O_RMA_Default).main() @ &m : res].
proof. print Equiv_EFCMARO_EFCMAROCC.
have ->:
  Pr[EF_CMA_RO(AL_KU_DSS(FL_KU_DSS), A, O_CMA, MCO).main() @ &m : res]
  =
  Pr[EF_CMA_RO_CC.main() @ &m : res].
+ by byequiv Equiv_EFCMARO_EFCMAROCC.
rewrite Pr[mu_split EF_CMA_RO_CC.coll] -addrA ler_add 1:EFCMAROCC_CRRO.
rewrite EFCMAROCC_EFCMAROCCNoRepro -ger0_norm 1:Pr[mu_ge0] // -subr0.
rewrite -(subrr Pr[EF_CMA_RO_CC_ReproSample.main() @ &m : res /\ !EF_CMA_RO_CC_ReproSample.coll]).
rewrite opprB (addrC Pr[EF_CMA_RO_CC_ReproSample.main() @ &m : res /\ !EF_CMA_RO_CC_ReproSample.coll]) addrA.
apply (ler_trans (`|  Pr[EF_CMA_RO_CC_NoRepro.main() @ &m : res /\ !EF_CMA_RO_CC_NoRepro.coll]
                    - Pr[EF_CMA_RO_CC_ReproSample.main() @ &m : res /\ !EF_CMA_RO_CC_ReproSample.coll] |
                  + Pr[EF_CMA_RO_CC_ReproSample.main() @ &m : res /\ !EF_CMA_RO_CC_ReproSample.coll])).
+ by rewrite -{4}(ger0_norm Pr[EF_CMA_RO_CC_ReproSample.main() @ &m : res /\ !EF_CMA_RO_CC_ReproSample.coll]) 1:Pr[mu_ge0] 2:&(ler_norm_add).
apply ler_add; 1: by rewrite EFCMARORepro_ReproGame.
by rewrite EFRMAROCCReproSample_Query EFRMAROCCReproQuery_IEFRMA.
qed.

end section Proof_EFCMA_RO_ALKUDSS.
