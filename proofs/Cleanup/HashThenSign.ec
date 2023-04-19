(* --- Require/Import --- *)
(* -- Built-In (Standard Library) -- *)
require import AllCore List Distr DList IntDiv RealExp StdOrder SmtMap BitEncoding FinType.
require (*--*) Word Subtype ROM.
(*---*) import RField IntOrder RealOrder BS2Int.

(* -- Local -- *)
require (*--*) DigitalSignatures KeyedHashFunctions Reprogramming EFRMA_Interactive_Equiv.



(* Message-signature pairs *)
op n : { int | 0 <= n } as ge0_n.

(* Signature queries *)
op qS : { int | 0 <= qS <= n } as rng_qS.

(* Random oracle (hash) queries *)
op qH : { int | 0 <= qH } as ge0_qH. 



(* --- Types --- *)
(* -- Fixed-length digital signature scheme -- *) 
type pk_fl_t.

type sk_fl_t.

type msg_fl_t.

clone import FinType as MSG_FL with
  type t <- msg_fl_t.

type sig_fl_t.


(* -- Arbitrary-length digital signature scheme -- *)
type rco_t.

clone import FinType as RCO with
  type t <- rco_t.

type pk_al_t = pk_fl_t.

type msg_al_t.

clone import FinType as MSG_AL with
  type t <= msg_al_t.

type sig_al_t = rco_t * sig_fl_t.

clone import FinProdType as RCOMSGAL with
  type t1 <- rco_t,
  type t2 <- msg_al_t,
  theory FT1 <- RCO,
  theory FT2 <- MSG_AL.

  
(* --- Distributions --- *)
op [lossless full uniform] dmsg_fl : msg_fl_t distr.

op [lossless] dmsg_al : msg_al_t distr.

op [lossless full uniform] drco : rco_t distr.


(* --- Clones --- *)
clone import DigitalSignatures as DSS_FL with
  type pk_t <= pk_fl_t,
  type sk_t <= sk_fl_t,
  type msg_t <= msg_fl_t,
  type sig_t <= sig_fl_t.

clone import ROM as MCORO with
  type in_t <- rco_t * msg_al_t,
  type out_t <- msg_fl_t,
  op dout <- fun _ => dmsg_fl,
  type d_in_t <- int,
  type d_out_t <- bool.

clone import MCORO.LazyEager as MCOROLE with 
  theory FinType <- RCOMSGAL.

module MCO = ERO.

clone import Reprogramming as Repro with
    type from <- rco_t * msg_al_t,
    type hash <- msg_fl_t,
      
      op p_max_bound <- mu1 drco witness,
         
      op dhash <- dmsg_fl,
      
  theory MUFF.FinT <- RCOMSGAL,
  theory MUFFH.FinT <- MSG_FL,
  theory ROM_ <- MCORO,
  theory LE <- MCOROLE
  
  proof dhash_ll by exact: dmsg_fl_ll.

clone import EFRMA_Interactive_Equiv as EFRMAEqv with
  type msg_t <- msg_fl_t,
  type sig_t <- sig_fl_t,
  type pk_t <- pk_fl_t,
  type sk_t <- sk_fl_t,
  
  op n_efrma <- n,
  op dmsg <- dmsg_fl,
  
  theory ClassDS <- DSS_FL
  
  rename [theory] "Class_EFRMA" as "DSS_FL_EFRMA"
  
  proof *. 
  realize dmsg_ll by exact: dmsg_fl_ll.
  realize ge0_nefrma by exact: ge0_n.
  
import DSS_FL_EFRMA.


(* --- Auxiliary --- *)
lemma p_max_rcom (m : msg_al_t) :
  p_max (dmap drco (fun (rco : rco_t) => (rco, m))) = mu1 drco witness.
proof.
apply ler_anti; split => [|_].
+ move: (listmax_in Real.(<=) RealOrder.ler_trans RealOrder.ler_total). 
  move=> /(_ 0%r (map (fun (x : rco_t * msg_al_t) => 
                          mu (dmap drco (fun (rco : rco_t) => (rco, m))) ((=) x)) 
                       RCOMSGAL.enum) _).
  - rewrite size_map; move: (enumP witness).
    by case RCOMSGAL.enum => //=; smt(size_ge0).
  move/mapP => @/p_max [rcom] [rcomin /= ->].
  by rewrite dmapE /(\o) /= (drco_uni witness rcom.`1) 1,2:drco_fu /pred1 mu_le.
apply (ler_trans (mu1 (dmap drco (fun (rco : rco_t) => (rco, m))) (witness, m))) => [| @/pred1].
+ rewrite ler_eqVlt; left.
  by rewrite dmap1E /pred1 /(\o).
by rewrite (mu_eq _ _ (fun (p : rco_t * msg_al_t) => (witness, m) = p)) 1:/# p_maxE.
qed.  


(* --- Properties --- *)
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


theory WithSampling.

type sk_al_t = sk_fl_t.

clone import DigitalSignatures as DSS_AL with
  type pk_t <- pk_al_t,
  type sk_t <- sk_al_t,
  type msg_t <- msg_al_t,
  type sig_t <- sig_al_t.

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
module type Adv_EFCMA_RO(SO : SOracle_CMA, RO : POracle) = {
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
module EF_CMA_RO(S : DSS_AL.KeyUpdating.Scheme, A : Adv_EFCMA_RO, SO : Oracle_CMA, RO : Oracle) = {
  proc main() = {
    var pk : pk_al_t;
    var sk : sk_al_t;
    var m : msg_al_t;
    var sig : sig_al_t;
    var is_valid, is_fresh : bool;
    
    (* Initialize (hash) random oracle *)
    RO.init();
    
    (* Generate a key pair using the considered signature scheme *)
    (pk, sk) <@ S.keygen();

    (* Initialize the signing oracle with the generated secret key *)
    SO(S).init(sk);

    (*
      Ask the adversary to forge a signature for any message (and provide both the
      message and the signature) given the public key pk and access to a signing oracle 
      that it can query an unlimited number of times
    *)
    (m, sig) <@ A(SO(S), RO).forge(pk);

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
module (R_EFCMARO_CRRO (FL_KU_DSS : DSS_FL.KeyUpdating.Scheme, A : Adv_EFCMA_RO) : Adv_CR_RO) (RO : POracle) = {
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

      cm <@ RO.o((rco, m));

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
    
    (mal', sig') <@ A(O_CMA_R_EFCMARO_CRRO, RO).forge(pk);
    
    rco' <- sig'.`1;
    
    mfl' <@ RO.o((rco', mal'));
    
    (rco, mal) <- oget (assoc O_CMA_R_EFCMARO_CRRO.comps mfl');
    
    return ((rco, mal), (rco', mal'));
  }
}.  


module (R_EFCMARO_METCRRO (FL_KU_DSS : DSS_FL.KeyUpdating.Scheme, A : Adv_EFCMA_RO) : Adv_METCR_RO) (O : TOracle_METCR, RO : POracle) = {
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

      cm <@ RO.o((rco, m));

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
    
    (mal', sig') <@ A(O_CMA_R_EFCMARO_METCRRO, RO).forge(pk);
    
    rco' <- sig'.`1;
    
    mfl' <@ RO.o((rco', mal'));
    
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



section Proofs_EFCMA_RO_ALKUDSS.

declare module FL_KU_DSS <: DSS_FL.KeyUpdating.Scheme{-ERO, -O_CMA, -O_METCR, -R_EFCMARO_CRRO, -R_EFCMARO_METCRRO, -Wrapped_Oracle, -RepO, -O_RMA_Default, -R_EFCMARO_IEFRMA, -QC_A, -Lazy.LRO, -ReproGame, -R_EFRMA_IEFRMA}.

declare axiom FL_KU_DSS_sign_ll : islossless FL_KU_DSS.sign. 
declare axiom FL_KU_DSS_verify_ll : islossless FL_KU_DSS.verify. 

declare module A <: Adv_EFCMA_RO{-FL_KU_DSS, -ERO, -O_CMA, -O_METCR, -R_EFCMARO_CRRO, -R_EFCMARO_METCRRO, -Wrapped_Oracle, -RepO, -DSS_FL_EFRMA.O_RMA_Default, -R_EFCMARO_IEFRMA, -QC_A, -Lazy.LRO, -ReproGame, -R_EFRMA_IEFRMA}.

declare axiom A_forge_ll (SO <: SOracle_CMA{-A}) (RO <: POracle{-A}) : 
  islossless SO.sign => islossless RO.o => islossless A(SO, RO).forge.

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

local hoare R_Repro_EFCMARORepro_Queries :
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
+ conseq (: Wrapped_Oracle.ch = 0 /\ RepO.ctr = 0 /\ RepO.se
            ==>
            Wrapped_Oracle.ch = QC_A.cH + QC_A.cS /\ RepO.ctr = QC_A.cS /\ RepO.se)
         (: true ==>  QC_A.cS <= qS /\ QC_A.cH <= qH) => //.
  - by apply: (A_forge_queries (<: R_Repro_EFCMARORepro(Wrapped_Oracle(ERO), RepO(Wrapped_Oracle(ERO))).O_R_Repro_EFCMARORepro) (Wrapped_Oracle(ERO))).
  proc.
  call (: Wrapped_Oracle.ch = QC_A.cH + QC_A.cS /\ RepO.ctr = QC_A.cS /\ RepO.se).
  - proc; inline *.
    by wp; skip => /#.
  - proc; inline *.
    wp; call (: true); wp => /=.
    case RepO.b.
    * rcondt 7; 1: by auto.
      wp.
      rnd; rnd.
      wp; skip => /> &1 seT bT rcom _ cm _.
      split => [/# |].
      by rewrite p_max_rcom.
    rcondf 7; 1: by auto.
    rnd.
    wp; skip => /> &1 se b rcom _.
    split => [/# |].
    by rewrite p_max_rcom.
  by wp; skip.
do 2! (call(: true) => //).
by skip => /#.
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
wp => /=. call (: true); wp => /=.
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
wp; call(: true); wp => /=.
skip => /> cmap msig qs' plist comps' qs eqsz ninqsp ver ltqS_szqs verT ninqs.
pose ifte := if _ then _ else _; move=> eqnone.
split; 1: by rewrite -eqsz; smt(rng_qS).
apply: ninqsp; rewrite negb_exists /= => m; rewrite negb_exists /= => rco.
move/iffRL /contra: (assoc_none comps' ifte) => /= /(_ eqnone).
by rewrite negb_exists /= => /(_ (rco, m)).
qed.

lemma ALKUDSS_EFCMARO_CRRO_IEFRMA &m :
  Pr[EF_CMA_RO(AL_KU_DSS(FL_KU_DSS), A, O_CMA, MCO).main() @ &m : res]
  <=
  Pr[CR_RO(R_EFCMARO_CRRO(FL_KU_DSS, A), MCO).main() @ &m : res]
  +
  Pr[I_EF_RMA(FL_KU_DSS, R_EFCMARO_IEFRMA(A), O_RMA_Default).main() @ &m : res]
  +
  qS%r * (qS + qH + 1)%r * mu1 drco witness.
proof.
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
rewrite addrC; apply ler_add.
+ by rewrite EFRMAROCCReproSample_Query EFRMAROCCReproQuery_IEFRMA.
apply (ler_trans `| Pr[ReproGame(ERO, R_Repro_EFCMARORepro).main(false) @ &m : res] -
                    Pr[ReproGame(ERO, R_Repro_EFCMARORepro).main(true) @ &m : res] |).
+ by rewrite EFCMARORepro_ReproGame.
apply (rom_reprogramming R_Repro_EFCMARORepro _ _ _ _ &m R_Repro_EFCMARORepro_Queries).
+ by move: rng_qS => [->].
by smt(rng_qS ge0_qH).
qed.


lemma ALKUDSS_EFCMARO_METCRRO_IEFRMA &m :
  Pr[EF_CMA_RO(AL_KU_DSS(FL_KU_DSS), A, O_CMA, MCO).main() @ &m : res]
  <=
  Pr[M_ETCR_RO(R_EFCMARO_METCRRO(FL_KU_DSS, A), O_METCR, MCO).main() @ &m : res]
  +
  Pr[I_EF_RMA(FL_KU_DSS, R_EFCMARO_IEFRMA(A), O_RMA_Default).main() @ &m : res]
  +
  qS%r * (qS + qH + 1)%r * mu1 drco witness.
proof.
have ->:
  Pr[EF_CMA_RO(AL_KU_DSS(FL_KU_DSS), A, O_CMA, MCO).main() @ &m : res]
  =
  Pr[EF_CMA_RO_CC.main() @ &m : res].
+ by byequiv Equiv_EFCMARO_EFCMAROCC.
rewrite Pr[mu_split EF_CMA_RO_CC.coll] -addrA ler_add 1:EFCMAROCC_METCRRO.
rewrite EFCMAROCC_EFCMAROCCNoRepro -ger0_norm 1:Pr[mu_ge0] // -subr0.
rewrite -(subrr Pr[EF_CMA_RO_CC_ReproSample.main() @ &m : res /\ !EF_CMA_RO_CC_ReproSample.coll]).
rewrite opprB (addrC Pr[EF_CMA_RO_CC_ReproSample.main() @ &m : res /\ !EF_CMA_RO_CC_ReproSample.coll]) addrA.
apply (ler_trans (`|  Pr[EF_CMA_RO_CC_NoRepro.main() @ &m : res /\ !EF_CMA_RO_CC_NoRepro.coll]
                    - Pr[EF_CMA_RO_CC_ReproSample.main() @ &m : res /\ !EF_CMA_RO_CC_ReproSample.coll] |
                  + Pr[EF_CMA_RO_CC_ReproSample.main() @ &m : res /\ !EF_CMA_RO_CC_ReproSample.coll])).
+ by rewrite -{4}(ger0_norm Pr[EF_CMA_RO_CC_ReproSample.main() @ &m : res /\ !EF_CMA_RO_CC_ReproSample.coll]) 1:Pr[mu_ge0] 2:&(ler_norm_add).
rewrite addrC; apply ler_add.
+ by rewrite EFRMAROCCReproSample_Query EFRMAROCCReproQuery_IEFRMA.
apply (ler_trans `| Pr[ReproGame(ERO, R_Repro_EFCMARORepro).main(false) @ &m : res] -
                    Pr[ReproGame(ERO, R_Repro_EFCMARORepro).main(true) @ &m : res] |).
+ by rewrite EFCMARORepro_ReproGame.
apply (rom_reprogramming R_Repro_EFCMARORepro _ _ _ _ &m R_Repro_EFCMARORepro_Queries).
+ by move: rng_qS => [->].
by smt(rng_qS ge0_qH).
qed.


declare op opsign : sk_fl_t -> msg_fl_t -> sig_fl_t * sk_fl_t.

declare axiom FL_KU_DSS_sign_fun (sk : sk_fl_t) (cm : msg_fl_t) :
  hoare[FL_KU_DSS.sign: arg = (sk, cm) ==> res = opsign sk cm].

local lemma FL_KU_DSS_sign_pfun (sk : sk_fl_t) (cm : msg_fl_t) :
  phoare[FL_KU_DSS.sign: arg = (sk, cm) ==> res = opsign sk cm] = 1%r.
proof. by conseq FL_KU_DSS_sign_ll (FL_KU_DSS_sign_fun sk cm). qed.

declare axiom FL_KU_DSS_keygen_stateless:
  equiv[FL_KU_DSS.keygen ~ FL_KU_DSS.keygen: true ==> ={res}].
  
declare axiom FL_KU_DSS_verify_stateless:
  equiv[FL_KU_DSS.verify ~ FL_KU_DSS.verify: ={arg} ==> ={res}].

lemma ALKUDSS_EFCMARO_CRRO_EFRMA &m :
  Pr[EF_CMA_RO(AL_KU_DSS(FL_KU_DSS), A, O_CMA, MCO).main() @ &m : res]
  <=
  Pr[CR_RO(R_EFCMARO_CRRO(FL_KU_DSS, A), MCO).main() @ &m : res]
  +
  Pr[EF_RMA(FL_KU_DSS, R_EFRMA_IEFRMA(R_EFCMARO_IEFRMA(A))).main() @ &m : res]
  +
  qS%r * (qS + qH + 1)%r * mu1 drco witness
  +
  n%r * mu1 dmsg_fl witness.
proof.
move: (I_EFRMA_le_EF_RMA (R_EFCMARO_IEFRMA(A)) _).
+ move=> SO SOs_ll.
  proc; inline *.
  wp.
  call (A_forge_ll (<: R_EFCMARO_IEFRMA(A, SO).O_CMA_R_EFCMARO_IEFRMA) (Wrapped_Oracle(MCO))).
  - proc; inline *.
    wp; call (SOs_ll); rnd; skip => />.
    by apply drco_ll.
  - proc; inline *.
    by wp; skip.
  wp. 
  while (true) (size w).
  - move=> z.
    wp; rnd; wp; skip => /> &1 neqw.
    split; 2: apply dmsg_fl_ll.
    by move: neqw; case (w{1}) => // rcom rcoml _ /= /#.
  by wp; skip => />; smt(size_ge0 size_eq0).
move=> /(_ FL_KU_DSS FL_KU_DSS_sign_ll FL_KU_DSS_verify_ll).
move=> /(_ opsign FL_KU_DSS_sign_fun FL_KU_DSS_keygen_stateless FL_KU_DSS_verify_stateless).
move=> /(_ (mu1 dmsg_fl witness) &m _).
+ by move=> cm; rewrite ler_eqVlt; left; rewrite &(dmsg_fl_uni) dmsg_fl_fu.
by move: (ALKUDSS_EFCMARO_CRRO_IEFRMA &m) => /#.
qed.

lemma ALKUDSS_EFCMARO_METCRRO_EFRMA &m :
  Pr[EF_CMA_RO(AL_KU_DSS(FL_KU_DSS), A, O_CMA, MCO).main() @ &m : res]
  <=
  Pr[M_ETCR_RO(R_EFCMARO_METCRRO(FL_KU_DSS, A), O_METCR, MCO).main() @ &m : res]
  +
  Pr[EF_RMA(FL_KU_DSS, R_EFRMA_IEFRMA(R_EFCMARO_IEFRMA(A))).main() @ &m : res]
  +
  qS%r * (qS + qH + 1)%r * mu1 drco witness
  +
  n%r * mu1 dmsg_fl witness.
proof.
move: (I_EFRMA_le_EF_RMA (R_EFCMARO_IEFRMA(A)) _).
+ move=> SO SOs_ll.
  proc; inline *.
  wp.
  call (A_forge_ll (<: R_EFCMARO_IEFRMA(A, SO).O_CMA_R_EFCMARO_IEFRMA) (Wrapped_Oracle(MCO))).
  - proc; inline *.
    wp; call (SOs_ll); rnd; skip => />.
    by apply drco_ll.
  - proc; inline *.
    by wp; skip.
  wp. 
  while (true) (size w).
  - move=> z.
    wp; rnd; wp; skip => /> &1 neqw.
    split; 2: apply dmsg_fl_ll.
    by move: neqw; case (w{1}) => // rcom rcoml _ /= /#.
  by wp; skip => />; smt(size_ge0 size_eq0).
move=> /(_ FL_KU_DSS FL_KU_DSS_sign_ll FL_KU_DSS_verify_ll).
move=> /(_ opsign FL_KU_DSS_sign_fun FL_KU_DSS_keygen_stateless FL_KU_DSS_verify_stateless).
move=> /(_ (mu1 dmsg_fl witness) &m _).
+ by move=> cm; rewrite ler_eqVlt; left; rewrite &(dmsg_fl_uni) dmsg_fl_fu.
by move: (ALKUDSS_EFCMARO_METCRRO_IEFRMA &m) => /#.
qed.

end section Proofs_EFCMA_RO_ALKUDSS.

end WithSampling.


theory WithPRF.

clone WithSampling as WS.

type ms_t.

type id_t.
(*
clone import FinType as ID with
  type t <- id_t.
*)

type sk_al_t = ms_t * sk_fl_t.


op [lossless] dms : ms_t distr.


(* --- Operators --- *)
op mkg : ms_t -> id_t -> rco_t. 

clone import KeyedHashFunctions as MKG with
  type key_t <= ms_t, 
  type in_t <= id_t,
  type out_t <= rco_t,   
    
    op f <= mkg,
    
    op dkey <= dms,
    op doutm <= fun _ => drco
    
    proof dkey_ll by exact: dms_ll
    proof doutm_ll by smt(drco_ll).

op extr_id : sk_fl_t -> id_t.

clone import DigitalSignatures as DSS_AL with
  type pk_t <- pk_al_t,
  type sk_t <- sk_al_t,
  type msg_t <- msg_al_t,
  type sig_t <- sig_al_t.


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
module type Adv_EFCMA_RO(SO : SOracle_CMA, RO : POracle) = {
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
module EF_CMA_RO(S : DSS_AL.KeyUpdating.Scheme, A : Adv_EFCMA_RO, SO : Oracle_CMA, RO : Oracle) = {
  proc main() = {
    var pk : pk_al_t;
    var sk : sk_al_t;
    var m : msg_al_t;
    var sig : sig_al_t;
    var is_valid, is_fresh : bool;
    
    (* Initialize (hash) random oracle *)
    RO.init();
    
    (* Generate a key pair using the considered signature scheme *)
    (pk, sk) <@ S.keygen();

    (* Initialize the signing oracle with the generated secret key *)
    SO(S).init(sk);

    (*
      Ask the adversary to forge a signature for any message (and provide both the
      message and the signature) given the public key pk and access to a signing oracle 
      that it can query an unlimited number of times
    *)
    (m, sig) <@ A(SO(S), RO).forge(pk);

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

(* --- Scheme --- *)
module AL_KU_DSS(FL_KU_DSS : DSS_FL.KeyUpdating.Scheme) : DSS_AL.KeyUpdating.Scheme = {
  proc keygen() : pk_al_t * sk_al_t = {
    var ms : ms_t;
    var pk : pk_al_t;
    var skfl : sk_fl_t;
    var sk : sk_al_t;
    
    ms <$ dms;
    
    (pk, skfl) <@ FL_KU_DSS.keygen();
    
    sk <- (ms, skfl);
    
    return (pk, sk);
  }
  
  proc sign(sk : sk_al_t, m : msg_al_t) : sig_al_t * sk_al_t = {
    var ms : ms_t;
    var id : id_t;
    var skfl : sk_fl_t;
    var rco : rco_t;
    var cm : msg_fl_t;
    var sigfl : sig_fl_t;
    var sig : sig_al_t;
    
    ms <- sk.`1;
    skfl <- sk.`2;
    
    id <- extr_id skfl;
    
    rco <- mkg ms id;
    
    cm <@ MCO.o((rco, m));
    
    (sigfl, skfl) <@ FL_KU_DSS.sign(skfl, cm);
    
    sig <- (rco, sigfl);
    sk <- (ms, skfl);
    
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

(* -- Reduction Adversaries -- *)
module (R_PRF_EFCMARO (FL_KU_DSS : DSS_FL.KeyUpdating.Scheme, A : Adv_EFCMA_RO) : Adv_PRF) (O : Oracle_PRF) = {
  module O_CMA_R_PRF_EFCMARO : SOracle_CMA = {
    var skfl : sk_fl_t
    var qs : msg_al_t list
    
    proc init(skfl_init : sk_fl_t) : unit = {
      skfl <- skfl_init;
      qs <- [];
    }

    proc sign(m : msg_al_t) : sig_al_t = {
      var id : id_t;
      var rco : rco_t;
      var sigfl : sig_fl_t;
      var sig : sig_al_t;
      var cm : msg_fl_t;
      
      id <- extr_id skfl;
      
      rco <@ O.query(id);
      
      cm <@ MCO.o((rco, m));
      
      (sigfl, skfl) <@ FL_KU_DSS.sign(skfl, cm);
      
      sig <- (rco, sigfl);
      
      qs <- rcons qs m;
            
      return sig;
    }
    
    proc fresh(m : msg_al_t) : bool = {
      return ! m \in qs; 
    }
  }
  
  proc distinguish() : bool = {
    var pk : pk_al_t;
    var sk : sk_al_t;
    var skfl : sk_fl_t;
    var m' : msg_al_t;
    var sig' : sig_al_t;
    var is_valid, is_fresh : bool;
    
    MCO.init();
    
    (pk, skfl) <@ FL_KU_DSS.keygen();
    
    O_CMA_R_PRF_EFCMARO.init(skfl);
    
    (m', sig') <@ A(O_CMA_R_PRF_EFCMARO, MCO).forge(pk);
    
    is_valid <@ AL_KU_DSS(FL_KU_DSS).verify(pk, m', sig');
    
    is_fresh <@ O_CMA_R_PRF_EFCMARO.fresh(m');
    
    return is_valid /\ is_fresh;  
  }
}.

section Proofs_EFCMA_RO_ALKUDSS.

declare module FL_KU_DSS <: DSS_FL.KeyUpdating.Scheme{-ERO, -O_CMA, -O_METCR, -WS.R_EFCMARO_CRRO, -WS.R_EFCMARO_METCRRO, -Wrapped_Oracle, -RepO, -O_RMA_Default, -WS.R_EFCMARO_IEFRMA, -WS.QC_A, -Lazy.LRO, -ReproGame, -R_EFRMA_IEFRMA, -R_PRF_EFCMARO, -O_PRF_Default, -WS.O_CMA}.

declare axiom FL_KU_DSS_sign_ll : islossless FL_KU_DSS.sign. 
declare axiom FL_KU_DSS_verify_ll : islossless FL_KU_DSS.verify. 

declare op skupd : sk_fl_t -> sk_fl_t.
declare op opsign : sk_fl_t -> msg_fl_t -> sig_fl_t * sk_fl_t.

declare axiom FL_KU_DSS_sign_fun (sk : sk_fl_t) (cm : msg_fl_t) :
  hoare[FL_KU_DSS.sign: arg = (sk, cm) ==> res = opsign sk cm].

local lemma FL_KU_DSS_sign_pfun (sk : sk_fl_t) (cm : msg_fl_t) :
  phoare[FL_KU_DSS.sign: arg = (sk, cm) ==> res = opsign sk cm] = 1%r.
proof. by conseq FL_KU_DSS_sign_ll (FL_KU_DSS_sign_fun sk cm). qed.

declare axiom FL_KU_DSS_sign_skupd (sk : sk_fl_t) :
  hoare[FL_KU_DSS.sign: arg.`1 = sk ==> res.`2 = skupd sk].

  
(*
declare axiom FL_KU_DSS_keygen_id0:
  hoare[FL_KU_DSS.keygen : true ==> extr_id res.`2 = nth witness ID.enum 0].
*)
(*
declare axiom opsign_iter_id (sk : sk_fl_t) (cm : msg_fl_t) :
  let idx = index (extr_id sk) ID.enum in 
       idx < ID.card - 1
    => extr_id (opsign sk cm).`2 = nth witness ID.enum idx.
*)

declare axiom skupd_fold_id (n m : int) (sk : sk_fl_t) :
     n < m <= qS
  => extr_id (fold skupd sk n) <> extr_id (fold skupd sk m).
    
declare axiom FL_KU_DSS_keygen_stateless:
  equiv[FL_KU_DSS.keygen ~ FL_KU_DSS.keygen: true ==> ={res}].
  
declare axiom FL_KU_DSS_verify_stateless:
  equiv[FL_KU_DSS.verify ~ FL_KU_DSS.verify: ={arg} ==> ={res}].


declare module A <: Adv_EFCMA_RO{-FL_KU_DSS, -ERO, -O_CMA, -O_METCR, -WS.R_EFCMARO_CRRO, -WS.R_EFCMARO_METCRRO, -Wrapped_Oracle, -RepO, -DSS_FL_EFRMA.O_RMA_Default, -WS.R_EFCMARO_IEFRMA, -WS.QC_A, -Lazy.LRO, -ReproGame, -R_EFRMA_IEFRMA, -R_PRF_EFCMARO, -O_PRF_Default, -WS.O_CMA}.

declare axiom A_forge_ll (SO <: SOracle_CMA{-A}) (RO <: POracle{-A}) : 
  islossless SO.sign => islossless RO.o => islossless A(SO, RO).forge.

declare axiom A_forge_queries (SO <: SOracle_CMA{-A, -WS.QC_A}) (RO <: POracle{-A, -WS.QC_A}):
  hoare[WS.QC_A(A, SO, RO).forge : true ==> WS.QC_A.cS <= qS /\ WS.QC_A.cH <= qH].

lemma take_mem (s : 'a list) (x : 'a) :
  ! x \in take (index x s) s.
proof.
elim: s => // x' s ih /=.
case (x' = x) => [-> | neqxxp].
by rewrite index_cons /=.
rewrite (: !index x (x' :: s) <= 0).
rewrite ler_eqVlt negb_or; split; smt(index_cons index_ge0).
simplify.
rewrite (eq_sym x) neqxxp /=.
rewrite index_cons (eq_sym x) neqxxp /= ih //.
qed.

local lemma test &m :
  `| Pr[EF_CMA_RO(AL_KU_DSS(FL_KU_DSS), A, O_CMA, MCO).main() @ &m : res] -
     Pr[WS.EF_CMA_RO(WS.AL_KU_DSS(FL_KU_DSS), A, WS.O_CMA, MCO).main() @ &m : res] |
  =
  `| Pr[PRF(R_PRF_EFCMARO(FL_KU_DSS, A), O_PRF_Default).main(false) @ &m : res] -
     Pr[PRF(R_PRF_EFCMARO(FL_KU_DSS, A), O_PRF_Default).main(true) @ &m : res] |.
proof.
do 2! congr; last congr.
+ byequiv => //.
  proc; inline{2} 2.
  wp => /=.
  call (: ={qs}(O_CMA, R_PRF_EFCMARO.O_CMA_R_PRF_EFCMARO)).
  - by skip.
  call (: ={glob FL_KU_DSS, ERO.m}).
  - by inline *; call (: true); wp; skip.
  call (:   ={glob FL_KU_DSS, ERO.m}
         /\ ={qs}(O_CMA, R_PRF_EFCMARO.O_CMA_R_PRF_EFCMARO)
         /\  O_CMA.sk{1}.`1 = O_PRF_Default.k{2}
         /\ O_CMA.sk{1}.`2 = R_PRF_EFCMARO.O_CMA_R_PRF_EFCMARO.skfl{2}
         /\ ! O_PRF_Default.b{2}).
  - by proc; skip.
  - proc; inline *. 
    wp.
    rcondf{2} 3; 1: by auto.
    call (: true).
    by wp; skip.
  inline *.
  wp; call (: true) => /=.
  swap{1} 4 -1.
  while (={ERO.m, w}); 1: by auto.
  wp.
  rnd.
  by wp; skip.
byequiv => //.
proc; inline{2} 2.
wp => /=.
call (: ={qs}(WS.O_CMA, R_PRF_EFCMARO.O_CMA_R_PRF_EFCMARO)).
- by skip.
call (: ={glob FL_KU_DSS, ERO.m}).
- by inline *; call (: true); wp; skip.
(*  
call (:   ={glob FL_KU_DSS, ERO.m}
       /\ ={qs}(WS.O_CMA, R_PRF_EFCMARO.O_CMA_R_PRF_EFCMARO)
       /\ WS.O_CMA.sk{1} = R_PRF_EFCMARO.O_CMA_R_PRF_EFCMARO.skfl{2}
       /\ O_PRF_Default.b{2}
       /\ (forall (id : id_t), id \in O_PRF_Default.m{2} <=>
             id \in take (index (extr_id R_PRF_EFCMARO.O_CMA_R_PRF_EFCMARO.skfl{2}) ID.enum) ID.enum)).
*)
seq 3 4 : (   ={glob FL_KU_DSS, ERO.m, pk}
           /\ ={qs}(WS.O_CMA, R_PRF_EFCMARO.O_CMA_R_PRF_EFCMARO)
           /\ WS.O_CMA.sk{1} = R_PRF_EFCMARO.O_CMA_R_PRF_EFCMARO.skfl{2}
           /\ O_PRF_Default.b{2}
           /\ O_PRF_Default.m{2} = empty
           /\ WS.O_CMA.qs{1} = []
           /\ R_PRF_EFCMARO.O_CMA_R_PRF_EFCMARO.qs{2} = []) => />.
+ inline *. 
  wp; call (: true).
  while (={w, ERO.m}); 1: by auto.
  wp. 
  rnd{2}.
  by wp; skip.
call (:   ={glob FL_KU_DSS, ERO.m}
       /\ ={qs}(WS.O_CMA, R_PRF_EFCMARO.O_CMA_R_PRF_EFCMARO)
       /\ WS.O_CMA.sk{1} = R_PRF_EFCMARO.O_CMA_R_PRF_EFCMARO.skfl{2}
       /\ O_PRF_Default.b{2}
       /\ ).
- by proc; skip.
- proc; inline *. 
  wp.
  rcondt{2} 3; 1: by auto.
  call (:   ={glob FL_KU_DSS} ==> ={glob FL_KU_DSS, res}
         /\ extr_id res{2}.`2 = ).
  wp => /=.
  rcondt{2} 3.
  - move=> &1.
    wp; skip => /> &2 bT /(_ (extr_id WS.O_CMA.sk{1})) /iffLR /contra /(_ _) //.
    by rewrite take_mem.
  wp.
  rnd.
  wp; skip => />.
  progress.
  search "_.[_]".
  by rewrite get_set_sameE oget_some.
  rewrite get_set_sameE oget_some //.
  search dom.
  admit. admit.
inline *.
wp. 
call (:   ={glob FL_KU_DSS} 
       ==> 
          ={glob FL_KU_DSS, res} 
       /\ extr_id res{2}.`2 = nth witness ID.enum 0).
conseq (: ={glob FL_KU_DSS} ==> ={glob FL_KU_DSS, res})
       _
       FL_KU_DSS_keygen_id0.
proc true => //.
while (={ERO.m, w}); 1: by auto.
wp.
rnd{2}.
wp; skip => />; smt(mem_empty index_nth).
qed.

end WithPRF.

