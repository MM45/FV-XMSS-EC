require import AllCore List Distr SmtMap.
require (*--*) DigitalSignatures PROM.

(* -- Types -- *)
(* Types for to-be-signed artifacts ('messages') and signatures, respectively *)
type msg_t.
type sig_t.

(* Types for public/verification keys and secret/private/signing keys, respectively *)
type pk_t.
type sk_t.

(* (Proper) distribution over type of to-be-signed artifacts ('messages') *)
op [lossless] dmsg : msg_t distr.

(* Number of messages the adversary obtains signatures for in EF-RMA game *)
const n_efrma : { int | 0 <= n_efrma } as ge0_nefrma.

(** The non-interactive, classical definition **)
clone DigitalSignatures as ClassDS with
  type msg_t <= msg_t,
  type sig_t <= sig_t,
  type pk_t  <= pk_t,
  type sk_t  <= sk_t.
import ClassDS.KeyUpdating.

clone import EFRMA as Class_EFRMA with
  op dmsg    <= dmsg,
  op n_efrma <= n_efrma,
  lemma dmsg_ll <- dmsg_ll,
  lemma ge0_nefrma <- ge0_nefrma
proof *.

module R_EFRMA_IEFRMA (A : Adv_I_EFRMA) : Adv_EFRMA = {
  module O_R : SOracle_RMA = {
    var q : int
    var msigl : (msg_t * sig_t) list
    
    proc init(msigl_init : (msg_t * sig_t) list) = {
      q <- 0;
      msigl <- msigl_init;
    }
    
    proc sign() : msg_t * sig_t = {
      var q_old : int;

      q_old <- q;
      q <- q + 1;
      
      return nth witness msigl q_old;
    }
    
    proc fresh(m : msg_t) : bool = {
     return ! m \in unzip1 (take q msigl); 
    }
    
    proc nr_queries() : int = {
      return q;
    }
  }
  
  proc forge(pk : pk_t, msigl : (msg_t * sig_t) list) : msg_t * sig_t = {
    var m' : msg_t;
    var sig' : sig_t;
    
    O_R.init(msigl);
    
    (m', sig') <@ A(O_R).forge(pk);

    return (m', sig');
  }
}.

section.
declare module A <: Adv_I_EFRMA {-R_EFRMA_IEFRMA, -O_RMA_Default, -EF_RMA}.
declare axiom A_ll (O <: SOracle_RMA {-A}):
     islossless O.sign
  => islossless A(O).forge.

declare module S <: Scheme {-A, -R_EFRMA_IEFRMA, -O_RMA_Default, -EF_RMA}.
declare axiom Ssign_ll: islossless S.sign.
declare axiom Sverify_ll: islossless S.verify.

declare op opsign : sk_t -> msg_t -> sig_t * sk_t.
declare axiom S_fun sk m:
  hoare[ S.sign: arg = (sk, m) ==> res = opsign sk m].

local lemma S_pfun sk m:
  phoare[ S.sign: arg = (sk, m) ==> res = opsign sk m] =1%r.
proof. by conseq Ssign_ll (S_fun sk m). qed.

declare axiom Skeygen_stateless:
  equiv[ S.keygen ~ S.keygen: true ==> ={res} ].
declare axiom Sverify_stateless:
  equiv[ S.verify ~ S.verify: ={arg} ==> ={res} ].

(* Pseudo-Interactive EF-RMA oracles *)
(** TODO: This is overengineered—pre-sample all messages, then
          carefully craft the invariant on secret keys **)
local module (O_RMA_Lazy : Oracle_RMA) (S : Scheme) = {
  var sk    : sk_t

  var qs    : msg_t list
  var bad   : bool

  (* Initialize secret/signing key and oracle query list qs *)
  proc init(sk_init : sk_t) : unit = {
    qs <- [];
    bad <- false;
    sk <- sk_init;
  }

  (* 
    Sign given message m using the considered signature scheme with the
    secret/signing key sk and append m to the list of oracle queries qs
  *)
  proc sign() : msg_t * sig_t = {
    var m, sig;

    if (size qs < n_efrma) {
      m <$ dmsg;
      (sig, sk) <- opsign sk m;
      qs <- rcons qs m;
    } else {
      bad <- true;
      (m, sig) <- witness;
    }

    return (m, sig);
  }
  
  (* 
    Check whether given message m is fresh, i.e., whether m is not contained in
    the list of oracle queries qs 
  *)
  proc fresh(m : msg_t) : bool = {
    return ! m \in qs;
  }

  (* Get the number of oracle queries, i.e., the size of the oracle query list qs *)
  proc nr_queries() : int = {
    return if bad then n_efrma + 1 else size qs;
  }
}.

local clone import PROM.FullRO with
  type in_t    <- unit,
  type out_t   <- msg_t,
  op   dout _  <- dmsg,
  type d_in_t  <- unit,
  type d_out_t <- bool.

local module (O_RMA_Hybrid (O : RO) : Oracle_RMA) (S : Scheme) = {
  var j     : int

  var msigl : (msg_t * sig_t) list
  var sk    : sk_t

  var qs    : msg_t list

  (* Initialize secret/signing key and oracle query list qs *)
  proc init(sk_init : sk_t) : unit = {
    var m, sig;

    O.init();
    msigl <- [];
    qs <- [];
    sk <- sk_init;

    while (size msigl < j) {
      m <$ dmsg;
      (sig, sk) <- opsign sk m;
      msigl <- rcons msigl (m, sig);
    }
    O.sample();
  }

  (* 
    Sign given message m using the considered signature scheme with the
    secret/signing key sk and append m to the list of oracle queries qs
  *)
  proc sign() : msg_t * sig_t = {
    var m : msg_t;
    var sig: sig_t;
    
    (m, sig) <- witness;

    if (size qs < n_efrma) {
      if (size qs < j) {
        (m, sig) <- nth witness msigl (size qs);
      }
      if (size qs = j) {
        m <@ O.get();
        (sig, sk) <- opsign sk m;
        msigl <- rcons msigl (m, sig);
      }
      if (j < size qs) {
        m <$ dmsg;
        (sig, sk) <- opsign sk m;
        msigl <- rcons msigl (m, sig);
      }
      qs <- rcons qs m;
    }

    return (m, sig);
  }
  
  (* 
    Check whether given message m is fresh, i.e., whether m is not contained in
    the list of oracle queries qs 
  *)
  proc fresh(m : msg_t) : bool = {
    return ! m \in qs;
  }

  (* Get the number of oracle queries, i.e., the size of the oracle query list qs *)
  proc nr_queries() : int = {
    return size qs;
  }
}.

local module (O_RMA_Eager : Oracle_RMA) (S : Scheme) = {
  var msigl : (msg_t * sig_t) list
  var sk    : sk_t

  var qs    : msg_t list

  (* Initialize secret/signing key and oracle query list qs *)
  proc init(sk_init : sk_t) : unit = {
    var m, sig;

    msigl <- [];
    qs <- [];
    sk <- sk_init;

    while (size msigl < n_efrma) {
      m <$ dmsg;
      (sig, sk) <- opsign sk m;
      msigl <- rcons msigl (m, sig);
    }
  }

  (* 
    Sign given message m using the considered signature scheme with the
    secret/signing key sk and append m to the list of oracle queries qs
  *)
  proc sign() : msg_t * sig_t = {
    var m, sig;

    (m, sig) <- nth witness msigl (size qs);
    if (size qs < n_efrma) {
      qs <- rcons qs m;
    }
    return (m, sig);
  }
  
  (* 
    Check whether given message m is fresh, i.e., whether m is not contained in
    the list of oracle queries qs 
  *)
  proc fresh(m : msg_t) : bool = {
    return ! m \in qs;
  }

  (* Get the number of oracle queries, i.e., the size of the oracle query list qs *)
  proc nr_queries() : int = {
    return size qs;
  }
}.

local equiv left_eq:
  I_EF_RMA(S, A, O_RMA_Default).main ~ I_EF_RMA(S, A, O_RMA_Lazy).main:
    ={glob A} ==> ={res}.
proof.
proc.
conseq (: ((nrqs{1} <= n_efrma) <=> (nrqs{2} <= n_efrma))
       /\ (!O_RMA_Lazy.bad <=> nrqs <= n_efrma){2}
       /\ (   !O_RMA_Lazy.bad{2}
           => ={is_valid, is_fresh})).
+ by move=> /> + + nrqsL + + nrqsR; case: (nrqsL <= n_efrma)=> />.
seq  3  3:
  (   ((size ClassDS.O_Base_Default.qs <= n_efrma){1} <=> !O_RMA_Lazy.bad{2})
   /\ (   !O_RMA_Lazy.bad{2}
       => (   ={pk, m', sig'}
           /\ ={qs}(ClassDS.O_Base_Default, O_RMA_Lazy)))); first last.
+ case: (O_RMA_Lazy.bad{2}).
  + inline *; auto.
    call {1} Sverify_ll.
    call {2} Sverify_ll.
    by auto=> /#.
  by inline *; auto; call Sverify_stateless; auto=> /#.
call (: O_RMA_Lazy.bad
      , ={qs}(ClassDS.O_Base_Default, O_RMA_Lazy)
     /\ ={sk}(O_RMA_Default, O_RMA_Lazy)
     /\ (size O_RMA_Lazy.qs <= n_efrma){2}
      , (n_efrma < size ClassDS.O_Base_Default.qs){1}
     /\ (size O_RMA_Lazy.qs = n_efrma){2}).
+ exact: A_ll.
+ proc.
  case: (size O_RMA_Lazy.qs{2} = n_efrma).
  + rcondf {2} 1; 1:by auto; smt().
    wp; ecall {1} (S_pfun O_RMA_Default.sk{1} m{1}).
    by auto=> />; smt(size_rcons).
  rcondt {2} 1; 1:by auto; smt().
  inline *.
  wp; ecall {1} (S_pfun O_RMA_Default.sk{1} m{1}).
  auto=> /> &2 notBad ge0_sqs sqs_neq_n m _.
  by rewrite size_rcons /#.
+ move=> &2 bad; proc; auto; call Ssign_ll; auto.
  by rewrite dmsg_ll; smt(size_rcons).
+ by move=> &1; proc; rcondf 1; auto=> /#.
inline *; wp; call Skeygen_stateless; auto=> />.
split; 1:by exact: ge0_nefrma.
move=> _ [] sigL skL [] sigR skR gAL qsL sk0L gAR badR qsR sk0R.
by case: badR=> /> /#.
qed.

local module I_EF_RMA0 (S : Scheme) (A : Adv_I_EFRMA) (O : Oracle_RMA) = {
  var bad : bool

  proc main() : bool = {
    var pk : pk_t;
    var sk : sk_t;
    var m', m : msg_t;
    var sig, sig' : sig_t;
    var msig : msg_t * sig_t;
    var q;
    var is_valid, is_fresh : bool;

    bad <- false;

    (* Generate a key pair using the considered signature scheme *)
    (pk, sk) <@ S.keygen();

    (* Initialize oracle *)
    O(S).init(sk);
    
    (* 
      Ask the adversary to forge a signature for any message (and provide both the
      message and signature) given the public key pk and a list of (message, signature) 
      pairs msigl
    *)
    (m', sig') <@ A(O(S)).forge(pk);

    (* 
      Verify (w.r.t. message m') the signature sig' provided by the adversary 
      using the verification algorithm of the considered signature scheme 
    *)
    is_valid <@ S.verify(pk, m', sig');

    q <@ O(S).nr_queries();
    while (0 < n_efrma - q) {
      (m, sig) <@ O(S).sign();
      bad <- bad \/ m = m';
      q <- q + 1;
    }

    (* Check that message was not one of the messages sampled by the signing oracle. *) 
    is_fresh <@ O(S).fresh(m');

    return is_valid /\ is_fresh; 
  }
}.

local equiv left_mid:
  I_EF_RMA(S, A, O_RMA_Lazy).main ~ I_EF_RMA0(S, A, O_RMA_Lazy).main:
    ={glob A} ==> !I_EF_RMA0.bad{2} => res{1} => res{2}.
proof.
proc.
conseq (: ={is_valid} /\ (!I_EF_RMA0.bad{2} => ={is_fresh}))=> />.
+ by move=> freshL nrqsL badR freshR validR + Hbad - /(_ Hbad) ->.
inline {1} 6; wp.
inline {1} 5; inline {2} 8; wp.
seq  4  5:
  (   ={glob O_RMA_Lazy, is_valid, m', sig'}
   /\ !I_EF_RMA0.bad{2}).
+ call Sverify_stateless=> //.
  call (: ={glob O_RMA_Lazy}).
  + proc; inline *; if=> //; 2:by auto.
    by auto.
  by inline *; wp; call Skeygen_stateless; auto.
inline {2} 1; sp.
case: (n_efrma <= q{2}).
+ by rcondf {2} 1; by auto=> //#.
while {2}
  (   ={m'}
   /\ (q = size O_RMA_Lazy.qs){2}
   /\ (   !I_EF_RMA0.bad{2}
       => (m'{1} \in O_RMA_Lazy.qs{1} <=> m'{2} \in O_RMA_Lazy.qs{2})))
  (n_efrma - q{2}).
+ move=> &0 z; inline *.
  rcondt 1; 1:by auto=> /#.
  auto=> /> &1 nBad_inv n_gt_s.
  rewrite dmsg_ll=> //= m _ _.
  by rewrite size_rcons mem_rcons //#.
by auto=> /#.
qed.

local equiv hybrid_left:
  I_EF_RMA0(S, A, O_RMA_Lazy).main ~ I_EF_RMA0(S, A, O_RMA_Hybrid(LRO)).main:
    ={glob A} /\ O_RMA_Hybrid.j{2} = 0 ==> ={res}.
proof.
proc; sim 7 7: (={is_valid, is_fresh}).
seq  5  5:
  (   ={is_valid, m'}
   /\ ={qs, sk}(O_RMA_Lazy, O_RMA_Hybrid)
   /\ (O_RMA_Hybrid.j = 0){2}
   /\ (O_RMA_Hybrid.j < size O_RMA_Hybrid.qs <=> () \in RO.m){2}
   /\ (O_RMA_Lazy.bad => n_efrma <= size O_RMA_Lazy.qs){1}).
+ call Sverify_stateless.
  call (: ={qs, sk}(O_RMA_Lazy, O_RMA_Hybrid)
       /\ (O_RMA_Hybrid.j = 0){2}
       /\ (O_RMA_Hybrid.j < size O_RMA_Hybrid.qs <=> () \in RO.m){2}
       /\ (O_RMA_Lazy.bad => n_efrma <= size O_RMA_Lazy.qs){1}).
  + proc; sp; if=> //.
    + rcondf {2} 1; 1:by auto; smt(size_ge0).
      if {2}.
      + inline *.
        rcondf {2} 7; 1:by auto=> /#.
        rcondt {2} 3; 1:by auto=> /#.
        auto=> /> &1 &2 + + + + + m _.
        by rewrite !domE !get_set_sameE !size_rcons /#.
      rcondt {2} 1; 1:by auto; smt(size_ge0).
      by auto=> /> &1 &2 + + + + + m _; rewrite size_rcons /#.
    by auto => /#.
  inline *.
  rcondf {2} 8; 1:by auto; call (: true); auto.
  auto; call Skeygen_stateless; auto=> />.
  by rewrite domE emptyE.
inline {1} 1; inline {2} 1.
sp; case: (O_RMA_Lazy.bad{1}).
+ rcondf {1} 1; 1:by auto=> /#.
  rcondf {2} 1; 1:by auto=> /#.
  by auto.
while (={q}
    /\ ={qs, sk}(O_RMA_Lazy, O_RMA_Hybrid)
    /\ (O_RMA_Hybrid.j = 0){2}
    /\ (O_RMA_Hybrid.j < size O_RMA_Hybrid.qs <=> () \in RO.m){2}).
+ inline *; sp; if=> //; 2:by auto.
  rcondf {2} 1; 1:by auto; smt(size_ge0).
  if {2}.
  + inline *.
    rcondf {2} 7; 1:by auto=> /#.
    rcondt {2} 3; 1:by auto=> /#.
    auto=> /> &1 &2 + + + + m _.
    by rewrite !domE !get_set_sameE !size_rcons /#.
  rcondt {2} 1; 1:by auto; smt(size_ge0).
  by auto=> /> &1 &2 + + + + m _; rewrite size_rcons /#.
by auto=> /#.
qed.

local equiv hybrid_right:
  I_EF_RMA0(S, A, O_RMA_Hybrid(RO)).main ~ I_EF_RMA0(S, A, O_RMA_Eager).main:
    ={glob A} /\ O_RMA_Hybrid.j{1} = n_efrma ==> ={res}.
proof.
proc.
seq  6  6:
  (   ={is_valid, m', q}
   /\ ={qs, sk, msigl}(O_RMA_Hybrid, O_RMA_Eager)
   /\ (O_RMA_Hybrid.j = n_efrma){1}
   /\ (size O_RMA_Hybrid.qs <= n_efrma){1}
   /\ (size O_RMA_Hybrid.msigl = n_efrma){1}
   /\ (q = size O_RMA_Hybrid.qs){1}).
+ inline *; auto; call Sverify_stateless.
  call (: ={qs, sk, msigl}(O_RMA_Hybrid, O_RMA_Eager)
       /\ (O_RMA_Hybrid.j = n_efrma){1}
       /\ (size O_RMA_Hybrid.qs <= n_efrma){1}
       /\ (size O_RMA_Hybrid.msigl = n_efrma){1}).
  + proc.
    sp 1 0; if {1}.
    + rcondt {1} 1; 1:by auto.
      rcondf {1} 2; 1:by auto=> /#.
      rcondf {1} 2; 1:by auto=> /#.
      by auto=> /> &0; rewrite size_rcons /#.
    auto=> /> &0 &2 eqwt qs_le_n msigl_n /lezNgt n_le_qs.
    by rewrite (nth_default witness) /#.
  wp; rnd {1}; wp.
  while (={msigl, sk}(O_RMA_Hybrid, O_RMA_Eager)
      /\ (O_RMA_Hybrid.j = n_efrma){1}
      /\ (size O_RMA_Hybrid.msigl <= n_efrma){1}).
  + by auto=> /> &2 + + m _; rewrite size_rcons /#.
  auto; call Skeygen_stateless; auto=> />.
  by rewrite ge0_nefrma /#.
inline *; wp.
while (={q}
    /\ ={qs, sk, msigl}(O_RMA_Hybrid, O_RMA_Eager)
    /\ (O_RMA_Hybrid.j = n_efrma){1}
    /\ (q = size O_RMA_Hybrid.qs){1}
    /\ (size O_RMA_Hybrid.qs <= n_efrma){1}
    /\ (size O_RMA_Hybrid.msigl = n_efrma){1}).
+ sp 1 0.
  rcondt {1} 1; 1:by auto=> /#.
  rcondt {1} 1; 1:by auto=> /#.
  rcondf {1} 2; 1:by auto=> /#.
  rcondf {1} 2; 1:by auto=> /#.
  rcondt {2} 2; 1:by auto=> /#.
  by auto=> /> &0; rewrite size_rcons /#.
by auto.
qed.

local lemma hybrid_mid_oracle j:
     0 <= j < n_efrma
  => equiv[ O_RMA_Hybrid(RO, S).sign ~ O_RMA_Hybrid(LRO, S).sign:
              ={O_RMA_Hybrid.qs}
           /\ (O_RMA_Hybrid.j = j){1} /\ (O_RMA_Hybrid.j = j + 1){2}
           /\ (size O_RMA_Hybrid.qs <= j + 1 <=> () \notin RO.m){2}
           /\ (   size O_RMA_Hybrid.qs{1} <= j
               =>    (size O_RMA_Hybrid.msigl = j){1}
                  /\ (size O_RMA_Hybrid.msigl = j + 1){2}
                  /\ exists m_j,
                          RO.m.[()]{1} = Some m_j
                       /\ let (sig_j, sk) = opsign O_RMA_Hybrid.sk{1} m_j
                          in    sk = O_RMA_Hybrid.sk{2}
                             /\ O_RMA_Hybrid.msigl{2} = rcons O_RMA_Hybrid.msigl{1} (m_j, sig_j))
           /\ (   j < size O_RMA_Hybrid.qs{1}
               => (   ={O_RMA_Hybrid.msigl, O_RMA_Hybrid.sk}))
           ==>    ={res, O_RMA_Hybrid.qs}
               /\ (O_RMA_Hybrid.j = j){1} /\ (O_RMA_Hybrid.j = j + 1){2}
               /\ (size O_RMA_Hybrid.qs <= j + 1 <=> () \notin RO.m){2}
               /\ (   size O_RMA_Hybrid.qs{1} <= j
                   =>    (size O_RMA_Hybrid.msigl = j){1}
                      /\ (size O_RMA_Hybrid.msigl = j + 1){2}
                      /\ exists m_j,
                              RO.m.[()]{1} = Some m_j
                           /\ let (sig_j, sk) = opsign O_RMA_Hybrid.sk{1} m_j
                              in    sk = O_RMA_Hybrid.sk{2}
                                 /\ O_RMA_Hybrid.msigl{2} = rcons O_RMA_Hybrid.msigl{1} (m_j, sig_j))
               /\ (   j < size O_RMA_Hybrid.qs{1}
                   => (   ={O_RMA_Hybrid.msigl, O_RMA_Hybrid.sk})) ].
proof.
move=> [] ge0_j j_le_n.
proc.
sp; if=> //; 2: by auto => /#.
case: (size O_RMA_Hybrid.qs{1} < j).
+ rcondt {1} 1; 1:by auto=> /#.
  rcondf {1} 2; 1:by auto=> /#.
  rcondf {1} 2; 1:by auto=> /#.
  rcondt {2} 1; 1:by auto=> /#.
  rcondf {2} 2; 1:by auto=> /#.
  rcondf {2} 2; 1:by auto=> /#.
  auto=> /> &1 &2.
  move=> eqwt2 eqwt1 dom_m2 pre_inv post_inv qs_lt_n qs_lt_j.
  move: (pre_inv _); 1:smt().
  move=> /> size_rel m_j m1_tt.
  case _: (opsign O_RMA_Hybrid.sk{1} m_j)=> /> sig_j sig_jP msiglRP.
  smt(nth_rcons size_rcons).
rcondf {1} 1; 1:by auto=> /#.
case: (size O_RMA_Hybrid.qs{1} = j).
+ rcondt {1} 1; 1:by auto=> /#.
  inline *.
  rcondf {1} 3; 1:by auto=> /#.
  rcondf {1} 6; 1:by auto=> /#.
  rcondt {2} 1; 1:by auto=> /#.
  rcondf {2} 2; 1:by auto=> /#.
  rcondf {2} 2; 1:by auto=> /#.
  auto=> /> &1 &2.
  move=> eqwt2 eqwt1 dom_m2 pre_inv qs_lt_n qs_eq_j m _.
  move: pre_inv=> /> msigl1_qs msigl2_Sqs m_j m1_tt.
  case _: (opsign O_RMA_Hybrid.sk{1} m_j)=> /> sig_j sig_jP msiglRP.
  smt(nth_rcons size_rcons).
rcondf {1} 1; 1:by auto=> /#.
rcondt {1} 1; 1:by auto=> /#.
rcondf {2} 1; 1:by auto=> /#.
case: (size O_RMA_Hybrid.qs{1} = j + 1).
+ rcondt {2} 1; 1:by auto=> /#.
  inline *.
  rcondt {2} 3; 1:by auto=> /#.
  rcondf {2} 7; 1:by auto=> /#.
  auto=> /> &1 &2.
  move=> eqwt2 eqwt1 dom_m2 _ post_inv qs_lt_n _ _ qs_Sj m _.
  move: (post_inv _); 1:smt().
  rewrite !domE size_rcons !get_set_sameE=> /= />.
  by rewrite !size_rcons /#.
rcondf {2} 1; 1:by auto=> /#.
rcondt {2} 1; 1:by auto=> /#.  
auto=> /> &1 &2 eqwt2 eqwt1 dom_m2 _ post_inv qs_lt_n /lezNgt j_le_qs j_neq_qs Sj_neq_qs m _.
move: (post_inv _); 1:smt().
by rewrite size_rcons /#.
qed.

local lemma hybrid_mid j:
     0 <= j < n_efrma
  => equiv[ I_EF_RMA0(S, A, O_RMA_Hybrid(RO)).main ~ I_EF_RMA0(S, A, O_RMA_Hybrid(LRO)).main:
              ={glob A} /\ O_RMA_Hybrid.j{1} = j /\ O_RMA_Hybrid.j{2} = j + 1 ==> ={res} ].
proof.
move=> /> ge0_j j_le_nefrma.
proc.
inline O_RMA_Hybrid(RO, S).fresh O_RMA_Hybrid(LRO, S).fresh.
wp.
while (={O_RMA_Hybrid.qs, q}
    /\ (O_RMA_Hybrid.j = j){1} /\ (O_RMA_Hybrid.j = j + 1){2}
    /\ (size O_RMA_Hybrid.qs <= j + 1 <=> () \notin RO.m){2}
    /\ (   size O_RMA_Hybrid.qs{1} <= j
        =>    (size O_RMA_Hybrid.msigl = j){1}
           /\ (size O_RMA_Hybrid.msigl = j + 1){2}
           /\ exists m_j,
                   RO.m.[()]{1} = Some m_j
                /\ let (sig_j, sk) = opsign O_RMA_Hybrid.sk{1} m_j
                   in    sk = O_RMA_Hybrid.sk{2}
                      /\ O_RMA_Hybrid.msigl{2} = rcons O_RMA_Hybrid.msigl{1} (m_j, sig_j))
    /\ (   j < size O_RMA_Hybrid.qs{1}
        => (   ={O_RMA_Hybrid.msigl, O_RMA_Hybrid.sk}))).
+ by wp; call (hybrid_mid_oracle j); auto=> /#.
inline {1} 6; inline {2} 6.
wp; call Sverify_stateless.
call (: ={O_RMA_Hybrid.qs}
     /\ (O_RMA_Hybrid.j = j){1} /\ (O_RMA_Hybrid.j = j + 1){2}
     /\ (size O_RMA_Hybrid.qs <= j + 1 <=> () \notin RO.m){2}
     /\ (   size O_RMA_Hybrid.qs{1} <= j
         =>    (size O_RMA_Hybrid.msigl = j){1}
            /\ (size O_RMA_Hybrid.msigl = j + 1){2}
            /\ exists m_j,
                    RO.m.[()]{1} = Some m_j
                 /\ let (sig_j, sk) = opsign O_RMA_Hybrid.sk{1} m_j
                    in    sk = O_RMA_Hybrid.sk{2}
                       /\ O_RMA_Hybrid.msigl{2} = rcons O_RMA_Hybrid.msigl{1} (m_j, sig_j))
     /\ (   j < size O_RMA_Hybrid.qs{1}
         => (   ={O_RMA_Hybrid.msigl, O_RMA_Hybrid.sk}))).
+ by conseq (hybrid_mid_oracle j _)=> //#.
inline *.
rcondt {1} 12.
+ auto; while (RO.m.[()] = None).
  + by auto.
  by auto; conseq (: true); 1:smt(emptyE).
splitwhile {2} 8: (size O_RMA_Hybrid.msigl < O_RMA_Hybrid.j - 1).
rcondt {2} 9.
+ auto; while (size O_RMA_Hybrid.msigl <= j /\ O_RMA_Hybrid.j = j + 1).
  + by auto; smt(size_rcons).
  by auto; call (: true)=> />; auto=> /#.
rcondf {2} 12.
+ auto; while (size O_RMA_Hybrid.msigl <= j /\ O_RMA_Hybrid.j = j + 1).
  + by auto; smt(size_rcons).
  by auto; call (: true)=> />; auto; smt(size_rcons).
auto.
while (={O_RMA_Hybrid.msigl, O_RMA_Hybrid.sk}
    /\ O_RMA_Hybrid.j{1} = j
    /\ O_RMA_Hybrid.j{2} = j + 1
    /\ size O_RMA_Hybrid.msigl{1} <= j).
+ by auto=> />; smt(size_rcons).
auto; call Skeygen_stateless; auto=> />.
smt(emptyE size_rcons get_setE).
qed.

local module D (O : RO) = {
  proc distinguish = I_EF_RMA0(S, A, O_RMA_Hybrid(O)).main
}.

local clone FullEager.

local equiv hybrid_mid_nop:
  I_EF_RMA0(S, A, O_RMA_Hybrid(LRO)).main ~ I_EF_RMA0(S, A, O_RMA_Hybrid(RO)).main:
    ={glob D, RO.m} ==> ={res}.
proof.
symmetry; conseq (FullEager.RO_LRO_D D _)=> />.
exact: dmsg_ll.
qed.

local module Run (O : Oracle_RMA) = {
  proc main(j : int) = {
    var b;

    O_RMA_Hybrid.j <- j;
    b <@ I_EF_RMA0(S, A, O).main();
    return b;
  }
}.
    

local lemma pr_hybrid &m:
    Pr[I_EF_RMA0(S, A, O_RMA_Lazy).main() @ &m: res]
  = Pr[I_EF_RMA0(S, A, O_RMA_Eager).main() @ &m: res].
proof.
have ->: Pr[I_EF_RMA0(S, A, O_RMA_Lazy).main() @ &m: res]
       = Pr[Run(O_RMA_Hybrid(LRO)).main(0) @ &m: res].
+ byequiv (: ={glob A} /\ j{2} = 0 ==> _)=> //; proc *; inline {2} 1; wp.
  by call hybrid_left; auto.
have ->: Pr[I_EF_RMA0(S, A, O_RMA_Eager).main() @ &m: res]
       = Pr[Run(O_RMA_Hybrid(RO)).main(n_efrma) @ &m: res].
+ byequiv (: ={glob A} /\ j{2} = n_efrma ==> _)=> //; proc *; inline {2} 1; wp.
  by symmetry; call hybrid_right; auto.
have: (n_efrma <= n_efrma) by done.
move: {-3}n_efrma ge0_nefrma=> n.
elim: n=> //=.
+ move=> _; byequiv (: ={glob D, RO.m, j} ==> _)=> //=.
  by proc; call hybrid_mid_nop; auto.
move=> n ge0_n ih Sn_ge_n.
rewrite ih 1:/#.
have ->: Pr[Run(O_RMA_Hybrid(RO)).main(n) @ &m: res]
       = Pr[Run(O_RMA_Hybrid(LRO)).main(n + 1) @ &m: res].
+ byequiv (: ={glob A} /\ j{1} = n /\ j{2} = n + 1 ==> _)=> //.
  by proc; call (hybrid_mid n)=> [/#|]; auto.
byequiv (: ={glob D, RO.m, j} ==> _)=> //.
by proc; call hybrid_mid_nop; auto.
qed.

local equiv right_eq:
  I_EF_RMA0(S, A, O_RMA_Eager).main ~ EF_RMA(S, R_EFRMA_IEFRMA(A)).main:
    ={glob A} ==> ={res}.
proof.
proc.
inline O_RMA_Eager(S).fresh.
wp; conseq (: ={is_valid, m'}
           /\ O_RMA_Eager.qs{1} = unzip1 msigl{2})=> //.
seq  5  5:
  (   ={pk, m', sig', is_valid}
   /\ (size O_RMA_Eager.qs <= n_efrma){1}
   /\ (O_RMA_Eager.msigl{1} = msigl{2})
   /\ (forall i, 0 <= i < size O_RMA_Eager.qs{1} => nth witness O_RMA_Eager.qs{1} i = (nth witness msigl{2} i).`1)
   /\ (size O_RMA_Eager.qs{1} <= R_EFRMA_IEFRMA.O_R.q{2})
   /\ (size O_RMA_Eager.qs{1} < n_efrma => size O_RMA_Eager.qs{1} = R_EFRMA_IEFRMA.O_R.q{2})
   /\ (size msigl{2} = n_efrma)).
+ call Sverify_stateless; inline {2} 4; wp.
  call (: (O_RMA_Eager.msigl{1} = R_EFRMA_IEFRMA.O_R.msigl{2})
       /\ (forall i, 0 <= i < size O_RMA_Eager.qs{1} => nth witness O_RMA_Eager.qs{1} i = (nth witness R_EFRMA_IEFRMA.O_R.msigl{2} i).`1)
       /\ (size O_RMA_Eager.qs{1} <= n_efrma)
       /\ (size O_RMA_Eager.qs{1} <= R_EFRMA_IEFRMA.O_R.q{2})
       /\ (size O_RMA_Eager.qs{1} < n_efrma => size O_RMA_Eager.qs{1} = R_EFRMA_IEFRMA.O_R.q{2})
       /\ (size R_EFRMA_IEFRMA.O_R.msigl{2} = n_efrma)).
  + by proc; inline *; auto; smt(size_rcons nth_rcons nth_default).
  inline *; wp=> //=.
  while (O_RMA_Eager.sk{1} = sk{2}
     /\ (O_RMA_Eager.msigl{1} = msigl{2})
     /\ (0 <= size O_RMA_Eager.msigl <= n_efrma){1}).
  + wp; ecall {2} (S_pfun sk{2} m{2}); auto=> /> &0 + _ + m _.
    by rewrite size_rcons /#.
  wp; call Skeygen_stateless; auto=> />.
  by rewrite ge0_nefrma /#.
inline {1} 1; sp.
case: (n_efrma <= q{1}).
+ rcondf {1} 1; 1:by auto=> /#.
  auto=> />; smt(eq_from_nth size_map nth_map).
conseq (: O_RMA_Eager.qs{1} = unzip1 msigl{2})=> //.
while {1}
  (   (q = size O_RMA_Eager.qs){1}
   /\ (0 <= q <= n_efrma){1}
   /\ (O_RMA_Eager.msigl{1} = msigl{2})
   /\ (forall i, 0 <= i < q{1} => nth witness O_RMA_Eager.qs{1} i = (nth witness msigl{2} i).`1)
   /\ (size msigl{2} = n_efrma))
  (n_efrma - q{1}).
+ move=> &0 z.
  inline *. rcondt 2; 1:by auto=> /#.
  by auto=> />; smt(size_rcons nth_rcons).
by auto; smt(size_ge0 eq_from_nth size_map nth_map).
qed.

local lemma pr_bad d &m:
     (forall m, mu1 dmsg m <= d)
  => Pr[I_EF_RMA0(S, A, O_RMA_Lazy).main() @ &m: I_EF_RMA0.bad] <= n_efrma%r * d.
proof.
move=> p; byphoare=> //.
proc.
seq 6: (!I_EF_RMA0.bad) 1%r (n_efrma%r * d) 0%r _ (q <= n_efrma => q = size O_RMA_Lazy.qs)=> //.
+ inline 6; wp.
  conseq (: size O_RMA_Lazy.qs <= n_efrma)=> [/#|].
  call (: true).
  call (: size O_RMA_Lazy.qs <= n_efrma).
  + proc; if; 2:by auto.
    by auto=> /> &0 + + m _; rewrite size_rcons /#.
  inline *; auto; conseq (: true)=> //=.
  exact: ge0_nefrma.
+ inline 2; wp.
  exlim (n_efrma - q)=> n; case @[ambient]: (0 <= n); last first.
  + move=> /ltzNge lt0_n; rcondf 1; 1:by auto=> /#.
    by hoare=> // /> &0; move: (p witness); smt(ge0_mu ge0_nefrma).
  move=> ge0_n.
  conseq (: _: <= ((n_efrma - q)%r * d))=> />.
  + move=> &0 ->> /(_ _)=> [/#|] -> _.
    by move: (p witness); smt(ge0_mu ge0_nefrma size_ge0).
  elim: n ge0_n.
  + rcondf 1; 1:by auto=> /#.
    by hoare=> // /> &0; move: (p witness); smt(ge0_mu ge0_nefrma).
  move=> n ge0_n ih.
  rcondt 1; 1:by auto=> /#.
  seq  3: (I_EF_RMA0.bad) d 1%r 1%r (n%r * d) (n = n_efrma - q /\ q = size O_RMA_Lazy.qs)=> //.
  + inline *; rcondt 1; 1:by auto=> /#.
    by auto=> />; smt(size_rcons).
  + inline *; rcondt 1; 1:by auto=> /#.
    wp; rnd (pred1 m'); auto=> />.
    by move=> &0 _ _ _; exact: p.
  + by conseq ih.
  + smt().
by sp; hoare=> /=; conseq (: true)=> //.
qed.

lemma I_EFRMA_le_EF_RMA d &m:
     (forall m, mu1 dmsg m <= d)
  => Pr[I_EF_RMA(S, A, O_RMA_Default).main() @ &m : res]
     <= Pr[EF_RMA(S, R_EFRMA_IEFRMA(A)).main() @ &m : res]
        + n_efrma%r * d.
proof.
move=> guessing.
have ->: Pr[I_EF_RMA(S, A, O_RMA_Default).main() @ &m: res]
       = Pr[I_EF_RMA(S, A, O_RMA_Lazy).main() @ &m: res].
+ by byequiv left_eq.
apply: (StdOrder.RealOrder.ler_trans (  Pr[I_EF_RMA0(S, A, O_RMA_Lazy).main() @ &m: res]
                                      + Pr[I_EF_RMA0(S, A, O_RMA_Lazy).main() @ &m: I_EF_RMA0.bad])).
+ by byequiv left_mid.
apply: StdOrder.RealOrder.ler_add.
+ apply: (StdOrder.RealOrder.ler_trans Pr[I_EF_RMA0(S, A, O_RMA_Eager).main() @ &m: res]).
  + by rewrite pr_hybrid.
  by byequiv right_eq.
by rewrite pr_bad.
qed.

end section.
