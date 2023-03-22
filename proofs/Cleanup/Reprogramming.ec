require import AllCore List Int Distr RealExp SmtMap FinType StdOrder StdBigop.
(*---*) import Bigreal.BRA Bigreal RField RealOrder.
require (*--*) ROM.

type from.

type hash.

type pT = from distr.

clone import MUniFinFun as MUFF with
  type t <- from.

clone import MUniFinFun as MUFFH with
  type t <- hash.

op [lossless] dhash : hash distr.
    
op p_max (d : pT) =
 listmax Real.(<=) 0%r (map (fun x => mu d (fun p => x = p)) MUFF.FinT.enum).

lemma p_maxE (d : pT) (x : from) : mu d (fun p  => x = p) <= p_max d.
proof.
  apply listmax_gt_in.
  + by apply ler_trans. + by apply ler_total.
  apply mapP; exists x => //=; apply MUFF.FinT.enumP.
qed.

lemma p_max_ge0 (d : pT) : 0%r <= p_max d.
proof. have := (p_maxE d witness); smt(mu_bounded). qed.

const p_max_bound : real.

clone import ROM as ROM_ with
  type in_t <- from,
  type out_t <- hash,
  op dout <- fun _ => dhash,
  type d_in_t <- int,
  type d_out_t <- bool.

  
clone import ROM_.LazyEager as LE with 
  theory FinType <- MUFF.FinT.
  
  
module type Oracle_r = {
    include Oracle
    proc set(x : from, Y : hash) : unit
}.

module type POracle_r = {
    include Oracle_r [-init]
}.

module Wrapped_Oracle (O: POracle) : Oracle_r = {
   var prog_list : (from * hash) list  
   var ch : int

   proc init() : unit = {
     prog_list <- [];
     ch <- 0;
   }

  proc o(x : from): hash = {
     var r,c : hash;
     var tmp : hash option;
    
     r <@ O.o(x);

     ch <- ch + 1; 
     tmp <- assoc prog_list x;
     c <- if tmp = None then r else oget tmp;
     return c; 
  }

   proc set (x : from, y: hash) : unit = {
     prog_list <- (x,y) :: prog_list;
   }

}.

module type RepO_ti = {
    proc init(b : bool) : unit
    proc repro(p : pT) : from
}.

module type RepO_t = {
    include RepO_ti [-init]
}.

module RepO(RO: POracle_r) : RepO_ti = {
    var ctr : int
    var b : bool
    var se : bool

    proc init(in_b : bool) : unit = {
        ctr <- 0;
        b <- in_b;
        se <- true;
    }

    proc repro(p: pT) : from = {
        var x,y;
        se <- if p_max p <= p_max_bound then se else false;
        ctr <- ctr + 1;
        x <$ p;
        if (b) {
            y <$ dhash;
            RO.set(x,y);
        } 
        return x;
    }
}.

module type DistA(RO: POracle, O: RepO_t) = {
    proc distinguish() : bool {RO.o, O.repro}
}.


module ReproGame(RO : Oracle, A : DistA) = {
  module Wrap = Wrapped_Oracle(RO)
  module O = RepO(Wrap)
 
  proc main (b: bool) : bool = {
    var b';
    RO.init();
    Wrap.init();
    O.init(b);
    b' <@ A(Wrap, O).distinguish();
    return b';
  } 
}.

section.

declare module A <: DistA {-ReproGame, -ERO, -Lazy.LRO}.

declare const rep_ctr : {int | 0 <= rep_ctr } as ge0_repctr.
declare const query_ctr : {int | 0 <= query_ctr } as ge0_queryctr.

local module Bad = { 
  var bad : bool
  var co : int
  var cr : int
  var i  : int
}.

local module Wrapped_Oracle1 (O: POracle) : Oracle_r = {
  include var Wrapped_Oracle(O) [-o]
  import var Bad
 
  proc o(x : from): hash = {
    var r,c : hash;
    var tmp : hash option;

    c <- witness;
    if (co <  query_ctr) { 
      r <@ O.o(x);
      tmp <- assoc prog_list x;
      c <- if tmp = None then r else oget tmp;
      co <- co + 1;
    } else {
      bad <- true;
      r <@ O.o(x);
      tmp <- assoc prog_list x;
      c <- if tmp = None then r else oget tmp;      
      co <- co + 1;
    }
    ch <- ch + 1; 
    return c; 
  }

}.

local module Wrapped_Oracle2 (O: POracle) : Oracle_r = {
  include var Wrapped_Oracle(O) [-o]
  import var Bad
 
  proc o(x : from): hash = {
    var r,c : hash;
    var tmp : hash option;

    c <- witness;
    if (co <  query_ctr) { 
      r <@ O.o(x);
      tmp <- assoc prog_list x;
      c <- if tmp = None then r else oget tmp;
      co <- co + 1;
    } else {
      bad <- true;
    }
    ch <- ch + 1; 
    return c; 
  }

}.

local module Wrapped_Oracle2' (O: POracle) : Oracle_r = {
  include var Wrapped_Oracle(O) [-o]
  import var Bad

  proc o(x : from): hash = {
    var r,c : hash;
    var tmp : hash option;

    c <- witness;
    if (co < query_ctr) { 
      r <@ O.o(x);
      tmp <- assoc prog_list x;
      c <- if tmp = None then r else oget tmp;
      co <- co + 1;
    } 
    ch <- ch + 1; 
    return c; 
  }

}.

local module RepO1(RO: POracle_r) : RepO_ti = {
  include var RepO(RO) [-repro]
  import var Bad

  proc repro(p: pT) : from = {
    var x,y;
    se <- if p_max p <= p_max_bound then se else false;
    x <- witness;
    if (se /\ cr < rep_ctr) { 
      x <$ p;
      if (b) {
        y <$ dhash;
        RO.set(x,y);
      }
      cr <- cr + 1;
    } else { 
      bad <- true;
      x <$ p;
      if (b) {
        y <$ dhash;
        RO.set(x,y);
      }
      cr <- cr + 1;
    }
    ctr <- ctr + 1;
    return x;
  }
}.

local module RepO2(RO: POracle_r) : RepO_ti = {
  include var RepO(RO) [-repro]
  import var Bad

  proc repro(p: pT) : from = {
    var x,y;
    se <- if p_max p <= p_max_bound then se else false;
    x <- witness;
    if (se /\ cr < rep_ctr) { 
      x <$ p;
      if (b) {
        y <$ dhash;
        RO.set(x,y);
      } 
      cr <- cr + 1;
    } else { 
      bad <- true;
    }
    ctr <- ctr + 1;
    return x;
  }
}.

local module ReproGame1 (RO: Oracle, A: DistA) = {
  import var Bad
  module Wrap = Wrapped_Oracle1(RO)
  module O = RepO1(Wrap)
 
  proc main (b: bool) : bool = {
    var b';
    bad <- false; co <- 0; cr <- 0;
    RO.init();
    Wrap.init();
    O.init(b);
    b' <@ A(Wrap, O).distinguish();
    return b';
  } 
}.

local module ReproGame2 (RO: Oracle, A: DistA) = {
  import var Bad
  module Wrap = Wrapped_Oracle2(RO)
  module O = RepO2(Wrap)
 
  proc main (b: bool) : bool = {
    var b';
    bad <- false; co <- 0; cr <- 0;
    RO.init();
    Wrap.init();
    O.init(b);
    b' <@ A(Wrap, O).distinguish();
    return b';
  } 
}.

local lemma Pr_count &m b : 
  hoare[ A(Wrapped_Oracle(ERO),RepO(Wrapped_Oracle(ERO))).distinguish : 
     Wrapped_Oracle.ch = 0 /\ RepO.ctr = 0 /\ RepO.se 
     ==> Wrapped_Oracle.ch <= query_ctr /\ 
     RepO.ctr <= rep_ctr /\ RepO.se] 
  =>
  Pr[ReproGame(ERO,A).main(b) @ &m:res] = Pr[ReproGame(ERO,A).main(b) @ &m:res /\  Wrapped_Oracle.ch <= query_ctr /\ RepO.ctr <= rep_ctr /\ RepO.se].
proof.
  move=> hhoare; byequiv => //.
  conseq (: _ ==> ={res, Wrapped_Oracle.ch, RepO.ctr, RepO.se}) (: true ==> Wrapped_Oracle.ch <= query_ctr /\ RepO.ctr <= rep_ctr /\ RepO.se) _ => //; 2: by sim.
  by proc; call hhoare; inline *; auto => /=.
qed.

local lemma Pr_Game_Game1 &m b : 
  Pr[ReproGame(ERO,A).main(b) @ &m:res /\  Wrapped_Oracle.ch <= query_ctr /\ RepO.ctr <= rep_ctr /\ RepO.se] =
  Pr[ReproGame1(ERO,A).main(b) @ &m:res /\  Wrapped_Oracle.ch <= query_ctr /\ RepO.ctr <= rep_ctr /\ RepO.se].
proof.
  byequiv => //.
  proc.
  call (: ={glob ERO,  glob RepO, glob Wrapped_Oracle} /\ ((RepO.ctr, Wrapped_Oracle.ch) = (Bad.cr,Bad.co)){2} ).
  + by proc; case: (Bad.co{2} < query_ctr); [rcondt{2} 2 | rcondf{2} 2]; auto => /=; conseq (: ={r}) => />; sim.
  + proc. seq 1 1: (#pre); 1: by auto.
    swap{1} 1 2.
    by case: ((RepO.se /\ Bad.cr < rep_ctr){2}); [rcondt{2} 2 | rcondf{2} 2]; auto => /=; sim/>.
  inline *; auto. swap{2} [1..3] 3; auto; sim />.
qed.

local lemma Pr_Game1_Game2 &m b: 
  Pr[ReproGame1(ERO,A).main(b) @ &m: res /\ Wrapped_Oracle.ch <= query_ctr /\ RepO.ctr <= rep_ctr /\ RepO.se] =
  Pr[ReproGame2(ERO,A).main(b) @ &m: res /\ Wrapped_Oracle.ch <= query_ctr /\ RepO.ctr <= rep_ctr /\ RepO.se].
proof.
  have : `|Pr[ReproGame1(ERO,A).main(b) @ &m: res /\ Wrapped_Oracle.ch <= query_ctr /\ RepO.ctr <= rep_ctr /\ RepO.se] -
           Pr[ReproGame2(ERO,A).main(b) @ &m: res /\ Wrapped_Oracle.ch <= query_ctr /\ RepO.ctr <= rep_ctr /\ RepO.se] | <=
         RealOrder.maxr Pr[ReproGame1(ERO,A).main(b) @ &m: (res /\ Wrapped_Oracle.ch <= query_ctr /\ RepO.ctr <= rep_ctr /\ RepO.se) /\ Bad.bad] 
                        Pr[ReproGame2(ERO,A).main(b) @ &m: (res /\ Wrapped_Oracle.ch <= query_ctr /\ RepO.ctr <= rep_ctr /\ RepO.se) /\ Bad.bad].
  + byupto.
  have -> : Pr[ReproGame1(ERO, A).main(b) @ &m : (res /\ Wrapped_Oracle.ch <= query_ctr /\ RepO.ctr <= rep_ctr /\ RepO.se) /\ Bad.bad] = 0%r.
  + byphoare => //; hoare.
    proc. call (: Bad.cr <= RepO.ctr /\ Bad.co <= Wrapped_Oracle.ch /\ (Bad.bad => ! (Wrapped_Oracle.ch <= query_ctr /\ RepO.ctr <= rep_ctr /\ RepO.se))). 
    + by proc; sp; wp; if; auto; call (: true); auto => /#.
    + proc; sp; wp; if; auto. 
      + by conseq (: true); auto => /#.
      by swap 1 2; wp; conseq (:true); auto => /#.
    inline *; swap [1..3] 3; auto; conseq (: true) => //= /#.
  have -> /#: Pr[ReproGame2(ERO, A).main(b) @ &m : (res /\ Wrapped_Oracle.ch <= query_ctr /\ RepO.ctr <= rep_ctr /\ RepO.se) /\ Bad.bad] = 0%r.
  byphoare => //; hoare.
  proc. call (: Bad.cr <= RepO.ctr /\ Bad.co <= Wrapped_Oracle.ch /\ (Bad.bad => ! (Wrapped_Oracle.ch <= query_ctr /\ RepO.ctr <= rep_ctr /\ RepO.se))). 
  + by proc; sp; wp; if; auto; 1: call (: true); auto => /#.
  + proc; sp; wp; if; auto; 2: smt().
    by conseq (: true); auto => /#.
  by inline *; swap [1..3] 3; auto; conseq (: true) => //= /#.
qed.

local module RepO2i : RepO_ti = {
  include var RepO(Wrapped_Oracle2'(ERO)) [-repro]
  import var Bad

  proc repro(p: pT) : from = {
    var x,y;
    se <- if p_max p <= p_max_bound then se else false;
    x <- witness;
    if (se /\ cr < rep_ctr) { 
      x <$ p;
      if (i <= cr) {
        y <$ dhash;
        Wrapped_Oracle2(ERO).set(x,y);
      }
      cr <- cr + 1;
    } 
    ctr <- ctr + 1;
    return x;
  }
}.

local module Hi = {
  import var Bad
  module Wrap = Wrapped_Oracle2'(ERO)
  module O = RepO2i
 
  proc main (i0: int) : bool = {
    var b';
    bad <- false; cr <- 0; co <- 0; i <- i0;
    ERO.init();
    Wrap.init();
    O.init(false);
    b' <@ A(Wrap, O).distinguish();
    return b' /\ Wrapped_Oracle.ch <= query_ctr /\ RepO.ctr <= rep_ctr /\ RepO.se;
  } 
}.

local lemma Hi_true &m : 
  Pr[ReproGame2(ERO, A).main(true) @ &m :
       res /\ Wrapped_Oracle.ch <= query_ctr /\ RepO.ctr <= rep_ctr /\ RepO.se]  = 
  Pr[Hi.main(0) @ &m : res].
proof.
  byequiv => //; proc.
  call (: ={glob Wrapped_Oracle, RepO.se, RepO.ctr, ERO.m, Bad.cr, Bad.co} /\ RepO.b{1} /\ (Bad.i <= Bad.cr){2}  ).
  + by sim />.
  + proc. 
    seq 2 2 : (#pre /\ ={x}); 1: by auto.
    wp; if; auto.
    conseq (: ={glob Wrapped_Oracle, RepO.se, RepO.ctr, ERO.m, x}); 1: smt().
    seq 1 1 : (#pre); 1: by sim />.
    by if; auto; sim.
  inline *; swap{1} [1 ..3] 3; swap{2} [1 ..4] 3; auto; sim />.
qed.

local lemma Hi_false &m : 
  Pr[ReproGame2(ERO, A).main(false) @ &m :
       res /\ Wrapped_Oracle.ch <= query_ctr /\ RepO.ctr <= rep_ctr /\ RepO.se]  = 
  Pr[Hi.main(rep_ctr) @ &m : res].
proof.
  byequiv => //; proc.
  call (: ={glob Wrapped_Oracle, RepO.se, RepO.ctr, ERO.m, Bad.cr, Bad.co} /\ !RepO.b{1} /\ (Bad.i = rep_ctr){2}).
  + by sim />.
  + proc. 
    seq 2 2 : (#pre /\ ={x}); 1: by auto.
    wp; if; auto.
    rcondf{1} ^if; 1: by auto.
    by rcondf{2} ^if; auto => /#.
  inline *; swap{1} [1 ..3] 3; swap{2} [1 ..4] 3; auto; sim />.
qed.

local module RepO2i1 (RO: POracle) : RepO_ti = {
  import var Bad

  include var RepO(Wrapped_Oracle2'(RO)) [-repro]
  var x_ : from

  proc repro(p: pT) : from = {
    var x,y;
    se <- if p_max p <= p_max_bound then se else false;
    x <- witness;
    if (se /\ cr < rep_ctr) { 
      x <$ p;
      if (i + 1 <= cr) {
        y <$ dhash;
        Wrapped_Oracle2'(RO).set(x,y);
      } else { if (i = cr) {
        x_ <- x;
        y <@ RO.o(x);
      } } 
      cr <- cr + 1;
    } 
    ctr <- ctr + 1;
    return x;
  }
}.

local module Hi1 (RO:POracle) = {
  import var Bad
  module Wrap = Wrapped_Oracle2'(RO)
  module O = RepO2i1(RO)
 
  proc run (i0: int) : bool = {
    var b';
    bad <- false;  cr <- 0; co <- 0; i <- i0;
    Wrap.init();
    O.init(false);
    b' <@ A(Wrap, O).distinguish();
    return b' /\ Wrapped_Oracle.ch <= query_ctr /\ RepO.ctr <= rep_ctr /\ RepO.se;
  } 
}.

local lemma Hip1_Hi1 &m i_ : Pr[Hi.main(i_ + 1) @ &m : res] = Pr[ Exp(ERO, Hi1).main(i_) @ &m : res].
proof.
  byequiv => //; proc; inline *; wp.
  call (: ={ERO.m, glob Wrapped_Oracle, glob RepO, Bad.cr, Bad.co} /\ Bad.i{1} = Bad.i{2} + 1).
  + by sim />.
  + proc; wp; conseq />.
    seq 2 2 : (#pre /\ ={x}); 1: by auto.
    if => //.
    seq 1 1 : (#pre); 1: by auto.
    if => //; 1: by sim.
    by inline *; auto.
  swap{1} [1..4] 3; auto; sim />.
qed.

local lemma Hi1_ERO_LRO  &m i_ : Pr[ Exp(ERO,Hi1).main(i_) @ &m : res] = Pr[ Exp(Lazy.LRO,Hi1).main(i_) @ &m : res].
proof.
  byequiv (: ={glob Hi1, arg} ==> ={res}) => //; symmetry.
  conseq (eq_eager_sampling Hi1 _) => // *;apply dhash_ll.
qed.

local module RepO2i2 : RepO_ti = {
  import var Bad
  include var RepO(Wrapped_Oracle2'(Lazy.LRO)) [-repro]
  var x_ : from

  proc repro(p : pT) : from = {
    var x,y;
    se <- if p_max p <= p_max_bound then se else false;
    x <- witness;
    if (se /\  cr < rep_ctr) { 
      x <$ p;
      if (i + 1 <= cr) {
        y <$ dhash;
        Wrapped_Oracle2'(Lazy.LRO).set(x,y);
      } else { if (i = cr /\ fsize Lazy.LRO.m <= query_ctr) {
        x_ <- x;
        if (! x \in Lazy.LRO.m) {
          y <@ Lazy.LRO.o(x);
        } else { 
          bad <- true;
          y <@ Lazy.LRO.o(x);          
        }
      } } 
      cr <- cr + 1;
    } 
    ctr <- ctr + 1;
    return x;
  }
}.

local module Hi2 = {
  import var Bad
  module Wrap = Wrapped_Oracle2'(Lazy.LRO)
  module O = RepO2i2
 
  proc run (i0: int) : bool = {
    var b';
    bad <- false;  cr <- 0; co <- 0; i <- i0;
    Lazy.LRO.init();
    Wrap.init();
    O.init(false);
    b' <@ A(Wrap, O).distinguish();
    return b' /\ Wrapped_Oracle.ch <= query_ctr /\ RepO.ctr <= rep_ctr /\ RepO.se;
  } 
}.

local module RepO2i3 : RepO_ti = {
  import var Bad
  include var RepO(Wrapped_Oracle2'(Lazy.LRO)) [-repro]

  proc repro(p: pT) : from = {
    var x,y;
    se <- if p_max p <= p_max_bound then se else false;
    x <- witness;
    if (se /\ cr < rep_ctr) { 
      x <$ p;
      if (i + 1 <= cr) {
        y <$ dhash;
        Wrapped_Oracle2'(Lazy.LRO).set(x,y);
      } else { if (i = cr /\ fsize Lazy.LRO.m <= query_ctr) {
        RepO2i2.x_ <- x;
        if (! x \in Lazy.LRO.m) {
          y <@ Lazy.LRO.o(x);
        } else { 
          bad <- true;
          Lazy.LRO.m <- rem Lazy.LRO.m x;
          y <@ Lazy.LRO.o(x); 
        }
      } } 
      cr <- cr + 1;
    } 
    ctr <- ctr + 1;
    return x;
  }
}.

local module Hi3 = {
  import var Bad
  module Wrap = Wrapped_Oracle2'(Lazy.LRO)
  module O = RepO2i3
 
  proc run (i0: int) : bool = {
    var b';
    
    bad <- false;  cr <- 0; co <- 0; i <- i0;
    Lazy.LRO.init();
    Wrap.init();
    O.init(false);
    b' <@ A(Wrap, O).distinguish();
    return b' /\ Wrapped_Oracle.ch <= query_ctr /\ RepO.ctr <= rep_ctr /\ RepO.se;
  } 
}.

local lemma Hi1_LRO_Hi2  &m i_ : Pr[ Exp(Lazy.LRO,Hi1).main(i_) @ &m : res] = Pr[Hi2.run(i_) @ &m : res].
proof.
  byequiv => //; proc; inline *; wp.
  call (: ={ Lazy.LRO.m, glob Wrapped_Oracle, glob RepO, Bad.cr, Bad.co, Bad.i} /\ (Bad.cr <= Bad.i => fsize Lazy.LRO.m <= Bad.co <= query_ctr){1}); last first.
  + by auto => />; rewrite fsize_empty ge0_queryctr.
  + by proc; sp; inline *; if; auto => /> &2 3? r *; rewrite fsize_set /b2i => /> /#.
  proc; wp; seq 2 2 : (#pre /\ ={x}); 1: by sim />.
  if => //.  
  seq 1 1: (#pre); 1: by sim />.
  if => //.
  + by wp; conseq (: ={y, Wrapped_Oracle.prog_list});[ smt() | sim].
  wp; if => //; 1: smt().
  + by sp 1 1; conseq (: ={Lazy.LRO.m}); [smt() | if{2}; sim].
  auto => /#.
qed.

local lemma Hi2_Hi3 &m i_ : 
  `|Pr[ Hi2.run(i_) @ &m : res] - Pr[Hi3.run(i_) @ &m : res]| <=
   maxr Pr[ Hi2.run(i_) @ &m : Bad.bad] Pr[ Hi3.run(i_) @ &m : Bad.bad].
proof. byupto. qed.

local lemma Hi2_bad &m i_ : 0 <= i_ => Pr[ Hi2.run(i_) @ &m : Bad.bad] <= query_ctr%r * p_max_bound.
proof.
move=> hi; fel 4 (b2i (Bad.i < Bad.cr)) (fun x => query_ctr%r * p_max_bound) 1 Bad.bad
  [RepO2i2.repro : ((if p_max p <= p_max_bound then RepO.se else false) /\ Bad.cr < rep_ctr /\
                      Bad.i = Bad.cr /\ fsize Lazy.LRO.m <= query_ctr)] => //.
+ by rewrite sumri_const.
+ smt().
+ auto => /> /#.
+ proc; wp.
  rcondt ^if; 1: by auto.
  rcondf ^if; 1: by auto => /#.
  rcondt ^if; 1: by auto.
  wp; seq 3 : (x \in Lazy.LRO.m) (query_ctr%r * p_max_bound) 1%r _ 0%r (!Bad.bad) => //.
  + by auto.
  + rnd (fun p => p \in Lazy.LRO.m); auto.
    move=> &hr /> _ _ _ hmax _ _ hsz.
    apply (ler_trans (mu p{hr} (fun (p0 : from ) => exists x, dom Lazy.LRO.m{hr} x /\ x = p0))).
    + by apply mu_le => /> x0 *; exists x0.
    apply (ler_trans ((fsize Lazy.LRO.m{hr})%r * p_max_bound)).
    apply: Mu_mem.mu_mem_le_fsize.
    + by move=> x hx /=; apply: ler_trans hmax; apply: (p_maxE p{hr} x).
    by apply ler_wpmul2r; smt(p_max_ge0). 
  by rcondt ^if; auto; conseq (: false).
+ move=> c;proc.
  rcondt ^if; 1: by auto.
  by wp; conseq (: true) => //; smt().
move=> b c; proc.
seq 2: (! (RepO.se /\ Bad.cr < rep_ctr /\ Bad.i = Bad.cr /\ FSet.card (fdom Lazy.LRO.m) <= query_ctr) /\
             Bad.bad = b /\ b2i (Bad.i < Bad.cr) = c); 1: by auto.
wp; if; last by auto.
seq 1 : (#pre); 1: by auto.
wp; if; 1: by conseq (:true) => // /#.
rcondf ^if; auto => /#. 
qed.

local lemma Hi3_bad &m i_ :  0 <= i_ => Pr[ Hi3.run(i_) @ &m : Bad.bad] <= query_ctr%r * p_max_bound.
proof.
move=> hi; fel 4 (b2i (Bad.i < Bad.cr)) (fun x => query_ctr%r * p_max_bound) 1 Bad.bad
  [RepO2i3.repro : ((if p_max p <= p_max_bound then RepO.se else false) /\ Bad.cr < rep_ctr /\
                      Bad.i = Bad.cr /\ fsize Lazy.LRO.m <= query_ctr)] => //.
+ by rewrite sumri_const.
+ smt().
+ auto => /> /#.
+ proc; wp.
  rcondt ^if; 1: by auto.
  rcondf ^if; 1: by auto => /#.
  rcondt ^if; 1: by auto.
  wp; seq 3 : (x \in Lazy.LRO.m) (query_ctr%r * p_max_bound) 1%r _ 0%r (!Bad.bad) => //.
  + by auto.
  + rnd (fun p  => p \in Lazy.LRO.m); auto.
    move=> &hr /> _ _ _ hmax _ _ hsz.
    apply (ler_trans (mu p{hr} (fun (p0 : from) => exists x, dom Lazy.LRO.m{hr} x /\ x = p0))).
    + by apply mu_le => /> x0 *; exists x0.
    apply (ler_trans ((fsize Lazy.LRO.m{hr})%r * p_max_bound)).
    apply: Mu_mem.mu_mem_le_fsize.
    + by move=> x hx /=; apply: ler_trans hmax; apply (p_maxE p{hr} x).
    by apply ler_wpmul2r; smt(p_max_ge0). 
  by rcondt ^if; auto; conseq (: false).
+ move=> c;proc.
  rcondt ^if; 1: by auto.
  by wp; conseq (: true) => //; smt().
move=> b c; proc.
seq 2: (! (RepO.se /\ Bad.cr < rep_ctr /\ Bad.i = Bad.cr /\ FSet.card (fdom Lazy.LRO.m) <= query_ctr) /\
             Bad.bad = b /\ b2i (Bad.i < Bad.cr) = c); 1: by auto.
wp; if; last by auto.
seq 1 : (#pre); 1: by auto.
wp; if; 1: by conseq (:true) => // /#.
rcondf ^if; auto => /#.
qed.

local module RepO2i4 (RO: POracle) : RepO_ti = {
  import var Bad
  include var RepO(Wrapped_Oracle2'(RO)) [-repro]
  var x_ : from

  proc repro(p: pT) : from = {
    var x,y;
    se <- if p_max p <= p_max_bound then se else false;
    x <- witness;
    if (se /\ cr < rep_ctr) { 
      x <$ p;
      if (i <= cr) {
        y <$ dhash;
        Wrapped_Oracle2'(RO).set(x,y);
      }
      cr <- cr + 1;
    } 
    ctr <- ctr + 1;
    return x;
  }
}.

local module Hi4 (RO:POracle) = {
  import var Bad
  module Wrap = Wrapped_Oracle2'(RO)
  module O = RepO2i4(RO)
 
  proc run (i0: int) : bool = {
    var b';
    bad <- false;  cr <- 0; co <- 0; i <- i0;
    Wrap.init();
    O.init(false);
    b' <@ A(Wrap, O).distinguish();
    return b' /\ Wrapped_Oracle.ch <= query_ctr /\ RepO.ctr <= rep_ctr /\ RepO.se;
  } 
}.

local lemma Hi3_Hi4 &m i_: 0 <= i_ => Pr[Hi3.run(i_) @ &m : res] = Pr[Exp(Lazy.LRO, Hi4).main(i_) @ &m : res].
proof.
  move=> hi; byequiv => //; proc; inline *; wp.
  call (: ={Wrapped_Oracle.ch, glob RepO, Bad.i, Bad.cr, Bad.co} /\ 
     if (Bad.cr <= Bad.i){1} then ={Lazy.LRO.m, Wrapped_Oracle.prog_list} /\ Wrapped_Oracle.prog_list{1} = [] /\ (fsize Lazy.LRO.m <= Bad.co <= query_ctr){1}
     else 
       ((RepO2i2.x_ \in Lazy.LRO.m){1} /\
        Wrapped_Oracle.prog_list{2} = (rcons Wrapped_Oracle.prog_list (RepO2i2.x_, oget Lazy.LRO.m.[RepO2i2.x_])){1} /\
        eq_except (pred1 RepO2i2.x_{1}) Lazy.LRO.m{1} Lazy.LRO.m{2})).
  + proc; sp; wp; if => //.
    inline *; auto => |> &1 &2. 
    case: (Bad.cr{2} <= Bad.i{2}) => |> 4? r ?.
    + by rewrite fsize_set /b2i => /> /#.
    rewrite -!cats1 assoc_cat.
    by case: (assocP  Wrapped_Oracle.prog_list{1} x{2}) => />; smt(mem_set get_setE).
  + proc; wp; seq 2 2 : (#pre /\ ={x}); 1: by auto.
    if => //.
    seq 1 1: (#pre /\ ={x}); 1: by auto.
    if{1}.
    + rcondt{2} ^if; 1: by auto => /#.
      by inline *; auto => />; smt().
    if{1}.
    + rcondt{2} ^if; 1: by auto.
      by sp 1 0; inline *; if{1}; auto; smt(get_setE remE).  
    by rcondf{2} ^if; auto => /> /#. 
  by auto => />; rewrite fsize_empty ge0_queryctr.
qed.

local lemma Hi4_LRO_ERO &m i_: Pr[Exp(Lazy.LRO, Hi4).main(i_) @ &m : res] = Pr[Exp(ERO, Hi4).main(i_) @ &m : res].
proof.
  byequiv (: ={glob Hi4, arg} ==> ={res}) => //.
  conseq (eq_eager_sampling Hi4 _) => // *;apply dhash_ll.
qed.

local lemma Hi4_Hi &m i_ : Pr[Exp(ERO, Hi4).main(i_) @ &m : res] = Pr[Hi.main(i_) @ &m : res].
proof. byequiv => //; proc; inline *; wp; swap{2} [1 .. 4] 3; sim. qed.

local lemma rom_reprogramming1 &m i_ : 0 <= i_ => 
  `|Pr[Hi.main(i_ + 1) @ &m : res] - Pr[Hi.main(i_) @ &m : res]| <= query_ctr%r * p_max_bound.
proof.
  move=> hi; rewrite (Hip1_Hi1 &m i_) (Hi1_ERO_LRO  &m i_) (Hi1_LRO_Hi2 &m i_).
  rewrite -(Hi4_Hi &m i_) -(Hi4_LRO_ERO &m i_) -(Hi3_Hi4 &m i_) 1://.
  move: (Hi2_Hi3 &m i_) (Hi2_bad &m i_) (Hi3_bad &m i_) => /#.
qed.

(* ----------------------------------------------------- *)

lemma rom_reprogramming &m : 
   hoare[A(Wrapped_Oracle(ERO), RepO(Wrapped_Oracle(ERO))).distinguish : 
     Wrapped_Oracle.ch = 0 /\ RepO.ctr = 0 /\ RepO.se 
     ==> Wrapped_Oracle.ch <= query_ctr /\ 
     RepO.ctr <= rep_ctr /\ RepO.se]
  =>
 `|Pr[ReproGame(ERO, A).main(false) @ &m:res]
 - Pr[ReproGame(ERO, A).main(true) @ &m:res]|
  <= rep_ctr%r * query_ctr%r * p_max_bound. 
proof.
move => Hquery.
rewrite 2!(Pr_count &m _ Hquery) 2!(Pr_Game_Game1 &m) 2!(Pr_Game1_Game2 &m).
rewrite Hi_true Hi_false.
rewrite (telescoping_sum_down (fun i => Pr[Hi.main(i) @ &m : res]) 0 rep_ctr ge0_repctr) /=.
apply (ler_trans (bigi predT (fun (i : int) => `|Pr[Hi.main(i + 1) @ &m : res] - Pr[Hi.main(i) @ &m : res]|) 0 rep_ctr)).
+ by apply big_normr.
apply (ler_trans (bigi predT (fun (i : int) => query_ctr%r * p_max_bound) 0 rep_ctr)).
+ by apply ler_sum_seq => i_ /mem_range |> *; apply (rom_reprogramming1 &m i_).
by rewrite sumri_const 1:ge0_repctr /#.
qed.

end section.
