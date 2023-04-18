(* --- Require/Import --- *)
(* -- Built-In (Standard Library) -- *)
require import AllCore List Distr.


(* -- Local -- *)
require import FL_XMSS_TW.
require (*--*) HashThenSign.


type mseed.
type mkey.

op mkg : mseed -> mkey.

(* Authentication paths in Fixed-Length XMSS-TW binary hash tree *)
type apXMSSTW = apFLXMSSTW.

(* Public keys *)
type pkXMSSTW = pkFLXMSSTW.

(* Secret keys *)
type skXMSSTW = .

(* Messages *)
type msgXMSSTW = msgWOTS.

(* Signatures *)
type sigXMSSTW = index * sigWOTS * apFLXMSSTW.

