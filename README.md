# Machine-Checked Security for XMSS as in RFC 8391 and SPHINCS+
This repository accompanies the paper "Machine-Checked Security for XMSS as in RFC 8391 and SPHINCS+", authored by Manuel Barbosa, François Dupressoir, Benjamin Grégoire, Andreas Hülsing, Matthias Meijers, and Pierre-Yves Strub. The most recent version of the paper can be found [here](https://eprint.iacr.org/2023/408).\
\
This repository comprises EasyCrypt scripts primarily aimed at the formal verification of the security of XMSS as a standalone construction &mdash; specified in [RFC 8391](https://www.rfc-editor.org/rfc/rfc8391). Due to the modular approach taken in the formal verification, the scripts contain an independent formal verification of the fix of the security proof of SPHINCS+ presented in [Recovering the Tight Security Proof of SPHINCS+](https://link.springer.com/chapter/10.1007/978-3-031-22972-5_1), validating the remediation of the flaw in the original proof and paving the way for a complete formal verification of SPHINCS+. Furthermore, again due to the modular approach, the scripts contain an independent formal verification of a security property of XMSS as a component of SPHINCS+.\
\
Currently, the latest version of EasyCrypt that has been confirmed to verify the scripts in this repository corresponds to the following commit of the `deploy-quantum-upgrade` branch of the [EasyCrypt repository](https://github.com/EasyCrypt/easycrypt): `commit 94538c51e6ed4ec582bf9c8bb5d9331bc1781993`.

## Repository Structure and Contents
This repository is structured as follows.
* `proofs/`: All scripts relevant to the formal verification of the security of XMSS (both as standalone and as a component of SPHINCS+) and the fix of the security proof of SPHINCS+.
  * `acai/` (*abstract context address indices*): Scripts comprising a version of the proofs that completely abstracts away (the indices corresponding to) the part of the addresses that is not directly used/manipulated in the executed operations (i.e., the part that may be used to, for example, differentiate the context in an encompassing structure).  
    * `DigitalSignatures.eca`: (Library) Generically defines signature schemes (both stateless and key-updating) and their security notions.
    * `DigitalSignaturesROM.eca`: (Library) Similar to `DigitalSignatures.eca`, except that it defines everything with respect to a random oracle (this is for proofs in the random oracle model).
    * `EUFRMA_Interactive_Equiv.ec`: Demonstrates equivalence between the regular EUF-RMA property for digital signature schemes and its (auxiliary) interactive variant.
    * `FL_XMSS_TW.ec`: Provides the context, specification, and proofs concerning fixed-length XMSS-TW.
    * `HashAddresses.ec`: Generically defines hash addresses and some of their properties (basic).
    * `HashThenSign.eca`: Demonstrates generic results concerning the hash-then-sign paradigm for digital signature schemes.
    * `KeyedHashFunctions.eca`: (Library) Generically defines keyed hash functions and their properties.
    * `Reprogramming.ec`: Demonstrates a generic bound for the reprogramming technique (for a random oracle).
    * `TweakableHashFunctions.eca`: (Library) Generically defines tweakable hash functions and their properties.
    * `WOTS_TW.ec`: Provides the context, specification, and proofs concerning WOTS-TW (with an abstract encoding).
    * `WOTS_TW_Checksum.ec`: Defines the concrete encoding used in WOTS-TW and demonstrates that the proofs from `WOTS_TW.ec` still hold true when using this encoding.
    * `XMSS_TW.ec`: Provides the context, specification, and proofs concerning XMSS-TW.
  * `fsai/` (*fully specified address indices*): Scripts comprising a version of the proofs that entirely specifies the (indices contained in the) addresses. More precisely, it considers the (relevant) indices used for the addresses in SPHINCS+. The files in this directory are identically named to those in the `acai/` directory (except that this directory does not contain the `HashAddresses.ec` file); indeed, each of these files is analogous (in purpose) to its similarly-named counterpart in the `acai\` directory.
