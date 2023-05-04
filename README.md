# Machine-Checked Security for XMSS as in RFC 8391 and SPHINCS+
This repository accompanies the paper "Machine-Checked Security for XMSS as in RFC 8391 and SPHINCS+", authored by Manuel Barbosa, François Dupressoir, Benjamin Grégoire, Andreas Hülsing, Matthias Meijers, and Pierre-Yves Strub. The most recent version of the paper can be found [here](https://eprint.iacr.org/2023/408).\
\
This repository comprises EasyCrypt scripts aimed at the formal verification of the security of XMSS as (1) a standalone construction &mdash; specified in [RFC 8391](https://www.rfc-editor.org/rfc/rfc8391) &mdash; and (2) a component of SPHINCS+ &mdash; specified in [the SPHINCS+ specification](https://sphincs.org/data/sphincs+-r3.1-specification.pdf).\
\
Currently, the latest version of EasyCrypt that has been confirmed to verify the scripts in this repository corresponds to the following commit of the `deploy-quantum-upgrade` branch of the [EasyCrypt repository](https://github.com/EasyCrypt/easycrypt): `commit 94538c51e6ed4ec582bf9c8bb5d9331bc1781993`.

## Repository Structure and Contents (TODO)
This repository is structured as follows.
* `proofs/`: All scripts relevant to the formal verification of the security of XMSS (both as standalone and as a component of SPHINCS+).
  * `DigitalSignatures.eca`: (Library) Generically defines signature schemes (both stateless and key-updating) and their security notions.
  * `DigitalSignaturesROM.eca`: (Library) Similar to `DigitalSignatures.eca`, except that it defines everything with respect to a random oracle (this is for proofs in the random oracle model).
  * `EFRMA_Interactive_Equiv.ec`: Demonstrates equivalence between the regular EF-RMA property for digital signature schemes and its (auxiliary) interactive variant.
  * `FL_XMSS_TW.ec`: Provides the context, specification, and proofs concerning fixed-length XMSS-TW.
  * `HashThenSign.eca`: Demonstrates generic results concerning the hash-then-sign paradigm for digital signature schemes.
  * `KeyedHashFunctions.eca`: (Library) Generically defines keyed hash functions and their properties.
  * `Reprogramming.ec`: Demonstrates a generic bound for the reprogramming technique (for a random oracle).
  * `TweakableHashFunctions.eca`: (Library) Generically defines tweakable hash functions and their properties.
  * `WOTS_TW.ec`: Provides the context, specification, and proofs concerning WOTS-TW (with an abstract encoding).
  * `WOTS_TW_Checksum.ec`: Defines the concrete encoding used in WOTS-TW and demonstrates that the proofs from `WOTS_TW.ec` still hold true when using this encoding.
  * `XMSS_TW.ec`: Provides the context, specification, and proofs concerning XMSS-TW.
