# Machine-Checked Security for XMSS as in RFC 8391 and SPHINCS+
This repository accompanies the paper "Machine-Checked Security for XMSS as in RFC 8391 and SPHINCS+", authored by Manuel Barbosa, François Dupressoir, Benjamin Grégoire, Andreas Hülsing, Matthias Meijers, and Pierre-Yves Strub.\
\
This repository comprises EasyCrypt scripts aimed at the formal verification of the security of XMSS as (1) a standalone construction (specified in [RFC 8391](https://www.rfc-editor.org/rfc/rfc8391)) and (2) a component of SPHINCS+ (specified in [the SPHINCS+ specification](https://sphincs.org/data/sphincs+-r3.1-specification.pdf)).
\
Currently, the latest version of EasyCrypt that has been confirmed to verify the scripts in this repository corresponds to the following commit of the deploy-quantum-upgrade branch of the [EasyCrypt repository](https://github.com/EasyCrypt/easycrypt): `commit b033d8d139740abf9fccf0f60da7764df0e0b851`.

## Repository Structure and Contents
This repository is structured as follows.
* `proofs/`: All scripts relevant to the formal verification of the security of XMSS (both as standalone and as a component of SPHINCS+).
  * `FL_XMSS_TW.ec`
  * `WOTS_TW.ec`
  * `XMSS_TW.ec`