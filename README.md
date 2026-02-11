# Machine-Checked Security for XMSS as in RFC 8391 and SPHINCS⁺
This repository accompanies the paper "Machine-Checked Security for XMSS as in
RFC 8391 and SPHINCS⁺", authored by Manuel Barbosa, François Dupressoir,
Benjamin Grégoire, Andreas Hülsing, Matthias Meijers, and Pierre-Yves Strub. The
original (proceeding's) version of the paper can be found
[here](https://link.springer.com/chapter/10.1007/978-3-031-38554-4_14); the most
recent version of the paper can be found
[here](https://eprint.iacr.org/2023/408).  

This repository comprises EasyCrypt scripts primarily aimed at the formal
verification of the security of XMSS as a standalone construction &mdash;
specified in [RFC 8391](https://www.rfc-editor.org/rfc/rfc8391). Due to the
modular approach taken in the formal verification, the scripts contain an
independent formal verification of the fix of the security proof of SPHINCS⁺
presented in [Recovering the Tight Security Proof of
SPHINCS⁺](https://link.springer.com/chapter/10.1007/978-3-031-22972-5_1),
validating the remediation of the flaw in the original proof and paving the way
for a complete formal verification of SPHINCS⁺. Furthermore, again due to the
modular approach, the scripts contain an independent formal verification of a
security property of XMSS as a component of SPHINCS⁺.  

The most recent version of EasyCrypt that has been confirmed to verify the scripts in
this repository corresponds to [release
2026.02](https://github.com/EasyCrypt/easycrypt/releases/tag/r2026.02) with SMT
provers Z3 4.13.4 and Alt-Ergo 2.6.0 (as specified in `easycrypt.project`).

## Repository Structure and Contents
This repository is structured as follows (excluding versioning- and build-related material).  
* `proofs/`: All scripts relevant to the formal verification of the security of
  XMSS (both as standalone and as a component of SPHINCS⁺) and the fix of the
  security proof of SPHINCS⁺.  
    * `DigitalSignatures.eca`: (Library) Generically defines signature schemes
      (both stateless and key-updating) and their security notions.  
    * `DigitalSignaturesROM.eca`: (Library) Similar to `DigitalSignatures.eca`,
      except that it defines everything with respect to a random oracle (this is
      for proofs in the random oracle model).  
    * `EUFRMA_Interactive_Equiv.ec`: Demonstrates equivalence between the regular
      EUF-RMA property for digital signature schemes and its (auxiliary)
      interactive variant.  
    * `FL_XMSS_TW.ec`: Provides the context, specification, and proofs concerning
      fixed-length XMSS-TW.  
    * `HashAddresses.eca`: Generically defines hash addresses and some of their
      properties (not a proper library: relatively minimal and primarily designed
      for use in this and related projects).  
    * `HashThenSign.eca`: Demonstrates generic results concerning the
      hash-then-sign paradigm for digital signature schemes. 
    * `KeyedHashFunctions.eca`: (Library) Generically defines keyed hash
      functions and their properties.  
    * `Reprogramming.ec`: Demonstrates a generic bound for the reprogramming
      technique (for a random oracle).  
    * `TweakableHashFunctions.eca`: (Library) Generically defines tweakable hash
      functions and their properties.  
    * `WOTS_TW.ec`: Provides the context, specification, and proofs concerning
      WOTS-TW (with an abstract encoding).  
    * `WOTS_TW_Checksum.ec`: Defines the concrete encoding used in WOTS-TW and
      demonstrates that the proofs from `WOTS_TW.ec` still hold true when using
      this encoding.  
    * `XMSS_TW.ec`: Provides the context, specification, and proofs concerning
      XMSS-TW.  
* `config/`: Configuration and test files  
  * `tests.config`: Specifies tests  
* `easycrypt.project`: EasyCrypt project file, specifying SMT prover versions and timeout  

## Building, Running, and Testing

You can run this development either via Docker or natively (if you have the
correct EasyCrypt + solver installation).

### Prerequisites

- Docker approach:  
  - [Docker Engine](https://docs.docker.com/engine/install), installed and running.
- Native approach:  
  - [EasyCrypt (release r2026.02)](https://github.com/EasyCrypt/easycrypt/tree/r2026.02), installed and configured with the solvers listed below.
  - Alt-Ergo 2.6.
  - Z3 4.13.4.

For the native approach, the [EasyCrypt README.md for
r2026.02](https://github.com/EasyCrypt/easycrypt/blob/r2026.02/README.md)
describes installation and solver configuration. More detailed instructions are
provided in the
[INSTALL.md](https://github.com/EasyCrypt/easycrypt/blob/r2026.02/INSTALL.md).

### Docker

Run all tests inside the Docker environment:
```shell
make docker-check
```

To explore and interact with the repository inside the container, start an interactive shell:
```shell
make docker-shell
```

This drops you into a shell inside the Docker image with the repository as the
working directory. From there you can run the same commands as in the native
approach (see below).

### Native

Run all tests:
```shell
make check
```

Beyond running the tests, this also stores test reports in the `reports/`
directory (automatically created on the first test run).

Remove EasyCrypt’s cached verification artifacts (.eco files):
```shell
make clean
```

Additionally remove the reports/ directory:
```shell
make clobber
```

### Help with Make
All of the above uses `make` and, hence, goes through the repository's
`Makefile`. To list available targets and brief descriptions:
```shell
make help
```

You can override `make` variables (see `Makefile`), for
example to tweak the setup or speed up testing by increasing parallelism.
However, be aware that changing these parameters can affect test stability
(e.g., different degrees of parallelism can trigger solver/time-out failures),
so unexpected failures may occur when deviating from the default settings.
