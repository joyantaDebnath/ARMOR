# CERES
This repository contains the official release of CERES library introduced in the paper titled *[On Re-engineering the X.509 PKI with Executable Specification for Better Implementation Guarantees](https://github.com/joyantaDebnath/CERES/blob/master/ccsfp468-debnath.pdf)* published in 2021 ACM Conference on Computer and Communications Security (ACM CCS 2021). 

## Table of Contents

- [CERES](#ceres)
  - [Table of Contents](#table-of-contents)
  - [What is CERES?](#what-is-ceres)
  - [Design Overview](#design-overview)
  - [Setup](#setup)
  - [Run](#run)
  - [Specification Consistency](#specification-consistency)
  - [Differential Testing](#differential-testing)
  - [DSL-based Parser Generation](#dsl-based-parser-generation)
  - [Datasets](#datasets)
  - [Known Setup Issues](#known-setup-issues)
  - [Disclaimer](#disclaimer)
  - [Acknowledgements](#acknowledgements)
  - [License](#license)
  - [Citation](#citation)
  - [Contributors](#contributors)

## What is CERES?
CERES is a high-assurance implementation of X.509 certificate chain validation logic (CCVL). This implementation is envisioned to be used as an oracle for checking noncompliance of a given CCVL implementation against the X.509 standard specification (*i.e.,* RFC 5280). One can also use CERES to validate a certificate chain to be used for configuring a TLS-enabled webserver. In addition, application developers can directly use CERES in their applications to delegate the task of X.509 certificate chain validation.

## Design Overview
CERES is realized from the following four logical modules: *Parser*, *Chain-builder*, *Driver*, and *Semantic-checker*. The *Parser* module takes as input the certificate chain to be validated as well as the trusted CA store, and returns the parse trees corresponding to the certificates. The *Chain-builder* module takes these parsed input certificates and forms candidate certificate chains. The *Semantic-checker* module then takes as input the current time, the semantic rules corresponding to the standard in Quantifier-Free First Order Logic, the ASTs corresponding to a candidate certificate chain, and the certificates in the trusted CA store, and then communicates with an "*SMT solver*" to check the assertions enforced by the semantic requirements as well as collect diagnostic information. The *Driver* module does the plumbing needed to combine the *Parser* and the *Semantic-checker* modules. Figure 1 shows the high-level design of CERES.

<p align = "center">
<img src="https://github.com/joyantaDebnath/CERES/blob/master/ceres-overview.png" width="400" height="430"></p>
<p align = "center">Figure 1- Realization of CERES</p>

## Setup
Currently, CERES is compatible with *Linux* distributions only, and the setup script `build-ceres.sh` is tested in Ubuntu OS (version >= 16). For other *Linux* distributions, users may need to modify the  script accordingly.

* To generate the CERES executable at `src/bin/ceres`, execute `build-ceres.sh`. User can optionally pass the location of trusted CA certificate store as a command-line argument in this script. Otherwise, the default *Linux* CA certificate store `/etc/ssl/certs/ca-certificates.crt` is used.
	```
	cd CERES/
	./build-ceres.sh
	```
* To check whether CERES executable is generated successfully, execute `test/test-ceres.sh`. This script needs a directory name containing one or more X.509 certificate chains (*e.g.,* `test/sample-certs/`) as a command-line argument.
	```
	cd CERES/test/
	./test-ceres.sh sample-certs/
	```
#### Dependencies
* Python3
* pip3
* pySMT
* CVC4
* LFSC proof-checker
* parsec.py
* PyInstaller
* GHC

Note that, `build-ceres.sh` script automatically downloads and installs all these dependencies in the system before generating the CERES executable. Also, it places the *CVC4* SMT solver and *LFSC* proof-checker at `~/.ceres/extras/`.


## Run
* To validate an input X.509 certificate chain (**.pem** or **.crt** encoded), run the CERES executable located at `src/bin/ceres` with the given chain.
	```
	cd src/bin/
	./ceres --input <input_cert_chain>
	```
* This is the complete list of command-line arguments supported by CERES executable.
	```
	--help                show manual
	--input INPUT         input certificate chain location
	--ca-store CA_STORE   CA certificate store location
	--check-purpose CHECK_PURPOSE1 CHECK_PURPOSE2 ... CHECK_PURPOSEn
	                      *** list of expected purposes of the leaf certificate: serverAuth, clientAuth, 
	                      codeSigning, emailProtection, timeStamping, OCSPSigning, digitalSignature,
	                      nonRepudiation, keyEncipherment, dataEncipherment, keyAgreement, keyCertSign,
	                      cRLSign, encipherOnly, decipherOnly ***
	--check-proof         check unsatisfiability proof
	--show-chain          show certificate chain details
	--check-spec          check specification consistency
	--dsl-parser          select "dsl-based" parser instead of "parser-combinator-based" parser
	--version             show current CERES version
	--asn1parse           only parse the input certificates
	--quick-semantic-check-sc
                       quick semantic check (no SMT solver) for a single certificate
	```

* The SMT-Libv2 file used by the *CVC4* SMT solver is saved in `~/.ceres/extras/CVC4/`.
* The proof checked by the *LFSC* proof-checker is saved in `~/.ceres/extras/LFSC/`.


## Specification Consistency
To check specification consistency, run CERES only with `check-spec` command-line argument. This will ask the user to provide a *length* for the symbolic certificate chain. Supported chain *length* values are from 1 to 32.

## Differential Testing
Sample scripts for differential testing of CERES, GnuTLS, OpenSSL, and mbedTLS implementations (CCVL) can be found  at `test/differntial-testing/`. 
* To run the sample differential testing script, execute the following commands.
	```
	cd test/differntial-testing/
	
	# build GnuTLS, OpenSSL, and mbedTLS libraries.
	./build-libs.sh
	
	# run sample differential testing script
	./diff-test.sh <directory_of_cert_chains>
	```
* The outputs of `diff-test.sh`  are saved in `test/differntial-testing/outputs/` for further analysis.

## DSL-based Parser Generation
The required files for automated generation of **dsl-based** parser can be found at `src/modules/parsers/dsl_based/grammar/`. User needs to run `generate-code.sh` passing a **.dsl** file that contains a grammar represented in the custom DSL discussed in the paper.
```
cd src/modules/parsers/dsl_based/grammar/
./generate-code.sh <input.dsl>
```

## Datasets
The certificate datasets used for the paper is publicly available [here](https://stonybrook365-my.sharepoint.com/:f:/g/personal/joyanta_debnath_stonybrook_edu/Esa7AR1nrghFtKCTw_w2xDkBegFDqJ48SkxAsYBVsb79UQ?e=eiI5Am). 
Please, email at <joyanta.debnath@stonybrook.edu> if the link doesn't work.

## Known Setup Issues
* LFSC proof checker requires  `>= GLIBCXX_3.4.26`. If its missing, following commands can be issued to update `GLIBCXX`.
	```
	 sudo add-apt-repository ppa:ubuntu-toolchain-r/test
	 sudo apt update
	 sudo apt install gcc-9
	 sudo apt install libstdc++6
	 
	 # check GLIBCXX version
	 strings /usr/lib/x86_64-linux-gnu/libstdc++.so.6 | grep GLIBCXX
	```
* GnuTLS (v3.6.15) may fail to build due to `Libnettle 3.4.1 was not found` error. In this case, user needs to upgrade `Libnettle` to build GnuTLS for the differential testing. We found this issue only in older Ubuntu machines (e.g., `<= Ubuntu 16.04`).

## Disclaimer

We follow a best-effort approach to manually interpret the RFC 5280 standard and translate it into a QFFOL formula. Although our empirical evaluation gives confidence about our interpretation's correctness, "*we do not claim our interpretation to be accurate*". Hence, our interpretation should not be considered as the official interpretation intended by the RFC authors. We want to emphasize that "*CERES has not been formally proven*" to be functionally correct with respect to the standard. This is why we refrain from referring to CERES as the reference implementation and instead refer to it as a high-assurance implementation.

In addition, we currently only support *RSA signature* verification. We also do not check certificate *revocation* status and do not match *hostnames*.


## Acknowledgements
We are grateful to [*Alan Mislove*](https://mislove.org/) for the initial idea of using measurements to drive our formalization efforts of the X.509 standard. 
We are also thankful to [*Cesare Tinelli*](https://homepage.cs.uiowa.edu/~tinelli/) for his helpful discussions on attribute grammar and all things SMT. This work was supported by the NSF Grant CNS-2006556.

## License
This work is licensed under a Creative Commons Attribution International 4.0 License.

## Citation
Please, use the following *bibtex* for citing this work.

```
@inproceedings{debnath2021ceres,
	author = {Debnath, Joyanta and Chau, Sze Yiu and Chowdhury, Omar},
	title = {On Re-engineering the X.509 PKI with Executable Specification for Better Implementation Guarantees},
	year = {2021},
	isbn = {9781450384544},
	publisher = {Association for Computing Machinery},
	address = {New York, NY, USA},
	url = {https://doi.org/10.1145/3460120.3484793},
	doi = {10.1145/3460120.3484793},
	booktitle = {Proceedings of the 2021 ACM SIGSAC Conference on Computer and Communications Security},
	pages = {17},
	numpages = {},
	keywords = {PKI, X.509 Certificate, Network Security, SSL/TLS Protocol, Differential Testing, Authentication, SMT Solver},
	location = {Virtual Event, Republic of Korea},
	series = {CCS '21}
}
```

## Contributors
Please, feel free to contact one of us if you have any questions.
* [Joyanta Debnath](https://www3.cs.stonybrook.edu/~jdebnath/)
* [Omar Chowdhury](https://www3.cs.stonybrook.edu/~omar/)
* [Sze Yiu Chau](https://szeyiuchau.github.io/)

