# ARMOR
This repository contains the official release of **ARMOR: A Formally Verified Implementation of X.509 Certificate Chain Validation**.

- [Paper (full version)](resources/armor-full-paper.pdf)

## Building Instructions

### Prerequisites
-   Ubuntu 20.04 system (one author uses Linux Mint 20)
-   Git (`git`)
-   Python 3 (`python3`) (tested with Python 3.8.10)
-   pip (`python3-pip`) (tested with pip 22.0.2)

```
sudo apt install git python3 python3-pip
```
#### Stack (`haskell-stack`)
```
sudo apt install haskell-stack
stack update
stack upgrade
```
**Remark:** This step will create ~/.local/bin if it does not exist. If so,
then (on some systems) to ensure that this directory is listed in your $PATH
variable you can log off and log back in again.

#### Agda

Armor uses Agda v2.6.2.2. To install this from source, choose a directory
listed in your $PATH environment variable (such as `~/.local/bin`) for the
Agda executable. We will refer to this as $AGDAEXECDIR in what follows:
**please replace all occurrences of $AGDAEXECDIR with this, or set this as
an environment variable**

Open a terminal in some working directory and perform the following steps. 

1.  Install dependencies for Agda
    
       `sudo apt install zlib1g-dev libncurses5-dev`
   
2.  Checkout Agda source repository

    ```
    git clone --depth 1 --branch v2.6.2.2 https://github.com/agda/agda.git
    cd agda
    ```
    
4.  Build Agda (this will take a while: stack may need to install the
    specific GHC and the Haskell base libraries, and then building Agda itself
    takes a long time).
    
    `stack install --stack-yaml stack-8.8.4.yaml --local-bin-path $AGDAEXECDIR`

5.  Confirm Agda is installed correctly
    
    The result of `agda --version` should be
    
    `Agda version 2.6.2.2-442c76b`

### Build and Install
`./install.sh`

An executable binary `armor` will be placed in `src/armor-driver/bin/`.

### Clean Up
`./cleanup.sh`

## Running 

- Invoke the driver with `python3` directly.

`python3 src/armor-driver/driver.py --chain <input chain> --trust_store <input CA store> [--purpose <expected purpose>]`

- If you built ARMOR correctly, executable `armor` can be invoked.

`./src/armor-driver/bin/armor --chain <input chain> --trust_store <input CA store> [--purpose <expected purpose>]`

**List of Supported Purposes**

`serverAuth`, `clientAuth`, `codeSigning`, `emailProtection`, `timeStamping`, `ocspSigning`


## Experimental Setup and Dataset
[Experimental Setup and Test Harnesses](evaluation/Diff_test_setup/)

[End to End Application](evaluation/End_to_end_application/)

[Datasets](https://drive.google.com/file/d/1OQI9LlvvQI7kvkH9Enr2U2CKTUiJg5qU/view?usp=sharing)

[Example Certificte Chains to Trigger Discrepancies](evaluation/Discrepancy_triggering_inputs/)

## Disclaimer
We follow a best-effort approach to manually interpret the RFC 5280 standard. Although our empirical evaluation gives confidence about our interpretation's correctness, "we do not claim our interpretation to be accurate". Hence, our interpretation should not be considered as the official interpretation intended by the RFC authors. In addition, we currently only support RSA signature verification. We also do not check certificate revocation status and do not match hostnames.

## Copyright
© 2024, Joyanta Debnath. Under license to IEEE.

## Citation (BibTex)
[Publication Link](https://doi.ieeecomputersociety.org/10.1109/SP54263.2024.00220)

@INPROCEEDINGS {10646820,
author = { Debnath, Joyanta and Jenkins, Christa and Sun, Yuteng and Chau, Sze Yiu and Chowdhury, Omar },
booktitle = { 2024 IEEE Symposium on Security and Privacy (SP) },
title = {{ ARMOR: A Formally Verified Implementation of X.509 Certificate Chain Validation }},
year = {2024},
volume = {},
ISSN = {},
pages = {1462-1480},
keywords = {Privacy;Runtime;Accuracy;Buildings;Semantics;Software;Libraries},
doi = {10.1109/SP54263.2024.00220},
url = {https://doi.ieeecomputersociety.org/10.1109/SP54263.2024.00220},
publisher = {IEEE Computer Society},
address = {Los Alamitos, CA, USA},
month =May}

## Contacts
Please, feel free to contact one of us if you have any questions.
* [Joyanta Debnath](https://joyantadebnath.github.io/homepage/)
* [Christa Jenkins](https://cwjnkins.github.io/)
* [Omar Chowdhury](https://www3.cs.stonybrook.edu/~omar/)
