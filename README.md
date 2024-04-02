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
The experimental setup, test harnesses, and datasets are publicly available here.

[ARMOR-Evaluation](https://stonybrook365-my.sharepoint.com/:f:/g/personal/joyanta_debnath_stonybrook_edu/EmKh1KjaQABJghV2AaTT73sBqq7zULyzcMWG8Jpu06g6nw)





## Disclaimer

## Acknowledgements


## License


## Citation


## Contributors
