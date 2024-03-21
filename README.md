

# Directory

-   Paper (full version): [dist/index.pdf](dist/index.pdf)
-   Source (clickable HTML): [html/Everything.html](html/Everything.html)
    
    Use the "View raw" option at the top left
    
    -   [PEM](html/Armor.Data.PEM.html), [X.509](html/Armor.Data.X509.html), and [X.690-DER](html/Armor.Data.X690-DER.html) parsers modules
    -   Generic soundness and completeness results:
        <html/Armor.Grammar.Parser.Completeness.html>
    -   [Chain builder](html/Armor.Data.X509.Semantic.Chain.Builder.html)
    -   Semantic checks
        -   [Certificate](html/Armor.Data.X509.Semantic.Cert.html)
        -   [Chain](html/Armor.Data.X509.Semantic.Chain.html)


## Code listings used in the paper

-   [`Fin`](html/Data.Fin.Base.html) datatype (Figure 3):

-   [Base64 `encode`, `decode` and proofs](html/Armor.Binary.Base64EncDec.html) (Figure 4):

-   [`IntegerValue`](html/Armor.Data.X690-DER.Int.TCB.html) type (Figure 5):

-   [`Raw` and `NonMalleable`](html/Armor.Grammar.Definitions.NonMalleable.Base.html)

-   [`Success` and `Parser`](html/Armor.Grammar.Parser.Core.html) (Figures 6, 7)
    
    Note that `Parser` is parameterized by type-level function `M : Set ->
         Set`, and that `Dec` does not appear explicitly. `M` is almost always
    instantiated with ``Logging `circ` Dec``

-   [`Sound`, `Complete`, and `StronglyComplete`](html/Armor.Grammar.Parser.Completeness.html) (Figure 8, 9)

-   [`Chain`](html/Armor.Data.X509.Semantic.Chain.TCB.html) (Figure 10)

-   [`chainUnique`](html/Armor.Data.X509.Semantic.Chain.Properties.html) (Figure 11)

-   [`buildChains` and `buildChainsComplete`](html/Armor.Data.X509.Semantic.Chain.Builder.html) (Figure 12)

-   [`R1`](html/Armor.Data.X509.Semantic.Cert.R1.html) semantic check

-   [`R3`](html/Armor.Data.X509.Semantic.Chain.R23.html) semantic check


# Building

**Prerequisites**

-   Ubuntu 20.04 system (one author uses Linux Mint 20)
-   Git (`git`)
-   Python 3 (`python3`) (tested with Python 3.8.10)
-   pip (`python3-pip`) (tested with pip 22.0.2)

```
sudo apt install git python3 python3-pip
```

**Update all submodules**
```
git submodule update --init --recursive --remote
```
This will update the `src/` folder with `armor-agda` and `armor-driver`.

**(Optional) Type-check and compile the modules written in Agda**
```
cd src/armor-agda/src
agda -c Armor/Main.agda +RTS -M8G -RTS
cd ../../..
```
This creates a binary called `Main` in `src/armor-agda`, which needs to be copied to `src/armor-driver`.

```
cp src/armor-agda/src/Main src/armor-driver/armor-bin
```

**Install the driver module written in Python**
```
cd src/armor-driver
./install.sh
cd ../..
```
An executable binary `armor` will be placed in `src/armor-driver/bin/`


# Running
`python3 src/armor-driver/driver.py --chain <pem/crt certificate chain> --trust_store <pem/crt trusted CA store>`

or

`./src/armor-driver/bin/armor --chain <pem/crt certificate chain> --trust_store <pem/crt trusted CA store>`


# Experimental Setup and Dataset
The experimental setup, test harnesses, and datasets are publicly available here.
[ARMOR-Evaluation](https://stonybrook365-my.sharepoint.com/:f:/g/personal/joyanta_debnath_stonybrook_edu/EmKh1KjaQABJghV2AaTT73sBqq7zULyzcMWG8Jpu06g6nw)


## Download (Anonymous Repo)

Follow the instructions here:
<https://github.com/fedebotu/clone-anonymous-github>

The hosting site for the anonymous repo only permits 350 file downloads every
15 minutes. Run the Python downloader multiple times to download all of our
source files; the downloader tracks which files needs to be re-downloaded on
subsequent invocations.

To better track the progress of your download, invoke the Python script with
the `--verbose True` flag, e.g.,

    python3 src/download.py --url https://anonymous.4open.science/r/armor-full-version --verbose True


## Stack (`haskell-stack`)

    sudo apt install haskell-stack
    stack update
    stack upgrade

**Remark:** This step will create ~/.local/bin if it does not exist. If so,
then (on some systems) to ensure that this directory is listed in your $PATH
variable you can log off and log back in again.


## Python

With `pip`, install

-   `pem` (tested with version 21.2.0)

    pip install pem


## Agda

Armor uses Agda v2.6.2.2. To install this from source, choose a directory
listed in your $PATH environment variable (such as `~/.local/bin`) for the
Agda executable. We will refer to this as $AGDAEXECDIR in what follows:
**please replace all occurrences of $AGDAEXECDIR with this, or set this as
an environment variable**

Open a terminal in some working directory and perform the following steps. 

1.  Install dependencies for Agda
    
        sudo apt install zlib1g-dev libncurses5-dev
2.  Checkout Agda source repository
    
        git clone --depth 1 --branch v2.6.2.2 https://github.com/agda/agda.git
        cd agda
3.  Build Agda (this will take a while: stack may need to install the
    specific GHC and the Haskell base libraries, and then building Agda itself
    takes a long time).
    
        stack install --stack-yaml stack-8.8.4.yaml --local-bin-path $AGDAEXECDIR

4.  Confirm Agda is installed correctly
    
    The result of `agda --version` should be
    
        Agda version 2.6.2.2-442c76b


## ARMOR

From the root of the repository, navigate to `armor` and build the Agda modules

    cd armor
    make all

Note that this command is written to use `stack --compiler ghc-8.8.4 exec
   ghc` to compile the generated Haskell source files. If you built Agda from
source, this should already be installed.


# Running

After building, perform the following steps to verify Armor was built correctly

1.  Change directory to `armor-driver` (if you built Armor correctly,
    `armor-bin` should now be in this directory).
    
        cd armor-driver

2.  Invoke the driver with `python3` directly
    
        python3 driver.py --chain certs/facebook-com-chain.pem
    
    The expected result is for all tests up to R17 should pass, with R17
    (certificate validity) failing.

