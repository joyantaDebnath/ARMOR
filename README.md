

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
-   Git
-   Python 3 (tested with Python 3.8.10)
-   pip (tested with pip 20.0.2)


## Stack (`haskell-stack`)

    sudo apt install haskell-stack
    stack update
    stack upgrade


## Agda

Armor uses Agda v2.6.2.2. To install this from source, choose a directory
listed in your $PATH environment variable (such as `~/.local/bin`) for the
Agda executable. We will refer to this as $AGDA<sub>EXEC</sub><sub>DIR</sub> in what follows:
**please replace all occurrences of $AGDA<sub>EXEC</sub><sub>DIR</sub> with this, or set this as
an environment variable**

Open a terminal in some working directory and perform the following steps. 

1.  Checkout Agda source repository
    
        git clone --depth 1 --branch v2.6.2.2 https://github.com/agda/agda.git
        cd agda
2.  Build Agda (this will take a while: stack may need to install the
    specific GHC and the Haskell base libraries, and then building Agda itself
    takes a long time).
    
        stack install --stack-yaml stack-8.8.4.yaml --local-bin-path $AGDA_EXEC_DIR

3.  Confirm Agda is installed correctly
    
    The result of `agda --version` should be
    
        Agda version 2.6.2.2-442c76b

