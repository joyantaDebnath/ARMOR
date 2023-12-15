

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

-   `Fin` datatype (Figure 3):
    
    <html/Data.Fin.Base.html>
-   Base64 `encode`, `decode` and proofs (Figure 4):
    
    <html/Armor.Binary.Base64EncDec.html>
-   `IntegerValue` type (Figure 5):
    
    <html/Armor.Data.X690-DER.Int.TCB.html>

-   `Raw` and `NonMalleable`
    
    <html/Armor.Grammar.Definitions.NonMalleable.Base.html>

-   `Success` and `Parser` (Figures 6, 7)
    
    <html/Armor.Grammar.Parser.Core.html>
    
    Note that `Parser` is parameterized by type-level function `M : Set ->
         Set`, and that `Dec` does not appear explicitly. `M` is almost always
    instantiated with ``Logging `circ` Dec``

-   `Sound`, `Complete`, and `StronglyComplete` (Figure 8, 9)
    
    <html/Armor.Grammar.Parser.Completeness.html>

-   `Chain` (Figure 10)
    
    <html/Armor.Data.X509.Semantic.Chain.TCB.html>

-   `chainUnique` (Figure 11)
    
    <html/Armor.Data.X509.Semantic.Chain.Properties.html>

-   `buildChains` and `buildChainsComplete` (Figure 12)
    
    <html/Armor.Data.X509.Semantic.Chain.Builder.html>

-   `R1` semantic check
    
    <html/Armor.Data.X509.Semantic.Cert.R1.html>

-   `R3` semantic check
    
    <html/Armor.Data.X509.Semantic.Chain.R23.html>

