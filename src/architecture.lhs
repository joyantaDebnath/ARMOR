
\section{Design and Implementation of ARMOR}

\subsection{Overview on Agda}
Agda is a powerful and expressive programming language that combines functional programming and formal verification. At its core, Agda is a dependently-typed functional programming language, which allows types to be predicated on values. This capability helps express rich properties in types and ensures that the programs conform to these properties. In other words, if a program compiles, it is also proven to meet the specifications described by the types. Another important feature is that Agda supports interactive theorem proving. Programmers can write proofs interactively by filling in parts of proofs, referred to as ``proof holes'' while the Agda compiler checks that every step is correct. This makes Agda a powerful tool for ensuring the correctness of an implementation. Note that we can generate an executable binary of the implementation by first compiling the Agda source code into Haskell and then using a Haskell compiler to compile the generated Haskell code into a binary. 

As a simple example of Agda's syntax, consider representing the Agda boolean values in their X.690 DER counterparts. As per the Basic Encoding Rules (BER), boolean values must comprise a singular octet, with False denoted by setting all bits to 0 and True denoted by setting at least one bit to 1. The DER further mandates that the value True is signified by setting all bits to 1. We capture these requirements of DER boolean in Agda by defining a type that holds not only the boolean value and its 8-bit numerical representation but also a proof that this representation is correct. To further illustrate, let us look at the Agda code below. 

\begin{figure}[h]
  \centering
  \begin{code}
      data BoolRep : Bool -> UInt8 -> Set where
        falser : BoolRep false (UInt8.fromN 0)
        truer  : BoolRep true (UInt8.fromN 255)


      record BoolValue (@0 bs : List UInt8) : Set where
        constructor mkBoolValue
        field
          v     : Bool
          @0 b  : UInt8
          @0 vr : BoolRep v b
          @0 bseq : bs == [ b ]
    \end{code}
    \label{code1}
    \caption{Agda example for representing DER boolean type}
  \end{figure}

Here, |BoolRep| is a dependent type representing a binary relationship between Agda |Bool| values (\ie, true, false) and |UInt8| (\ie, 8-bit unsigned integers or octet values stipulated by the X.690 DER), where the |falser| constructor associates the false boolean value with 0, and the |truer| constructor associates true with 255. The function |UInt8.fromN| transforms a non-negative unbounded integer into its equivalent |UInt8| representation. It is important to note that this transformation is contingent upon Agda's ability to automatically verify that the provided number is less than 256. Also, the keyword |Set| (referred to as the type of types) defines the type of |BoolRep|, indicating that |BoolRep| maps specific pairs of |Bool| and |UInt8| values to unique types. Subsequently, we can construct a dependent and parameterized record type, |BoolValue|, to represent the boolean value defined by X.690. This record type, essentially a predicate over byte-strings, includes the boolean value |v|, its byte-string representation |b|, a proof |vr| that |b| is the correct representation of |v|, and a proof |bseq| that the byte-string representation |bs| of this grammatical terminal is a singleton list containing |b|. The |@0| annotations applied to types and fields specify that these values are erased at runtime to minimize execution overhead and to mark parts of the formalization used solely for verification purposes. In short, |BoolRep| verifies the correct mapping between boolean values and their numerical representations, while |BoolValue| holds the boolean value, its numerical representation, and the proof of the correctness of this representation, returned by the |BoolRep|.



\subsection{Overall Architecture} 
The X.509 certificate chain validation process can be decomposed in the following steps. The process begins with receiving the end-user and associative CA certificates, typically in PEM format, which is the most-used and recognized certificate format and represented as ASCII (Base64) encoded data. In addition, all the certificates (end-user and CA) can be included in one PEM file. These PEM certificates are then processed through a Base64 decoder to convert into DER binary format for each certificate. These DER bytes are then parsed to obtain the internal data representation of each certificate. This structured representation provides detailed information contained within each certificate and has a one-to-one correspondence with the ASN.1 certificate representation. The parsed certificates are then organized to construct a valid certification path. This involves placing the given certificates in the correct order, beginning with the end-user certificate and leading up to the root CA certificate. Note that this chain-building process can return multiple valid certificate chains since a single certificate can be cross-signed by more than one CA. Each candidate certificate chain then undergoes semantic validation, where various checks are performed on different fields of a certificate and interrelationships among different certificates. If at least one candidate certificate chain passes the semantic validation, the certificate chain validation returns True otherwise returns False.

\subsection{Trusted Computing Base}

\subsection{Implementation Details}