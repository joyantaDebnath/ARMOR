\appendix
\section{Appendix}

\begin{table*}[h]
  \setlength\extrarowheight{1.2pt}
  \setlength{\tabcolsep}{1.5pt}
  \centering
  \sffamily\scriptsize
  \caption{Semantic restrictions enforced by \armor}
  \sffamily\scriptsize
  \begin{tabularx}{0.8\textwidth}{||c||X||}
  \hline
  \textbf{Name} & \textbf{Description}                                                                                                                                                                                              \\ \hline
  R1              & \texttt{SignatureAlgorithm} field MUST contain the same algorithm identifier as the \texttt{Signature} field in the sequence \texttt{TbsCertificate}.                                                                                                 \\ \hline
  R2              & \texttt{Extension} field MUST only appear if the \texttt{Version} is 3                                                                                                                                                                      . \\ \hline
  R3              & At a minimum, conforming implementations MUST recognize \texttt{Version} 3 certificates. Generation of \texttt{Version} 2 certificates is not expected by implementations based on this profile.                                             \\ \hline
  R4              & The \texttt{Serial} number MUST be a positive integer assigned by the CA to each certificate. Certificate users MUST be able to handle \texttt{Serial} number values up to 20 octets.                                                         \\ \hline
  R5              & The \texttt{Issuer} field MUST contain a non-empty distinguished name (DN).                                                                                                                                                         \\ \hline
  R6              & If the \texttt{Subject} is a CA (\eg, the \texttt{Basic Constraints} extension, is present and the value of \texttt{CA} is TRUE), then the \texttt{Subject} field MUST be populated with a non-empty distinguished name.                                      \\ \hline
  R7              & \texttt{Unique Identifiers} fields MUST only appear if the \texttt{Version} is 2 or 3. These fields MUST NOT appear if the \texttt{Version} is 1.                                                                                                     \\ \hline
  R8              & Where it appears, the \texttt{PathLenConstraint} field MUST be greater than or equal to zero.                                                                                                                                       \\ \hline
  R9              & If the \texttt{Subject} is a CRL issuer (\eg, the \texttt{Key Usage} extension, is present and the value of \texttt{CRLSign} is TRUE), then the \texttt{Subject} field MUST be populated with a non-empty distinguished name.                                 \\ \hline
  R10             & When the \texttt{Key Usage} extension appears in a certificate, at least one of the bits MUST be set to 1.                                                                                                                           \\ \hline
  R11             & If subject naming information is present only in the \texttt{Subject Alternative Name} extension , then the \texttt{Subject} name MUST be an empty sequence and the \texttt{Subject Alternative Name} extension MUST be critical.                                         \\ \hline
  R12             & If the \texttt{Subject Alternative Name} extension is present, the sequence MUST contain at least one entry.                                                                                                                                  \\ \hline
  R13             & If the \texttt{KeyCertSign} bit is asserted, then the \texttt{CA} bit in the \texttt{Basic Constraints} extension MUST also be asserted. If the \texttt{CA} boolean is not asserted, then the \texttt{KeyCertSign} bit in the \texttt{Key Usage} extension MUST NOT be asserted. \\ \hline
  R14             & A certificate MUST NOT include more than one instance of a particular \texttt{Extension}.                                                                                                                                           \\ \hline
  R15             & A certificate-using system MUST reject the certificate if it encounters a critical \texttt{Extension} it does not recognize or a critical \texttt{Extension} that contains information that it cannot process.                               \\ \hline
  R16             & A certificate policy OID MUST NOT appear more than once in a \texttt{Certificate Policies} extension.                                                                                                                               \\ \hline
  R17             & While each of these fields is optional, a \texttt{DistributionPoint} MUST NOT consist of only the \texttt{Reasons} field; either \texttt{distributionPoint} or  \texttt{CRLIssuer} MUST be present.                                                             \\ \hline
  R18             & The certificate \texttt{Validity} period includes the current time.                                                                                                                                                                 \\ \hline
  R19              & Conforming implementations may choose to reject all \texttt{Version} 1 and \texttt{Version} 2 intermediate CA certificates                                                                                                                                                                                                                                            . \\ \hline                                                               \\ \hline
  R20              & A certificate MUST NOT appear more than once in a prospective certification path.                                                                                                                                                                                                                                                                  \\ \hline
  R21              & Certificate users MUST be prepared to process the \texttt{Issuer} distinguished name and \texttt{Subject} distinguished name fields to perform name chaining for certification path validation.                                                                                                                                                                      \\ \hline
  R22              & Validate whether root CA certificate is trusted by system.                                                                                                                                                                                                                                                                                         \\ \hline
  R23              & Validate RSA signatures.                                                                                                                                                                                                                                                                                                                           \\ \hline                                                                                                                                                                                                                                                                                                   
                                                                                                                                                                                                                                                                                                            
  \end{tabularx}
  \label{rules}
  \end{table*}
  
  
  % \begin{table*}[h]
  % \setlength\extrarowheight{1.2pt}
  % \setlength{\tabcolsep}{1.5pt}
  % \centering
  % \sffamily\scriptsize
  % \caption{Semantic properties for a chain of X.509 certificates. [TODO : Fix]}
  % CCP = Certificate Chain Property
  % \vspace{0.5em}
  % \sffamily\scriptsize
  % \begin{tabularx}{\textwidth}{||c||X||}
  % \hline
  % \textbf{Constraint} & \textbf{Description}                                                                                                                                                                                                                                                                                                                      \\ \hline
  % CCP1              & If a certificate contains both a \texttt{Key Usage} extension and an \texttt{Extended Key Usage} extension, then both extensions MUST be processed independently and the certificate MUST only be used for a purpose consistent with both extensions. If there is no purpose consistent with both extensions, then the certificate MUST NOT be used for any purpose. \\ \hline
  % CCP2              & Conforming implementations may choose to reject all \texttt{Version} 1 and \texttt{Version} 2 intermediate CA certificates                                                                                                                                                                                                                                            . \\ \hline
  % CCP3              & The \texttt{PathLenConstraint} field is meaningful only if the \texttt{CA} boolean is asserted and the \texttt{Key Usage} extension, if present, asserts the \texttt{KeyCertSign} bit. In this case, it gives the maximum number of non-self-issued intermediate certificates that may follow this certificate in a valid certification path.                                          \\ \hline
  % CCP4              & For \texttt{DistributionPoint} field, if the certificate issuer is not the CRL issuer, then the \texttt{CRLIssuer} field MUST be present and contain the Name of the CRL issuer. If the certificate issuer is also the CRL issuer, then conforming CAs MUST omit the \texttt{CRLIssuer} field and MUST include the \texttt{distributionPoint} field.                                                                \\ \hline
  % CCP5              & A certificate MUST NOT appear more than once in a prospective certification path.                                                                                                                                                                                                                                                                  \\ \hline
  % CCP6              & Certificate users MUST be prepared to process the \texttt{Issuer} distinguished name and \texttt{Subject} distinguished name fields to perform name chaining for certification path validation.                                                                                                                                                                      \\ \hline
  % CCP7              & Validate whether root CA certificate is trusted by system.                                                                                                                                                                                                                                                                                         \\ \hline
  % CCP8              & Validate RSA signatures.                                                                                                                                                                                                                                                                                                                           \\ \hline
  % CCP9              & Validate leaf certificate purpose against user's expected certificate purpose.                                                                                                                                                                                                                                                                                                                           \\ \hline
  % CCP10              & Every non-leaf certificate in a chain must be a CA certificate.                                                                                                                                                                                                                                                                                                                           \\ \hline
  % \end{tabularx}
  % \label{ccp}
  % \end{table*}