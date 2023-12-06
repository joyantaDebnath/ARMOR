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
  R3              & The \texttt{Serial} number MUST be a positive integer assigned by the CA to each certificate. Certificate users MUST be able to handle \texttt{Serial} number values up to 20 octets.                                                         \\ \hline
  R4              & The \texttt{Issuer} field MUST contain a non-empty distinguished name (DN).                                                                                                                                                         \\ \hline
  R5              & If the \texttt{Subject} is a CA (\eg, the \texttt{Basic Constraints} extension, is present and the value of \texttt{CA} is TRUE), then the \texttt{Subject} field MUST be populated with a non-empty distinguished name.                                      \\ \hline
  R6              & \texttt{Unique Identifiers} fields MUST only appear if the \texttt{Version} is 2 or 3. These fields MUST NOT appear if the \texttt{Version} is 1.                                                                                                     \\ \hline
  R7              & Where it appears, the \texttt{PathLenConstraint} field MUST be greater than or equal to zero.                                                                                                                                       \\ \hline
  R8              & If the \texttt{Subject} is a CRL issuer (\eg, the \texttt{Key Usage} extension, is present and the value of \texttt{CRLSign} is TRUE), then the \texttt{Subject} field MUST be populated with a non-empty distinguished name.                                 \\ \hline
  R9             & When the \texttt{Key Usage} extension appears in a certificate, at least one of the bits MUST be set to 1.                                                                                                                           \\ \hline
  R10             & If subject naming information is present only in the \texttt{Subject Alternative Name} extension , then the \texttt{Subject} name MUST be an empty sequence and the \texttt{Subject Alternative Name} extension MUST be critical.                                         \\ \hline
  R11             & If the \texttt{Subject Alternative Name} extension is present, the sequence MUST contain at least one entry.                                                                                                                                  \\ \hline
  R12             & If the \texttt{KeyCertSign} bit is asserted, then the \texttt{CA} bit in the \texttt{Basic Constraints} extension MUST also be asserted. If the \texttt{CA} boolean is not asserted, then the \texttt{KeyCertSign} bit in the \texttt{Key Usage} extension MUST NOT be asserted. \\ \hline
  R13             & A certificate MUST NOT include more than one instance of a particular \texttt{Extension}.                                                                                                                                           \\ \hline
  R14             & A certificate-using system MUST reject the certificate if it encounters a critical \texttt{Extension} it does not recognize or a critical \texttt{Extension} that contains information that it cannot process.                               \\ \hline
  R15             & A certificate policy OID MUST NOT appear more than once in a \texttt{Certificate Policies} extension.                                                                                                                               \\ \hline
  R16             & While each of these fields is optional, a \texttt{DistributionPoint} MUST NOT consist of only the \texttt{Reasons} field; either \texttt{distributionPoint} or  \texttt{CRLIssuer} MUST be present.                                                             \\ \hline
  R17             & The certificate \texttt{Validity} period includes the current time.                                                                                                                                                                 \\ \hline
                                                                                                                                                                                                                                     
  R18              & If a certificate contains both a \texttt{Key Usage} extension and an \texttt{Extended Key Usage} extension, then both extensions MUST be processed independently and the certificate MUST only be used for a purpose consistent with both extensions. If there is no purpose consistent with both extensions, then the certificate MUST NOT be used for any purpose. \\ \hline
  R19              & Conforming implementations may choose to reject all \texttt{Version} 1 and \texttt{Version} 2 intermediate CA certificates                                                                                                                                                                                                                                            . \\ \hline
  R20              & The \texttt{PathLenConstraint} field is meaningful only if the \texttt{CA} boolean is asserted and the \texttt{Key Usage} extension, if present, asserts the \texttt{KeyCertSign} bit. In this case, it gives the maximum number of non-self-issued intermediate certificates that may follow this certificate in a valid certification path.                                          \\ \hline
  R21              & For \texttt{DistributionPoint} field, if the certificate issuer is not the CRL issuer, then the \texttt{CRLIssuer} field MUST be present and contain the Name of the CRL issuer. If the certificate issuer is also the CRL issuer, then conforming CAs MUST omit the \texttt{CRLIssuer} field and MUST include the \texttt{distributionPoint} field.                                                                \\ \hline
  R22              & A certificate MUST NOT appear more than once in a prospective certification path.                                                                                                                                                                                                                                                                  \\ \hline
                                                                                                                                                                                                                                                                                                                                                                  
  R23              & Every non-leaf certificate in a chain must be a CA certificate.                                                                                                                                                                                                                                                                                                                       
  
                                                                                                                                                                                                                                                                                                                          \\ \hline     
  R24              & Certificate users MUST be prepared to process the \texttt{Issuer} distinguished name and \texttt{Subject} distinguished name fields to perform name chaining for certification path validation.                                                                                                                                                                      \\ \hline
  R25              & Validate whether the chain starts from a trusted CA.                                                                                                                                                                                                                                                                                         \\ \hline   
  R26              & Validate RSA signatures.                                                                                                                                                                                                                                                                                                                           \\ \hline
  R27              & Validate leaf certificate purpose against user's expected certificate purpose. \\ \hline                                                      
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


% \subsection{Examples of inconsistency, ambiguity, and under-specification}
% \label{sect:bad-spec}

% Perhaps unsurprisingly, the specification documents considered 
% are all written in English, 
% which is a natural language that is prone to inconsistency, ambiguity and 
% misinterpretation, and we have indeed observed several instances of 
% problematic clauses in the RFC 5280. Here we give a few illustrative examples.

% Regarding the requirements on serial number, in Section 4.1.2.2, RFC 5280 says:

% \quoteRFC{The serial number MUST be a positive integer assigned by the CA to 
% each certificate...CAs MUST force the serial Number to be a non-negative 
% integer...Non-conforming CAs may issue certificates with serial numbers that 
% are negative or zero. Certificate users SHOULD be prepared to gracefully handle 
% such certificates.}

% The first sentence is inconsistent with the last sentence: one excludes zero, 
% while 
% the other allows it.
% An 
% errata 
% on this has been 
% filed~\footnote{\url{https://www.rfc-editor.org/errata/eid3200}} back in 2012
% but at the time of writing it this does not seem to be included in any RFC 
% updates or clarifications.
%
%has a status of ``held for document updated'' and 
%is 
%not ``verified''.

% We now give an example of requirements that we consider to be ambiguous. 
% Regarding the contents of the CRL distribution points extension, in Section 
% 4.2.1.13, RFC 5280 says:

% \quoteRFC{
% 	A DistributionPoint consists of three fields,
% 	each of which is optional: distributionPoint, reasons, and cRLIssuer.
% 	While each of these fields is optional, a DistributionPoint MUST NOT
% 	consist of only the reasons field; either distributionPoint or
% 	cRLIssuer MUST be present.  If the certificate issuer is not the CRL
% 	issuer, then the cRLIssuer field MUST be present and contain the 
% 	Name
% 	of the CRL issuer.  If the certificate issuer is also the CRL issuer,
% 	then conforming CAs MUST omit the cRLIssuer field and MUST 
% 	include
% 	the distributionPoint field.
% }

% However, it is not immediately clear whether the \emph{\footnotesize 
% \textsf{either ... or ... }}
% clause should be 
% interpreted as an \emph{exclusive or} ($\oplus$), or should it be represented 
% with a \emph{logical or} ($\lor$). If one assumes the \emph{exclusive or} 
% interpretation, 
% then the \emph{\footnotesize \textsf{MUST omit}} clause in the 
% last sentence 
% of the quote seems to be somewhat redundant, as it is already implied by the 
% later
% \emph{\footnotesize \textsf{MUST include}} clause of the same sentence. 
% However, if \emph{logical or} is 
% indeed the correct interpretation, 
% that is, it is acceptable for both \texttt{distributionPoint} 
% and \texttt{cRLIssuer} to be present,
% then the \emph{\footnotesize \textsf{either 
% 		... or ...}} could have been written as \emph{\footnotesize \textsf{at 
% 		least one 
% 		of ... and ...}} to make it less confusing. 
% 	Such interpretation matters 
% 		because it 
% outlines the correct combinations of the fields that constitute the CRL 
% distribution points extension,
% %(in this case the 
% %CRL distribution points), 
% and affects what should be deemed as syntactically correct by the parser.

% Additional, we argue that RFC 5280 also suffers from the problem of 
% under-specification. Many clauses concerning the choice of values and options 
% are stipulated as \emph{producer rules} (\eg, \emph{\footnotesize 
% 	\textsf{conforming CAs must ...}}), but it is not immediately apparent 
% 	whether some or all of these should also be enforced by the consumer. In 
% 	some cases, RFC 5280 mentioned that certificate user should 
% 	\emph{\footnotesize \textsf{gracefully handle}} certain non-conforming 
% 	inputs, without really defining what needs to happen. Does that mean the 
% 	validation should not crash? Should the non-conforming inputs be rejected 
% 	or processed as normal? RFC 5280 is not explicit on those questions. 
% 	Similarly, it also did not make clear on what should the certificate user 
% 	do 
% 	in cases where the certificate itself violates the DER.



  % \subsection{Examples on RFC 5280 rules}
  %  \label{rfcrulex}
  % \begin{table}[h]
  % \setlength\extrarowheight{1.2pt}
  % \setlength{\tabcolsep}{1.5pt}
  % \centering
  % \sffamily\tiny
  %   \caption{(todo: update table) Example of producer and consumer rules\label{tab:prodconex}}
  % \vspace{-1.5em}
  % \sffamily\tiny
  %   \begin{tabular}{c||l||l}
  %   \textbf{Field} &
  %     \textbf{Syntactic Requirement} &
  %     \textbf{Semantic Requirement} \\ \hline
  %   Version &
  %     Version  $::=$  INTEGER  \{  v1(0), v2(1), v3(2)  \} &
  %     \begin{tabular}[c]{@@{}l@@{}}When extensions are used,\\ as expected  in this profile,\\ Version MUST be 3 (value is 2).\end{tabular} \\ \hline
  %   \begin{tabular}[c]{@@{}l@@{}}KeyUsage\\ Extension\end{tabular} &
  %     \begin{tabular}[c]{@@{}l@@{}}KeyUsage $::=$ BIT STRING \{\\ digitalSignature (0), nonRepudiation (1),\\ keyEncipherment (2), dataEncipherment (3),\\ keyAgreement (4), keyCertSign (5), cRLSign (6),\\ encipherOnly (7), decipherOnly (8) \}\end{tabular} &
  %     \begin{tabular}[c]{@@{}l@@{}}When the KeyUsage extension\\ appears in a  certificate, at least\\ one of the bits MUST be set to 1.\end{tabular} \\
  %   \end{tabular}
  %   \vspace{-1.1em}
  %   \end{table}

  
% \begin{table}[h]
%   \setlength\extrarowheight{1.2pt}
%   \setlength{\tabcolsep}{1.5pt}
%   \centering
%   \sffamily\tiny
%     \caption{(todo: update table) Example of syntactic and semantic requirements\label{tab:synsemex}}
%   \vspace{-1.5em}
%   \sffamily\tiny
%     \begin{tabular}{c||l||l}
%     \textbf{Field} &
%       \textbf{Syntactic Requirement} &
%       \textbf{Semantic Requirement} \\ \hline
%     Version &
%       Version  $::=$  INTEGER  \{  v1(0), v2(1), v3(2)  \} &
%       \begin{tabular}[c]{@@{}l@@{}}When extensions are used,\\ as expected  in this profile,\\ Version MUST be 3 (value is 2).\end{tabular} \\ \hline
%     \begin{tabular}[c]{@@{}l@@{}}KeyUsage\\ Extension\end{tabular} &
%       \begin{tabular}[c]{@@{}l@@{}}KeyUsage $::=$ BIT STRING \{\\ digitalSignature (0), nonRepudiation (1),\\ keyEncipherment (2), dataEncipherment (3),\\ keyAgreement (4), keyCertSign (5), cRLSign (6),\\ encipherOnly (7), decipherOnly (8) \}\end{tabular} &
%       \begin{tabular}[c]{@@{}l@@{}}When the KeyUsage extension\\ appears in a  certificate, at least\\ one of the bits MUST be set to 1.\end{tabular} \\
%     \end{tabular}
%     \vspace{-1.1em}
%     \end{table}