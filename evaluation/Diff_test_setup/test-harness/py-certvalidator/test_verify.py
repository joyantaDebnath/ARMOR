from asn1crypto import pem
from certvalidator import CertificateValidator, ValidationContext
import sys

# Check if enough arguments are provided
if len(sys.argv) < 3:
    print("0 - Usage: python verify.py <Certificate Chain file> <Trusted CA file> [CRL file]")
    sys.exit(0)

entity_path = sys.argv[1]
ca_path = sys.argv[2]
crl_path = sys.argv[3] if len(sys.argv) > 3 else None  # CRL is optional

end_entity_cert = None
other_certs = []
trust_roots = []
crls = []

# Load entity certificate and intermediate certificates
try:
    with open(entity_path, 'rb') as f:
        for type_name, headers, der_bytes in pem.unarmor(f.read(), multiple=True):
            if end_entity_cert is None:
                end_entity_cert = der_bytes
            else:
                other_certs.append(der_bytes)
except Exception as e:
    print(f"0 - Error loading entity certificate: {e}")
    sys.exit(0)

# Load CA certificates
try:
    with open(ca_path, 'rb') as f:
        for _, _, der_bytes in pem.unarmor(f.read(), multiple=True):
            trust_roots.append(der_bytes)
except Exception as e:
    print(f"0 - Error loading CA certificates: {e}")
    sys.exit(0)

# Load CRLs (only if provided)
if crl_path:
    try:
        with open(crl_path, 'rb') as f:
            for _, _, der_bytes in pem.unarmor(f.read(), multiple=True):
                crls.append(der_bytes)
        revocation_mode = 'require'  # Perform CRL validation
    except Exception as e:
        print(f"0 - Error loading CRLs: {e}")
        sys.exit(0)
else:
    revocation_mode = 'hard-fail'  # Ignore CRLs if not provided

# Create validation context
context = ValidationContext(
    trust_roots=trust_roots,
    other_certs=other_certs,
    crls=crls,
    revocation_mode=revocation_mode  # CRL check only if CRL is provided
)

# Validate the certificate
validator = CertificateValidator(end_entity_cert, validation_context=context)

try:
    validator._validate_path()  # Path validation

    # Ensure the certificate is valid for server authentication
    validator.validate_usage(
        set([]),
        extended_key_usage=set(['server_auth'])
    )

    print("1")  # Success
except Exception as e:
    print(f"0 - {e}")  # Validation failed
