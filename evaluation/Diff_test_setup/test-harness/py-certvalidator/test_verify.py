from asn1crypto import pem
from certvalidator import CertificateValidator, errors, ValidationContext
import sys

ca_path = sys.argv[1]
entity_path = sys.argv[2]

end_entity_cert = None
intermediates = []

with open(entity_path, 'rb') as f:
	for type_name, headers, der_bytes in pem.unarmor(f.read(), multiple=True):
		if end_entity_cert is None:
			end_entity_cert = der_bytes
		else:
			intermediates.append(der_bytes)

trust_roots = []
with open(ca_path, 'rb') as f:
    for _, _, der_bytes in pem.unarmor(f.read(), multiple=True):
        trust_roots.append(der_bytes)

# print("End entity cert:\n", len(end_entity_cert))
# print("Trust roots:\n", len(trust_roots))

context = ValidationContext(trust_roots=trust_roots)
validator = CertificateValidator(end_entity_cert=end_entity_cert, intermediate_certs=intermediates, validation_context=context)

# validator.validate_tls('www.google.com')
try:
	validator.validate_usage(
		set([]),
		extended_key_usage=set(['server_auth'])
	)
	print("success")
except Exception as e:
	print("failed")
	print(e)