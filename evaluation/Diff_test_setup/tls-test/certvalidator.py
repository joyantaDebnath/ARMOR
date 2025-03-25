from oscrypto import tls
from certvalidator import CertificateValidator, errors

session = tls.TLSSession(manual_validation=False)
connection = tls.TLSSocket('www.google.com', 443, session=session)

try:
    validator = CertificateValidator(connection.certificate, connection.intermediates)
    validator.validate_tls(connection.hostname)
except (errors.PathValidationError):
    print("error")

