# Exact finite certificate checker

This standard-library Python program checks a supplied finite periodic-sieve certificate using integers. It does not run the unbounded exhaustive search or formally verify the general entropy proof.

Run the bundled checks without Python optimization flags:

```sh
python certificate_checker.py
```

Expected output: `Seven exact certificate tests passed.`

Verify the separate real-quadratic horizontal-step example:

```sh
python - <<'PYTHON'
import json
from certificate_checker import verify_certificate, uniform_bound
with open('example_real_quadratic.json') as f:
    data = json.load(f)
assert verify_certificate(data['input'], data['certificate'])
assert uniform_bound(data['input'], data['certificate']) == data['uniform_component_bound']
print('Exact example verified:', data['uniform_component_bound'])
PYTHON
```

The example uses Z[sqrt(2)], the norm-seven generator 3+sqrt(2), and only the two horizontal unit offsets. It is not a certificate for a large two-dimensional moat instance. The verifier rejects coincident conjugate kernels, incomplete or duplicated representative sets, incorrect moduli and inconsistent edge potentials. Assertions perform validation, so the program explicitly rejects `python -O`.

The proof of certificate sufficiency, necessity, the integer component bound and search termination is in Section 11 of the accompanying version 2 manuscript. A successful finite certificate can be checked without trusting the breadth-first constructor or the general analytic existence argument.
