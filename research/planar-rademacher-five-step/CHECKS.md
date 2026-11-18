Both programs use only the Python standard library and explicit exceptions, not assertions which disappear under optimization. From this directory:

    python -B -O verify.py
    python -B -O independent.py
    sha256sum -c SHA256SUMS

The first check directly enumerates all 32 integer outcomes and verifies the parity witnesses for n=4 and n=5. The independent check reconstructs the previous three-dimensional example and tests the signed permutation, its rank-two deformation and all parity certificates in exact rational or integer arithmetic. They do not check arbitrary-length extremality, which is not claimed.

Observed output:

    PASS: 32 integer sign sums; histogram 2:6, 10:20, 26:4, 34:2; 6/32 >=12; 0 ties.
    PASS: parity witnesses for all 8 one-class choices at n=4 and 136 two-class multisets at n=5.
    PASS: 32 exact norms; rank-two sign equivalence and deformed DK dual; 8 one-class and 136 two-class parity certificates; all conditional quadratic moments zero.
