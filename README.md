# Exact minimum support on two opposite-parity cube levels

If a nonzero real function on the n-cube has exactly two Walsh levels i<j of opposite parity, its smallest possible support has size

    2^max(n−i,j) / 2.

We give all extremizing functions, not just a support witness. For i+j≤n they are a product of i disjoint signed coordinate pairs, multiplied by 1+g, where g is a sign-valued function of pure degree j−i on the remaining coordinates. The other half of the range follows by multiplying by full parity.

This answers Valyuzhenich's *Optimal functions with spectral constraints in hypercubes*, arXiv:2303.10995v1, §6 Problem 5, where exactly levels {0,3} are required: the answer is 2^(n−1) for every n≥3. That special case has a short antipodal proof. The broader characterization is a consequence of antipodal pairing together with his known single-level equality theorem and a Fourier tensor argument. No claim is made about same-parity pairs or the already settled interval-support problem.

Run `sh replay.sh | diff -u RESULTS.txt -` with Python 3. The two independent checks use direct Walsh spectra on explicitly classified families, and exact support-space ranks without assuming the classification.
