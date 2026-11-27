# The two sparse-code first-moment certificates are not ordered

This note refutes the universal comparison in [AICR c/0059](https://aicr.info/c/0059/). It compares the two random-matrix first moments stated there, not the actual distributions of minimum distances.

For three blocks, 54 columns, 55 independent rows, and threshold \(2^{-\rho}=1/2\), the binary regular certificate is **6**, but the prime-field sparse certificate is **4**, already at \(p=2^{31}-1\). The exact binary cumulative sums on either side of the threshold are \(21367885/43046721<1/2<154953641997605/183014339639688\). A single class of support patterns is enough for the prime-field crossing: four rows have identical supports. Although rare, a fixed small support contributes a growing expected number of relations as the field grows. Replacing the vector count with a count modulo nonzero scalars does not restore the universal inequality: at the same dimensions and \(p=100000000003\), the projective certificate equals **5**.

More generally, for fixed \(k,n,m\) and \(2\le w\le m\), the weight-\(w\) term for the prime-field experiment is asymptotic to
\[
 \binom mw\binom nk^{1-w}p^{\,w-k}.
\]
Thus for every fixed threshold and every fixed target cutoff, the binary certificate eventually reaches that cutoff along \(m=n+1\), whereas sufficiently large primes keep the sparse certificate at most \(k+1\) (at most \(k+2\) after dividing by \(p-1\)). The same phenomenon occurs using exact-weight binary sparse rows in place of binary regular rows.

A separate, field-uniform support-only bound in [PROOF.md](PROOF.md) makes the distinction explicit: along the same sequence the actual probability of a relation below each fixed cutoff tends to zero uniformly over all field sizes. These statements neither estimate any deployed configuration nor imply a failure of any protocol.

## Replay

Run `sh replay.sh` in this directory (Python 3 and SHA-256 utilities; standard library only). One verifier counts transitions between Hamming-weight shells and updates a binary parity count. The other diagonalizes the two abstract random walks by additive characters, compares those counts against small vector-convolution checks, and independently checks primality. The two verifiers use only the declared toy instances. The script validates the frozen contents and compares their complete output to [RESULTS.txt](RESULTS.txt).
