# Fixed-\(K\) factoring from Carmichael prime-support advice

## Status

Research-branch theorem. It has passed a full self-review and the
deterministic finite checker in this directory. It is not an immutable
release and has not yet received an author-independent proof audit.

## Theorem

Fix \(K\ge2\). Let \(N\) have at most \(K\) distinct prime divisors.
The auxiliary input is a finite list \(\mathcal S\) of distinct primes
such that
\[
 r\mid\lambda(N)\Longrightarrow r\in\mathcal S. \tag{1}
\]
False positives are allowed; neither \(\lambda(N)\) nor its prime
exponents are supplied.

There is an unconditional deterministic complete-factorization
algorithm with bit complexity
\[
 \exp\!\left(
   \bigl(\sqrt{2(K-1)}+o(1)\bigr)
   \sqrt{\log N\,\log\log N}\right)
 \operatorname{poly}_K(B), \tag{2}
\]
where
\[
 B=\log N+|\mathcal S|+\sum_{r\in\mathcal S}\log r \tag{3}
\]
is an upper bound for the ordinary input/advice length.

The exponential term in (2) is parameterized by \(\log N\), while an
unusually large false-positive advice list is charged through
\(\operatorname{poly}_K(B)\). For \(K=2\), (2) specializes to the
\(\sqrt2\) semiprime bound.

## Method

After synthesizing a fully factored exponent multiple from
\(\mathcal S\), scan a subexponential range of ordinary bases. Any pair
whose reduced \((p-1)/(q-1)\) coordinate is large is separated by a
smooth-number subgroup escape. In each block that remains, every
pairwise reduced numerator and denominator is small. Relative to one
unknown reference prime, enumerate those rational ratios and recover the
reference shift as the unique positive root of a monotone integer
polynomial.

## Exact scope

Condition (1) requires the actual prime divisors of \(\lambda(N)\) to
be present as genuinely prime list entries. It is not inferred from
\(N\). The theorem does not factor an unfactored Carmichael value, does
not remove the fixed-\(K\) promise, and is not a general-input
subexponential factoring algorithm. Arbitrary multiplicities of the
at most \(K\) primes are allowed.

No concrete modulus, key, implementation, or security claim is involved.

## Reproduction

\`\`\`sh
./replay.sh
\`\`\`
