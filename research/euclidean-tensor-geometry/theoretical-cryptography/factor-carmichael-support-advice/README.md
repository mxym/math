# Deterministic factoring from Carmichael prime-support advice

## Status

Research-branch result. The proof is self-contained modulo the stated
least-character-nonresidue theorem. It has passed the deterministic
finite verifier in this directory. It is not an immutable release and
has not yet received an author-independent proof audit.

## Theorem

Let \(N\ge2\). The auxiliary input is a finite list \(\mathcal S\) of
distinct primes such that
\[
  r\mid\lambda(N)\quad\Longrightarrow\quad r\in\mathcal S. \tag{1}
\]
The list may contain extra primes. No exponents
\(v_r(\lambda(N))\) and no value of \(\lambda(N)\) are supplied.

Define
\[
 E_{\mathcal S}(N)=
 \prod_{\substack{r\in\mathcal S\\r\le N}}
 r^{\lfloor\log_r N\rfloor} \tag{2}
\]
and
\[
 P_{\mathcal S}(N)=
 \max\bigl(\{p:p\mid N,\ p\notin\mathcal S\}\cup\{1\}\bigr). \tag{3}
\]
For every fixed \(\varepsilon>0\), the complete prime factorization of
\(N\) can be computed deterministically in
\[
 P_{\mathcal S}(N)^{1/(4\sqrt e)+\varepsilon}\,
 \operatorname{poly}_{\varepsilon}
 \!\left(\log N+\sum_{r\in\mathcal S}\log r+|\mathcal S|\right) \tag{4}
\]
bit operations.

Thus the **prime support** of a Carmichael exponent, even with false
positives, is enough to synthesize the fully factored exponent multiple
needed by the multiradix splitting method. The multiplicities in that
exponent need not be given.

## What this does not say

Condition (1) is advice. The theorem does not compute the prime support
of \(\lambda(N)\), does not turn an unfactored value of \(\lambda(N)\)
into that support, and does not give an ordinary polynomial-time
factoring algorithm. The output-sensitive factor
\(P_{\mathcal S}(N)^{1/(4\sqrt e)+\varepsilon}\) can still be exponential
in the input length. No concrete modulus, key, implementation, or
security claim is involved.

## Reproduction

\`\`\`sh
./replay.sh
\`\`\`

The checker independently reconstructs exact Carmichael prime supports,
adds false-positive support primes, synthesizes (2), checks
\(\lambda(N)\mid E_{\mathcal S}(N)\), and replays complete multiradix
refinement on squarefree and arbitrary-multiplicity inputs.
