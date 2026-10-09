# Proof map and self-audit

This is a project self-review, not external professional mathematical peer review. The paper's theorem numbers refer to `paper.tex` version 1.

## Theorem → necessary lemma → verification

| Claim | Necessary chain | Evidence and limitations |
|---|---|---|
| Theorem 1.1, universal pure bound | Pure conditional ensemble; Holevo `I_M<=h`; deletion of one setting | Published Holevo theorem, explicitly cited; elementary summation proved. Not Lean verified. |
| Theorem 1.1, full-rank necessity | All settings saturate; equality implies commuting pure conditional projectors; invertible amplitude implies orthogonal conditionals; `H(X|Y)=0`; monomial matrices | Lemma 2.1 supplies the complete argument. The equality implication is the precise published external input. |
| Theorem 1.1, three-setting rigidity | Monomial in computational/Fourier bases; two diagonal marginal descriptions force `I/p`; singleton Fourier support forces affine permutation and linear phase; third setting forces `s^2=-1` | Proposition 2.2 proves the reverse direction for arbitrary amplitudes, not only stabilizer states. No finite search is used. |
| Theorem 1.1, converse | Normalize actual state; compute both partial traces; expand actual Born amplitudes; geometric sum | Equations (9)–(10), root-of-unity identities. Two exact checker paths test the formulas. |
| Existence and `2p^2` rays | Cyclic `F_p^*`; roots of `X^2+1`; uniqueness from support and relative phases | Written group/field argument for every odd prime. |
| Theorem 1.2 | Weyl multiplication; character projector is Hermitian idempotent trace one; local-vector/product or graph dichotomy; graph determinant `-1`; line-intersection Born law; nonscalar matrix has at most two eigenlines | All specialized identities proved in Section 3. Actual density/Born replays independently test six representative states. Finite matrix enumeration is a regression test only. |
| Corollary 3.1 | Count determinant fibre; `p^2` distinct characters; uniqueness of nonzero Weyl expectation support; product counts | Complete count in the written proof, no sampling argument. |
| Theorem 4.1 | Holevo equality; conditional eigenvectors; complete-MUB bilinear identity; contradiction for two positive eigenvalues; projection blocks; complement support bound; Cauchy–Schwarz | Lemma 4.2 and Theorem 4.1 give all steps. No general-rank finite checker or Lean theorem is claimed. |

## Reverse-direction checks

1. The matrix in a common measurement basis is `U^* C conjugate(U)`, **not** `U^* C U`. The latter would conjugate Bob's physical basis and invalidate the problem definition.
2. Full Schmidt rank is used exactly where all `p` conditional vectors must be linearly independent. The rank-deficient counterexamples do not contradict Lemma 2.1 because its hypothesis fails for them.
3. `E=p h` forces every setting, not merely one favorable subset, to attain `h`: all retained terms are at most `h`, and the omitted maximum cannot be smaller.
4. Commutativity of rank-one projectors permits parallel rays; invertibility excludes that case only in the full-rank theorem. The general-rank argument deliberately retains parallel classes.
5. The Fourier marginal diagonal has constant diagonal entries only after the original marginal is known diagonal and trace one. This is used to conclude the entire marginal is `I/p` because the Fourier marginal is also diagonal.
6. Singleton Fourier support is converted to an exact character by Fourier inversion. Its column-zero and column-one consequences fix an affine permutation; the third setting imposes a quadratic finite-difference identity. This is not a heuristic normalizer argument.
7. `s^2=-1` is required. Ordinary affine Bell states with `s^2!=-1` have only two correlated settings and score `log p`. This negative case is replayed explicitly.
8. The graph form represents all entangled pure stabilizer states, not every pure state. Every nongraph pure stabilizer state has a pure marginal and is a product; all other cases are accounted for.
9. A determinant-`-1` scalar exists only at `p=1 mod 4`. At `p=3 mod 4`, a nonscalar graph may have zero, one, or two invariant lines; deleting one setting yields score zero or `log p`, never a violation.
10. The pure-state universal bound is not asserted for mixed states. The full-rank classification is a classification of **attainers**, not a proof of a strict gap in the supremum when no attainer exists.

## Spectral/rank proof review

The Schmidt conditional map is an antiunitary isometry times the common factor `1/sqrt(r)` only **after** the flat-spectrum conclusion. Before that conclusion, its explicit Schmidt-coordinate formula is used. For two distinct positive eigenvalues, every measurement vector has support in at most one eigenspace, so the two nonnegative diagonal projector values multiply to zero. The complete-MUB identity then makes their sum strictly positive, yielding a contradiction.

For the rank gap, the Gram matrix of the projected measurement vectors is the projector `P` itself in that basis. Parallel classes become rank-one blocks; the projector equation forces each nonzero block to have trace one. A nontrivial block of size `m>=2` contributes `m-1` to the complement rank and at most `m<=2(m-1)` to its diagonal support. Zero rows contribute one to both. Consequently `t<=2q` is valid, including zero measurement probabilities. The case `q=0` is separated before division.

## Exact replay ranges

`check_exact.py` enumerates determinant-`-1` matrices at primes `3,5,7,11,13,17,19,29,31`: 69,840 matrices in total. It directly constructs six density matrices (two at `p=3`, four at `p=5`), with all computational and quadratic settings, and checks matrix equations, both partial traces, rational Born numerators, uniform marginals and support sizes. The cases realize `m=0,1,2,p+1` where possible. Five corrupted inputs are explicitly rejected.

`check_affine_gauss.py` independently checks 2,825 quadratic root sums by integer circular autocorrelation at the same nine primes. Its 252 affine states use every nonzero slope and two fixed displacement/phase pairs per prime. For `p<=7` it reconstructs every actual phase sum. For larger primes it applies the already-replayed norm formula to each reconstructed quadratic coefficient. It includes a wrong-slope negative check. It shares no cyclotomic routines with the first checker.

Entropy is not approximated: perfect tables have `p` entries of size `1/p`, independent tables have `p^2` entries of size `1/p^2`, and both marginals are uniform. The code verifies those exact facts.

## Typesetting review

The final PDF has eight A4 pages, embedded standard text/math fonts, complete references, resolved cross-references, and no overfull/underfull-box or undefined-reference warnings in the final build. Pages were rendered and visually inspected, including the full-rank reverse proof, finite-Weyl Born identities, rank-gap proof, and bibliography. The earlier nine-page layout with a nearly empty final page was replaced before publication. PDF rendering is a presentation check, not a mathematical proof check.

## Still not claimed

No complete Lean proof. No general classification of rank-deficient equality states. No sharp ratio for primes `p=3 mod 4`, `p>=7`. No mixed-state classification, no experimental confirmation, and no assertion of historical priority from search, a commit, a release, or a DOI.
