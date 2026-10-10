# Erdős similarity: growing logarithmic gaps

We prove positive-measure affine non-universality for a class of sequences
whose adjacent ratios can tend to zero. This removes the globally bounded
logarithmic-gap hypothesis in the preceding routing-based research.

For a strictly decreasing positive null sequence, let $z_n=-\log_2 a_n$.
If

\[
z_{n+1}-z_n=o(\log\log z_n),
\]

then, for every $\varepsilon>0$, there is a compact set $F\subset[0,1]$
with $m(F)>1-\varepsilon$ that contains no nontrivial affine copy of the
sequence. The same holds simultaneously for each prescribed countable
family satisfying the hypothesis. In fact the closed periodic parent
set misses infinitely many distinct outputs of every map
$f(a)=y+ca^s+O(a^{s+\alpha})$, with $s,\alpha>0$ and $c\ne0$.

An explicit application is

\[
a_n=2^{-n(\log\log(n+20))^\beta},\qquad 0<\beta<1.
\]

Its adjacent ratios tend to zero and its occupied logarithmic bins have
upper Banach density zero. The more general local-annulus theorem also
allows arbitrarily large gaps between useful blocks.

Read the [complete proof](paper.md), [typeset PDF](paper.pdf),
[proof review and verification scope](AUDIT.md), and
[prior-work comparison](PRIOR_WORK.md). The added arguments are annular
sampling and a variable-tree schedule with total span $U^{o(1)}$; finite
routing, center exposure and open repair are credited to earlier work.
This is a result for a class within the longstanding Erdős similarity
problem. It does not settle the full conjecture or the sequences
$2^{-n^2}$ and $2^{-2^n}$.

## Reproduction

Python 3.10 or later suffices for the exact finite controls and integrity
checks; no numerical solver or CAS is needed:

```sh
python3 -B research/erdos-similarity-growing-gaps/checks/exact.py
python3 -B -O research/erdos-similarity-growing-gaps/checks/exact.py
python3 -B research/erdos-similarity-growing-gaps/verify.py
```

The checker compares actual preorder placement with a closed-form span
and checks exact entropy coefficients and a rational upper bound for
$\log2$. These are finite controls, not a proof of the infinite analytic
theorem. The new package
[`formalizations/erdos-similarity-growing-gaps/`](../../formalizations/erdos-similarity-growing-gaps/)
formally closes the deterministic annular sampling layer: the first-sample
lemma, local gap propagation, the implication
$z_{n+1}-z_n=o(\log\log z_n)\Rightarrow W$, and the variable-tree algebra
all replay at trust level zero. The random routing, continuum parameter
stratification, measure construction, countable exhaustion, and avoidance
endpoint are explicitly still outside the Lean package.

The Lean replay needs Lean 4.34.1 and Mathlib at
`d13f23b723b8a846827a245b89c10fc7d3f11612` with its pinned transitive
dependencies. A compatible Lake manifest is included in `formal/`.
Obtain the official dependency cache with `lake exe cache get` in a
project using that manifest, or reuse the repository's matching pinned
dependency project. Then run:

```sh
python3 -B research/erdos-similarity-growing-gaps/formal/replay.py \
  --lean /path/to/lean-4.34.1/bin/lean \
  --dependency-project /path/to/pinned-lake-project \
  --output /outside/repository/new-lean-run
```

`--library-root /path/to/complete/official/library/overlay` may replace
`--dependency-project` when a complete matching official overlay is
available. Own sources are always recompiled in the new output directory.
Standard Lean axioms `propext`, `Classical.choice`, `Quot.sound` and the
official compiler/kernel implementation remain trusted.

To build the paper, install Pandoc, TeX Live with AMS/Latin Modern/xurl,
and Poppler, then run:

```sh
python3 -B research/erdos-similarity-growing-gaps/build.py \
  --output /outside/repository/new-paper-build
```

The build does not enable TeX shell escape. Published source hashes,
Lean output, exact-check output and PDF report are in `results/` and
`SOURCES.json`; `MANIFEST.json` binds the local package. The literature
comparison is limited and no worldwide priority or external human
review is claimed. The finite construction is existential and can be
astronomically large.
