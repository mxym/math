# State-independent entanglement extraction

**Complete written analytic argument for the precise model below; not Lean-formalized or externally peer reviewed.** The principal external inputs are standard Schur--Weyl duality, Weyl/hook dimension formulas and highest-weight characters. The Gaussian statement uses the ordinary central limit theorem. Finite ancillary checks do not certify the unbounded argument.

The preceding extraction paper allowed the preprocessing to depend on the input state. This continuation gives a stronger quantifier order: **one deterministic family of global unitaries and subsequent local product channels, indexed only by local dimensions, copy number and requested target dimension, works for every state**. No eigenvalues, eigenbasis, rank or entropy are supplied to the protocol. There is no tomography, measurement or additional ancilla before the global unitary.

For every fixed $2\le m\le n$, every input spectrum p including zeros, and target rate R, this family attains the same exact fidelity-decay exponent as the state-aware completely-PPT optimum:

\[
 E_p(R)=(R-\log m)_++\max_{1\le\alpha\le2}
 \frac{\alpha-1}{\alpha}(S_\alpha(p)-\log(mn)+2\min(R,\log m)).
\]

It attains faithful capacity $C=\min(\log m,[\log(mn)-H(p)]/2)$ and eventual-exact capacity $C_0=\min(\log m,[\log(mn)-\log\operatorname{rank}\rho]/2)$ without state knowledge.

The new strict-direct reliability law, for $C_0<R<C$, is
\[
 \lim_k-\frac1k\log(1-F_k)
 =\min_{H(q)\ge\log(mn)-2R}D(q\|p).
\]
It is optimal even against state-aware completely-PPT protocols. The exact zero-error boundary is excluded for a mathematical reason described in the proof, not treated by a false continuity argument.

If $0<C<\log m$ and varentropy $V(p)>0$, the same protocol attains the exact Gaussian window:
\[
 \log K_k=kC+z\sqrt{k}+o(\sqrt{k})
 \quad\Longrightarrow\quad F_k\to\Phi(-2z/\sqrt{V(p)}).
\]

## What makes the construction universal

Schur--Weyl blocks are fixed independently of the state. The state is an arbitrary unknown operator on each representation factor tensored with an identity on its permutation-multiplicity factor. We retain a known fraction of that identity factor, not a state-dependent set of eigenvectors. All blocks are packed simultaneously into disjoint local sectors by one unitary, with a block-specific embedded Bell dimension. Exact extraction of sufficiently small blocks gives the reliability result. A universal dominating state relates these same blocks to ordinary iid self-information and yields the Gaussian law without an assumed Young-diagram CLT.

## Attribution and scope

Universal compression, pure-state concentration, universal ordinary mixed-state LOCC distillation, and state-agnostic work extraction are established prior subjects. The paper explicitly credits Jozsa--Horodecki--Horodecki--Horodecki, Hayashi--Matsumoto, Keyl--Werner, Watanabe--Takagi, Takagi and collaborators, and the earlier source-coding literature. The Rains constraints and Lami entropy converse are not claimed as new.

This is a stronger result for **global-unitary preprocessing followed by local extraction**, not a solution of ordinary fixed-input LOCC distillation. The initial global entangling operation cannot be omitted. The original APPT higher-dimensional purity and APPT=AS problems remain separate. No universal efficient circuit, exact zero-error-boundary law, cap-boundary Gaussian law, arXiv submission, DOI or exhaustive priority certification is claimed.

## Exact ancillary checks

```sh
python3 check.py --report verification/exact-checks.json
python3 -O test_checker.py --report verification/source-mutations.json
```

Only Python's standard library is needed. The independent combinatorial routes include hook dimensions versus tableau recursion, Weyl dimensions versus Schur characters, full probability normalization, rank-deficient Schur weights, noncommuting input orientations, coherent multiplicity-factor selection, and every dyad of several Bell-code subspaces. All checks use exact integers or rationals. The tests include corrupted-source rejection and assertion-disabled positive controls. Their scope is ancillary, not a replacement for the analytic proof.

The full derivation is in `PROOF.md`; `RESEARCH_LOG.md` records current-literature checks, design obstacles and the explicit verification boundary. The earlier immutable qutrit, negativity and extraction releases are unchanged.
