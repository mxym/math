# Sharp permanent--determinant norms in three and four rows

mxym/math research project. AI-assisted manuscript, 7 October 2026.

For every complex coefficient \(\lambda\), the least constant in
\[
|\operatorname{per} A+\lambda\det A|
\le C_\lambda\prod_{i=1}^3\|A_{i\cdot}\|_2
\]
is
\[
C_\lambda=\max\{2/\sqrt3,|1+\lambda|,|1-\lambda|,
                         |\lambda+i/\sqrt3|,|\lambda-i/\sqrt3|\}.
\]
We prove this on the entire complex plane, obtain the exact coefficient lens,
classify equality for the sharp absolute-value permanent--determinant
inequality, and calculate the exact amplification and tensor product norm of
every marginal-preserving three-row permutation law. Equality outside that
absolute-value endpoint is not classified here.

The proof is a self-contained Hermitian-matrix certificate with five explicit
sharp lower witnesses. The rational interpolation checkers certify universal
polynomial identities using degree bounds explained in Section 5; the analytic
positivity and equality arguments are given in the text. No numerical optimizer
or solver output is a premise of the proof. This is a traditional proof, not a
Lean formalization.

The permanent-only endpoint is classical: E. A. Carlen, E. H. Lieb and
M. Loss, *An inequality of Hadamard type for permanents*, Methods and
Applications of Analysis 13 (2006), 1--18. The project previously proved the real
three-row endpoint in
[the robust-permanent note](../../notes/sharp-robust-permanent/paper.md), Section 9.
The complex pencil proof below does not assume the Bristiel--Caputo permanent
inequality; that result is an input to the earlier all-arity robustness note.
The present coefficient classification is a distinct three-row statement.
Part Q supplies the complete four-row tradeoff
\[
|\operatorname{per}A|+c|\det A|
\le\max\{3/2,1+c\}\prod_{i=1}^4\|A_{i\cdot}\|_2\quad(c\ge0),
\]
its full equality classification and quantitative pairwise deficit, an exact
all-column two-row symmetric--alternating spectrum, and exact four-row parity
tensor norms. It also determines the four-row pencil norm for real coefficients.
It does not assert that same pencil formula for every nonreal coefficient, or
classify every marginal-preserving four-row law. Part Q uses a self-contained
two-row Laplace/Cauchy argument; its permanent-only endpoint is classical.
No all-arity or general-exponent extension is asserted. A limited literature
screen is recorded separately and does not establish mathematical priority.
