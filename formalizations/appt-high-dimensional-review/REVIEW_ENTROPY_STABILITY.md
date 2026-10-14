# Quantitative stability of the physical APPT entropy head

This checkpoint addresses an exact dependency of the proposed von Neumann/Renyi rigidity results. It does **not** prove the full entropy extremum, the implication from full-entropy near-optimality to head saturation, or its converse. No new preprint or Release is created.

## Exact finite statement

Let A be an actual APPT density matrix on C^m tensor C^n, 2<=m<=n, D=mn. Its decreasing eigenvalues are lambda_1,...,lambda_D. Use exactly the paper pivot b=lambda_(D-m(m+1)/2+1)>0. Put h=m-1, a_i=lambda_i/b-1 (1<=i<=h), beta_i=1-lambda_(D+1-i)/b (1<=i<=h+1), f(x)=(1+x)log(1+x)-x, and

    H = sum_(i=1)^h [f(a_i)+a_i beta_i] + sum_(i=1)^(h+1) f(-beta_i),
    Delta = 2-H.

The new finite physical theorem proves Delta>0, a_1^3<=300 Delta and beta_1<=72 Delta. If Delta<=1/144, every actual eigenvalue is positive and

    |D lambda_i-1|^3 <= 11904 Delta  for every i.

The constants are sufficient, not claimed optimal. The logarithm is the actual real logarithm, including f(-1)=1, and the APPT predicate quantifies over every global unitary. No star inequality, spectrum ansatz, pivot value, sign/order assumptions or flatness premise is supplied by the final physical caller.

## Proof dependencies

EntropyHeadStability retains the exact prebound H<=2+beta_1(a_1-1)-gap(a_1). For a_1>=1 the previously verified quartic margin gives Delta>=37/1344, while a_1<=2. For a_1<=1, gap(a_1)>=a_1^3/9 and Delta>=gap(a_1)+beta_1(1-a_1). Splitting at a_1=1/2 gives the cubic positive-outlier and linear negative-outlier bounds. If Delta=0 they force every head coordinate to vanish, hence H=0 rather than two, proving strictness in every finite dimension.

PhysicalHeadConditions reuses the construction of the genuine sorted shifted-star witness but returns all its derived scalar conditions. The canonical eigenvalue permutation, exact paper pivot, zero eigenvalue endpoint and positive normalization are proved internally. Old proof modules and their source manifest are not rewritten.

NormalizedHeadStability uses trace one to handle the missing normalization step: if b(1-y)<=lambda_i<=b(1+a) and y<=1/2, then Db<=2 and |D lambda_i-1|<=2(a+y). Combining (a+y)^3<=4(a^3+y^3), y^3<=y and the two deficit bounds yields 11904 Delta. It does not replace b with 1/D without proof.

PhysicalHeadStability connects this to the original matrix and actual ordered eigenvalues. PhysicalHeadLimit proves the genuine dimension-varying statement: for any sequence of such physical matrices whose *head deficit* tends to zero, for every epsilon>0 all normalized eigenvalues eventually lie in (1-epsilon,1+epsilon), uniformly over the entire spectrum. Dimensions need not be fixed or separately assumed to grow. The conclusion is expressed directly in eigenvalues; an operator-norm identification is not silently imported.

## Controls and reproduction scope

Controls include a zero scalar head with deficit two (flatness alone does not imply head saturation), an admissible head containing a zero-eigenvalue endpoint with deficit one, rejection of a missing star budget, a nonuniform pivot, and the necessity of trace normalization. These scalar controls do not assert quantum realizability unless explicitly stated. The primary forged-proof test targets the final physical dimension-varying flatness theorem; additional exact-type controls target the finite physical cubic bound and scalar outlier bound.

The six new modules were individually compiled in a restored, SHA-256-verified public Lean 4.34.1/Mathlib environment. Its compiler and cached resources came from the existing repository's pinned environment archive. Direct offline compilation/replay is not called a fresh Lake or independent CI run. The selected source dependencies were compared against the previously independently verified main manifest. GitHub CI uses the actual pinned dependency checkout and a fresh selected-closure Lake build.

Run in this directory:

    lake exe cache get
    python3 reproduce_entropy_stability.py --check-only
    python3 reproduce_entropy_stability.py --fresh

The separate ENTROPY_STABILITY_HASHES.json and EntropyStabilityAudit.lean bind the entire dependency closure of these results. This avoids changing the existing purity audit, its 154-input source manifest or immutable publication trees. The new workflow does not certify all unrelated APPT roots anew. Exact successful run details and downloaded evidence must be read from the retained verification record; this written description alone is not a certificate.
