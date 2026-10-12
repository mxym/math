# Independent parent review of the finite target-atom crossover

Status: PASS for the written mathematical argument as a continuation conditional on its explicitly imported potential estimate (P). This is not Lean verification or a novelty certification.

The reviewed source is PROOF.md, SHA256 88d9971c062414b1637806b0b61248585f1132c6082783df227266fe7122996e.

I checked the following points directly from the full text:

1. The weak-L^s event integral has factor s'=s/(s-1), and the finite-level Holder step costs N^(1/s). With squared gradient energy the optimization h=w^(2/3)N^(-1/(3s)) therefore yields exactly w^(1/3)N^(1/(3s)), not twice that exponent.
2. The source boundary X=0 produces weak-s tail because beta+1=s. The zero-extension losses are included when X<=2h. The transverse bump has all inverse boundary-distance moments. Truncation F_h<=8 yields the strong overlap logarithm and the independent unrestricted upper bound. Taking the minimum of two independently valid upper bounds is legitimate.
3. In the finite-difference estimate, m_h(x-he_j) and m_h(x) are both bounded by r(x). Thus the shifted signed-square integrals are finite and their difference is the stated d_+-d_- term. Centering f by a constant leaves its finite difference unchanged. No off-support potential value is required.
4. All strip windows remain separated uniformly under h<=epsilon_0 2^(-K). Exact cumulative matches at BOTH endpoints, not just central mass matching, preserve every outer atom mass. Convex maxima give genuine global potentials; only activity on the source is used. There are at most 2K+1 target atoms, with slopes ordered and distinct. The horizontal discrepancy identity follows because the central intervals overlap and no direct two-outer-label crossing occurs.
5. p-moment normalization contributes K^(-1/p). Since the unnormalized squared map difference is comparable to K h and the coupling cost is bounded by K h^3, the exponent after scaling is 1/2-1/p=1/(2s). The proposed K cutoff yields h 2^K<=C w^(5/12), uniformly in N. Fixed N and small w genuinely leave K fixed, eliminating a hidden order-of-limits assumption.
6. N=2 cannot use the K-strip formula. The separate rare-cell construction does: mass m_a~a^s, angular perturbation O(a), and positive normalized symmetric difference give map separation a^(1/2) and target distance O(a^(3/2)). Both target p-moments equal one. The exact N=1 formula is min(w,2), not w for unrestricted w.
7. Supremum uses W2<=w, so only an upper bound on the constructed coupling cost is necessary. Target distances need not be equal to w. Zero masses and coincident labels are properly handled by counting distinct positive-mass support points.

No material gap or coefficient/exponent correction was identified. The constants may depend on p,d and the fixed normalized source, but not N or w. The result must retain d>=2, p>2, small-w qualification and the dependence on (P). The sharp N exponent is up to multiplicative constants, not an exact numerical coefficient or a proved limit.

Before publication, preserve attribution to the inherited two-atom/multistrip constructions, and distinguish this new two-parameter statement from prior unrestricted logarithmic sharpness. A full literature equivalence check remains incomplete. No claim is made here about the truth of an uninspected Lean encoding or about all strongly log-concave sources.
