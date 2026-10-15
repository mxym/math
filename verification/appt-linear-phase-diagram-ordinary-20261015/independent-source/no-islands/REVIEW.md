# Independent ordinary review: no islands in the mixed-c set

Decision: **PASS for the exact source below.** This is a complete internal AI-agent ordinary mathematical read, not Lean verification, external human peer review or a priority certificate. The earlier c>=1 and last-boundary decisions are dependencies with their own source bindings; their PASS was not automatically extended to this proof.

The whole 365-line `NO_ISLANDS.md` was read. Its SHA-256 is `f7509ff124d76f12855a55705f317c51133c8e1a93fcadc7f230bebd91b8ad16`. The exact owner ZIP and all source dependencies are retained in `INPUT_OWNER_ZIP.json` and `DEPENDENCY_BINDINGS.json`. The credited L20 elimination and L/S actual-matrix statements match the previously fully read immutable inputs. No unreviewed root scalar argument is used as a premise.

## Mathematical assessment

**The constrained h reduction is exact.** For K=2c, k=Kx and a=2k^2/[3(K-k)], U=(b(K)-B)/P is strictly convex in h. Its unconstrained minimizer is v/k, v=w(k)-g(K), always less than one. If v<=0 the actual constrained value is exp(a)r_0>r_0, which precludes strict mixed value. Only when v>0 is the interior formula U_min=exp(a)Delta/q(k) valid, giving the test W<0. The admissibility condition is essential throughout this argument, and it is not omitted in the later derivative proof.

**Both quantitative derivative inequalities have whole-domain proofs.** The exact identity

    t g''/g' = qz-q+1/z,   z=(t-d)/d,

combined with AM-GM and the strictly positive elementary function of sqrt(q), proves t g''/g'>1-g/2 for every t>0. The latter function's derivative is -(1-y)^2/y, so the strict direction is correct.

The elasticity implication is conditional: if e(t)>1/2, then e(t)<1-w(t)/4. I independently derived the displayed ODE using w as variable. Its small-w solution lies strictly below E(w)=1-w/4. At a possible contact on 0<w<=2, the sufficient polynomial R(E) is positive throughout E in[1/2,1]: R''+20=192(2E-1)(E-1)<=0 and both endpoint values are positive. Thus an upward contact is impossible. After w=2, the constant barrier e=1/2 has strictly negative contact derivative because q<1/5. This excludes e>1/2 there. There is no invalid extrapolation of a linear upper bound to large w with negative right side. The removable t=0 expansions are used only to initialize this comparison, with the subsequent argument covering all positive t.

**Each width is admissible on just one initial K interval.** The monotonicity of t^2 w''(t) gives x^2 w''(xK)<w''(K)<g''(K), hence strict concavity of v(K). Its initial slope x/2 is positive and its large-K limit is negative infinity. Therefore v>0 exactly on one interval (0,T_x), with a single finite positive endpoint. A fixed width cannot become admissible again later.

**The normalized increment monotonicity uses admissibility at its decisive step.** For fixed E=e(k), the auxiliary chi_E(t)=t g'(t)-2E g(t) increases on[k,K]. If E<=1/2 this follows from g',g''>0. If E>1/2, the proven inequalities and g(t)<=g(K)<w(k) give

    t g''/g' > 1-g(t)/2 > 1-w(k)/2 > 2E-1.

Hence K Delta'-2e(k)Delta>0, exactly the derivative condition for Delta/d(k)^2. The proof treats E as constant only within this auxiliary t comparison; it correctly differentiates d(k) when returning to K.

The identities v=d(k)-Delta and q(k)r_0=Delta+phi(v), with phi(v)=exp(-v)-1+v, then prove H_K>0 throughout the entire admissible interval. The strict decrease of phi(v)/v^2 follows from its integral formula. The cases v'>0 and v'<=0 are handled separately, so multiplying a strict inequality by a negative derivative never reverses it unnoticed. Consequently W_K>0 everywhere it is used.

**The global no-islands conclusion follows, not a sampled pattern.** At fixed x, W starts at log(1-x^2)<0 as K->0 and tends to a strictly positive value as K approaches T_x. Its strictly positive K derivative gives exactly one zero K_x. Analytic IFT applies because W_K is nonzero, and uniqueness glues the local solutions into one analytic curve for 0<x<1. Taking the union of the initial strict intervals (0,K_x) gives exactly (0,sup_x K_x). The last-boundary theorem supplies an attained interior tie at the supremum and the strict bounds 1/10<c_star<1. Thus no disconnected mixed-c component is left unexamined.

For K>K_star, every interior width is strictly below bulk at the crossing, whether its h minimum is constrained or interior. The earlier affine argument therefore yields the full pure all-r argmax. At K=K_star, all extra ties remain inside a compact subset of the admissible x interval. W is analytic there and not identically zero: as x->1 its positive 1/(1-x) term dominates log(1-x). Discreteness of zeros on that interior compact subset proves finitely many tying widths, with one unique h at each. This source does not prove that there is only one such width or that its Hessian is nondegenerate; those claims belong to the separate critical-certificate scope.

**Actual quantum scope remains L/S's original one.** The parameter statement concerns existence of strict mixed value in c, then transfers the full scalar argmax through already proved actual-matrix theorems. Original complex trace-one densities remain PPT after every global unitary, m->infinity with all integers n>=m, fixed positive alpha/m limit and finite critical peak ratio. Full argmax distance, actual spread J and actual peak loss all remain necessary. No positive-r body-law shortcut, finite exact optimizer statement or simultaneous small-c physical limit is introduced.

## Independent controls and remaining limits

The new reviewer program `independent_checks.py` imports no author module. Its actual run `20261015T125457.850334Z` PASS checks fourteen symbolic identities, including the ODE, curvature identity, polynomial barrier and exact W derivatives, together with finite conditional-monotonicity and concavity diagnostics. These samples do not establish the continuum theorem; the full proof read above does.

Actual caught AssertionErrors retain concrete witnesses for deleting v>0, applying the elasticity bound unconditionally, reversing the curvature bound, reversing phi(v)/v^2 monotonicity, and reversing the mixed-window closing sign. In particular K=2,x=.01 has W<0 but v<0 and its actual constrained U/r_0>1, a direct false-positive if admissibility is dropped. At t=10, 1-w/4 is negative while e is positive. The author floating diagnostic files are retained in the owner archive but are not represented as reviewer executions or premises of this proof.

No correction or unresolved mathematical finding was needed in this exact source. It closes no-islands for the existence of strict mixed value, not the global uniqueness of every mixed phase at every r. No complete finite-dimensional spectral classification, new formal audit, external priority claim or new major-result count is supplied. The original author pending status is preserved as historical source text. Later critical and global-mixed manuscripts require their own decisions.
