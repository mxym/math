# Independent ordinary review of the cubic-scale APPT packet

Verdict: **PASS for the complete written statements C0-C4**. Reviewed at 2026-10-14T07:25:08.551098+00:00.
The result applies to the entire original all-global-unitary APPT set, every
fixed alpha>0, and all dimension sequences with m->infinity and D/m^3->delta>0.
This is mathematical manuscript review. It is not a Lean or kernel audit,
external peer review, or a historical-novelty certificate.

## Actual source coverage and binding

- INITIAL_PAPER.md: complete 1-461, SHA256 `9bc18d7f5b45cb2c9522425a9a162febb25f9a1ea6d582391b510d82c0fab2e0`.
- INITIAL_THEOREM_MAP.md: complete 1-18, SHA256 `345a73ef453836b9d57137b2bfc1995f16c3662b483074527df4ea43f2e1a1fb`.
- Final PAPER.md changes only the disclosed nonmathematical status at line3.
  Its final SHA256 is `a2e940d320950c258d2aed13bb5afa81ea3bc41efa74acc09dca703d0a817449`. Reversing that sole change
  restores the exact initial hash. No mathematical line changed, and no
  second complete final reread is claimed. Delta context 1-6 was read.
- Final THEOREM_MAP.md: complete 1-19, SHA256 `50dd9a5c171e0efcd65848f5c6e9fca3065d31f9c99b38382ca70d7c0484c693`.
  Only status and outcome descriptions changed. Its target rows are intact,
  and reversing the disclosed edits restores the exact initial-map hash.
- README.md: complete 1-36; LITERATURE.md: complete 1-46. Both supplementary
  sources were checked separately and are bound in REVIEW.json.
- check_cubic.py: complete 1-209, SHA256 `b7f69605ee10f0e16ed2cf5faaa451f95f95c0d321c315f8e99c4a03e8afd0e3`.
  The author script was inspected, not rerun or substituted for proof.
- FINITE_CONTROLS.json: raw lines 1-100 plus complete structured inspection
  of all report keys, eight profiles, finite flags, entropy targets/final
  errors, and wrong-extension controls. The full JSON was parsed; a raw
  1810-line reread is not claimed. SHA256 `3d670715143597a66ada2818ed83f8d8354b7855656d5a8ff87e9b9752ec5cae`.
- Inherited SHARP_ASYMPTOTIC.md: actually read 1-259, SHA256
  `49b71670f33283f1018c915d07b11c509266395f3a201dc19bb627cd932bc2f9`. Only its stated arbitrary-edge, row/star, normalization,
  lambda1 bound, and physical q-projection inputs are used. This reading
  does not widen the historical audit scope or newly certify all old results.

## Proof findings

No mathematical defect requiring manuscript revision was found.

The physical slot reduction is exact. A positive anomaly occupies a negative
Schmidt edge direction; a negative anomaly occupies a positive diagonal or
edge direction. Both can occupy the same edge because they are different
witness eigenvectors. Arbitrary unitary traces reduce by the usual spectral
rearrangement inequality to adverse permutations: |U_ji|^2 is doubly
stochastic. Thus the sufficient construction covers arbitrary global
unitaries, not just selected eigenbases, including lower Schmidt ranks.

The exact matrix is (2+kappa)I-kappa J-P. Its nonpositive off-diagonal entries
make the nonnegative Schmidt test equivalent to PSD by taking absolute values
in Rayleigh quotients. The exact finite rank-one prefactor in (19) is correct.
Its Perron/walk gap uniformly protects every finite prefix at bounded c.
In particular the single-diagonal beta1 test keeps beta1 below one before
bounded small-order kernel derivatives are used; this is noncircular.

Coercivity precedes compactness. The inherited actual l2 residual bound gives
O(1) head kernel gain for every physical spectrum. Interval endpoint loss
then forces c_m bounded for any bounded-below correction. Only afterward is
the additive centered entropy identity (17) used. Both actual trace
normalization and integer-rank rounding are retained at additive o(1).

Every fixed finite profile with strict cost slack gives an actual all-unitary
APPT state. There are finitely many witness patterns for that profile, and
all exact rank-one inequalities converge to their graph costs. Endpoint ranks
are large enough, and trace-normalized kernel gain reaches the profile value.

The first omitted walk term records all tail l1 mass even when there are
more anomalous entries than could be placed disjointly in the physical graph.
The O(1/L) tail gain and positive mass penalty prove unrestricted finite
approximation, attained infinite profiles, and compactness. The same two
losses prove both directions of the complete near-maximizer criterion.

The onset is exactly the maximum single-anomaly gain/cost ratio. Every pair
of nonzero anomalies has a strict interacting pattern, so only the named
single families and the empty profile can tie at criticality. Above it the
empty anomaly profile is unique. These are limiting claims, not exact finite
optimizer claims.

For alpha>=2 the shifted-star inverse and square identity give a single-edge
cost lower bound at the combined head energy. The positive superquadratic and
negative subquadratic kernels then give the unrestricted scalar upper. Strict
cost equality supplies the full single-positive equality profile, including
alpha=2. The stationary equation and p=0/p=1 critical tie in (9) are correct.
For alpha<2 the full graph formula is retained; no scalar substitution is made.

## Independent supporting arithmetic

An independent fixed-label enumeration, different from the author's
vertex-creation generator, examined **10,894 slot assignments** on seven
rational profiles. All maximal graph costs matched. Nine direct full m by m
LDL checks accepted strict-cost constructions and rejected the trace-only or
unprotected-width alternatives. Six symbolic checks independently covered
the finite rank-one prefactor, two-negative strict gap, shifted-star square,
full three-vertex inverse, and the interval optimum/deficit Taylor terms.
All passed. The independent script/report are bound in REVIEW.json.

The author report separately records 3,440 finite Schur checks, 192
trace-normalized entropy checks, and 1,011 shifted-star checks, with no
retained failures. Its low-order two-positive control correctly rejects an
unrestricted alpha=1 scalar reduction. These remain finite supporting
calculations and are not the proof of C0-C4.

The supplemental literature metadata were independently checked against the
primary arXiv sources: AAW v2 (18 September 2026), Tran v1 (16 September
2026), Jiang/Qiu/Yu v1 (6 September 2026). Actual contextual reads were AAW
rendered 862-954 and Tran rendered 286-373, plus metadata/abstracts. Their
disclosed domains agree with the bounded literature screen. This is not a
full paper audit or an originality certificate.

The initial binding helper safely rejected the newly changed status bytes
before writing any review output. The final helper validated the declared
byte deltas explicitly; this was not a mathematical control failure.

No Lean execution, audit expansion, catalog edit, commit, submission,
publication, or external novelty claim was performed by this reviewer.
