# Primary sources and scope

- Bartosz Regula and Hao-Chung Cheng,
  [*Sharp one-shot bounds and optimal exponents of universal randomness
  extraction*, arXiv:2611.33270v1 (24 Nov 2026)](https://arxiv.org/html/2611.33270v1).
  Section II.2, Equations (22)–(25), specifies the exact versus
  upper-bound notions of universality and the trace-distance metric.
  Section IV, Lemma 8 and §IV.3 Equations (85)–(86) identify the benchmark
  and its achievability bound. Section IV.3, Theorem 11, gives the
  \(1/3\) lower bound under \(4^*\)-universality; Lemma 12
  provides the random-bin symmetrization and Lemmas 13–14 and
  Equations (113)–(126) give the fourth-moment and clipping method.
  The criterion here keeps the symmetrization and clipping method,
  allowing instead spectral control of quadratic features.
  Section IV.5, around Equations (141)–(144), explicitly raises the
  weakest-hash-assumption question, shows that ordinary two-universality
  does not suffice, and discusses balanced bins. The exact threshold
  within the strong independence hierarchy and the new sufficient
  condition do not resolve the unrestricted weakest-assumption
  question. The separate problem of balancing with arbitrary side
  information in the last paragraph of §IV.5 is not addressed.
- Uffe Haagerup and Magdalena Musat,
  [*On the best constants in noncommutative Khintchine-type inequalities*,
  J. Funct. Anal. 250 (2007), 588–624](https://doi.org/10.1016/j.jfa.2007.05.014),
  is the earlier functional-calculus truncation method cited by
  Regula–Cheng. The new step here is the quadratic coefficient Gram
  bound, not the clipping technique.
- Hao-Chung Cheng, Li Gao, Shi-Bing Li and Hongsen Qiu,
  [*Exponential Analysis for Trace-Distance Errors in Quantum
  Information Theory*, arXiv:2611.34468v1 (25 Nov 2026)](https://arxiv.org/html/2611.34468v1).
  Theorem 24 and Equation (51) give the exact i.i.d. reliability
  exponent for independent random binning. Section V.E,
  around Equation (54), compares that with an affine field-projection
  family under strong **two**-wise independence on a flat source.
  Its \(q=2\), two-output case is precisely the one-row binary
  affine construction, since projecting multiplication gives
  a nondegenerate linear pairing. This is the closest same-source entropy comparison
  we located. It does not address the strong-three threshold, the
  occupancy optima at that threshold, or the pair-Gram hypothesis.
- Bonnie Berger,
  [*The Fourth Moment Method*, SIAM J. Comput. 26(4) (1997),
  1188–1207](https://doi.org/10.1137/S0097539792240005),
  establishes fourth-moment lower bounds on absolute expectations
  of weighted sign sums and illustrates failure of three-wise
  independence in that scalar setting. This is a classical
  three-versus-four precedent; it does not give a CQ pair-Gram
  converse or the non-binary simultaneous-bin results proved here.
- Brendan Pass and Susanna Spektor,
  [*On Khintchine type inequalities for \(k\)-wise independent
  Rademacher random variables*, arXiv:1708.08775](https://arxiv.org/pdf/1708.08775),
  Theorem 3.1 treats upper moment extrema of order \(p\ge2\);
  Remarks 3.3–3.4 give the even-length binary law (balanced signs
  except for rare all-equal cases) and its three-wise independence.
  That known law also attains the binary TV optimum in (2), as
  follows directly from \(|S|\ge S^2/N\) for the binary sign sum \(S\).
- Cindy Courtois and Michel Denuit,
  [*Moment Bounds on Discrete Expected Stop-Loss Transforms, with
  Applications*, Methodol. Comput. Appl. Probab. 11 (2009), 307–338](https://doi.org/10.1007/s11009-007-9048-0)
  ([2006 author version](https://sites.uclouvain.be/IAP-Stat-Phase-V-VI/ISBApub/Actu/2006-11-WP-Courtois_Denuit.pdf)),
  §3.3, Proposition 3.3, Case 2 of the author version. A single
  exchangeable bin count \(B\) has the first three moments of
  \(\operatorname{Bin}(N,1/m)\). Specializing the scalar result to
  threshold \(b=N/m\) gives the lower certificate in (2);
  for \(m\ge3\), its scalar support is contained in
  \(\{0,b,2b,2b+1\}\), since \(\phi_2(0,b)=2b+1-2/m\).
  A sharp scalar optimum does not by itself show that the
  \(m\) counts can be coupled with sum exactly \(N\) for
  every function. The joint hash constructions, especially
  attainment in the stated regimes and the stronger
  exact \(m=3,4\) bound, are the multibin claims here.
- Vladimir Klebanov, Alexander Weigl and Jörg Weisbarth,
  [*Sound Probabilistic #SAT with Projection*, arXiv:1610.08167v1](https://arxiv.org/abs/1610.08167),
  Construction 2.2 and Theorem 2.3
  ([authors' PDF](https://formal.kastel.kit.edu/~klebanov/pubs/qapl2016.pdf)),
  state the strong three-wise binary affine construction, citing
  Carla P. Gomes, Ashish Sabharwal, and Bart Selman,
  *Model Counting: A New Strategy for Obtaining Good Bounds* (AAAI 2006).
  Neither the affine family nor the elementary finite-field rank
  count is claimed new. Its exact pair-Gram norm and role
  in the converse coefficient are made explicit here.
- Mark N. Wegman and J. Lawrence Carter,
  [*New hash functions and their use in authentication and set equality*,
  JCSS 22 (1981), 265–279](https://doi.org/10.1016/0022-0000(81)90033-7),
  §1, for the strong hierarchy. Mikkel Thorup and Yin Zhang,
  [*Tabulation Based 4-Universal Hashing with Applications to Second
  Moment Estimation*, SODA 2004](https://www.cs.utexas.edu/~yzhang/papers/hash-soda04.pdf),
  Introduction and §3, apply four-wise moments to streaming
  second-moment estimation. Jakob Bæk Tejs Houen and Mikkel Thorup,
  [*Understanding the Moments of Tabulation Hashing via Chaoses*,
  arXiv:2205.01453](https://arxiv.org/abs/2205.01453),
  derive moments of scalar tabulation sums. These distinct
  applications do not supply the cq converse stated here.
- Masahito Hayashi and Shun Watanabe,
  [*Uniform Random Number Generation from Markov Chains:
  Non-Asymptotic and Asymptotic Analyses*, arXiv:1503.04371](https://arxiv.org/abs/1503.04371).
  This is an antecedent for classical randomness-generation
  converses via random ensembles, not a statement of this
  CQ spectral relaxation or the strong-three occupancy optimum. Regula–Cheng §IV.3, footnote 1,
  notes that this paper's one-shot converse uses full mutual
  independence under its own “strongly universal₂” terminology.
- [*Sharp Non-Commuting Operator Constants, Quantitative One-Shot
  Converse Sharpenings, and Constructive Lean 4.35.0 Formalization
  for Universal Quantum Randomness Extraction*,
  ARR-2026-58NB9TJZQD9Y4A0Z v1](https://airr.science/papers/ARR-2026-58NB9TJZQD9Y4A0Z/versions/v1/)
  (26 Nov 2026 posting): Theorem B concerns sharpening constants
  under the original \(4^*\) hypothesis, not the relaxation.
  We do not seek the sharp constant at \(C=1\).

This bounded duplicate check was performed on 27 Nov 2026 UTC.
It included the above primary works and searches combining
“privacy amplification”, “three-wise”, “4-universal converse”,
“quadratic Gram matrix”, “flat source”, “balanced bin occupancy”,
and the two November arXiv identifiers. No match was located
for the pair-Gram criterion and its one-sided collision
corollary, or for the stated coupled-bin constructions and nonbinary exact optima.
This is not an absolute priority claim. All case-checking
code is original toy arithmetic; no external data is reproduced.
