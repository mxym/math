# Exact supersymmetry singlet counts in the Fateev–Zamolodchikov spin-one complex

**Yongxian Zhang** ([ORCID 0009-0000-3864-3536](https://orcid.org/0009-0000-3864-3536)).  
2026-11-26. AI-assisted proof development and mathematical cross-checking; no external peer review claimed.

We determine the number of zero-energy states of the dynamical supersymmetry Hamiltonian of [Hagendorf, §§4.1–4.2 and Conjecture 4.2](https://arxiv.org/pdf/1207.0357), for every real coupling pair \((x,y)\) and chain length \(s\ge1\), in the signed shift sector \((-1)^{s+1}\) at twists \(0\) and \(\pi\). At \(\pi\) we impose the even magnetic parity required by the dynamical complex; at \(0\) no magnetic parity restriction is imposed.

| Couplings | Twist \(0\) | Twist \(\pi\), even magnetic parity |
| --- | ---: | ---: |
| \(x^2\ne y^2\) | \(0\) | \(1\) |
| \(x^2=y^2\ne0\) | \(1\) | \(1\) |
| \(x=y=0\), \(s\) odd | \(s+1\) | \(s\) |
| \(x=y=0\), \(s\) even | \(s\) | \(s+1\) |

At the isotropic point the single \(\pi\)-twist state has magnetic charge zero. In other non-light-like couplings the even sector is the natural statement; individual magnetization need not be conserved. “Singlet” here means a simultaneous kernel of the dynamical supercharge and the preceding adjoint, not necessarily a physical total-spin-zero representation.

1. [Isotropic, twist zero](UNTWISTED.md): the dynamical complex is the dual of the reduced cyclic complex of the two-by-two matrix algebra, hence exact by cyclic Morita invariance.
2. [Isotropic, twist \(\pi\), and all non-light-like couplings](TWISTED-AND-DEFORMED.md): the inner-twisted cyclic complex is computed by a twisted trace. The scalar inclusion becomes zero because the twist has trace zero, giving exactly one reduced class in every degree. An invertible local change of basis transports the two cohomologies to all \(x^2\ne y^2\).
3. [Singular couplings](SINGULAR.md): a diagonal positive local density treats the nonzero light-like lines; graded antisymmetry treats the origin. Hagendorf already obtained the untwisted origin counts and the existence of a light-like singlet at twist \(\pi\); these parts are explicitly credited in the proof.

This proves the singlet assertions in Conjecture 4.2 and determines the specified sectors also at the singular couplings. It does not resolve Conjecture 4.1 on the rest of the spectrum, the alternating-sign-matrix formulas, or other twists or sectors. The same exact cyclic complex was used in the independent [all-length tensor rank result](https://github.com/mxym/math/releases/tag/periodic-physical3-bond2-all-lengths-v1.0.0). The check `node verify.js` tests representative cases through \(s=7\); it is not used for the all-length conclusions.
