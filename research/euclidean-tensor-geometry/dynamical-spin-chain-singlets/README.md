# Three exact results on dynamical spin-chain supersymmetry

**Yongxian Zhang** ([ORCID 0009-0000-3864-3536](https://orcid.org/0009-0000-3864-3536)).  
2026-11-26. AI-assisted proof development and internal mathematical checks; no external peer review claimed.

This archive studies three families from [Hagendorf's *Spin chains with dynamical lattice supersymmetry*](https://arxiv.org/abs/1207.0357). They are separate from the earlier [even-parity Fateev–Zamolodchikov count](https://github.com/mxym/math/releases/tag/fateev-zamolodchikov-singlets-v1.0.0) and [mod-three model](https://github.com/mxym/math/releases/tag/hagendorf-mod-three-singlets-v1.0.0).

1. [Higher-spin trigonometric singlets](TRIGONOMETRIC.md): for every spin, length and allowed twist, exact dimensions by magnetization in the signed supersymmetry momentum sector. At zero twist, odd lengths give one per allowed local magnetization and even lengths give none. At nonzero twist the sole case is one neutral singlet at every even length.
2. [Odd-parity Fateev–Zamolodchikov singlets](ODD-PARITY-FZ.md): proves the two states asserted in Conjecture 4.8 and counts exactly two at the original twisted momentum \(-1\) for odd lengths. This does not exclude other momenta. At the trigonometric value the two are in magnetizations \(\pm1\).
3. [The deformed \(t\)–\(J\) chain](DEFORMED-TJ.md): full kernel in every length \(N\ge2\), for both allowed twists and all real nonzero deformations, and the exact undeformed kernel for all twists. A lower spectral gap bound \(4\min(\zeta^2,1)\) is sharp for twist zero or \(|\zeta|\le1\) or even length, within the two deformed twists. No exact value is asserted for the remaining odd, \(\pi\)-twisted, \(|\zeta|>1\) regime.

The first two proofs use the [common cyclic normalization argument](CYCLIC-NORMALIZATION.md), but different local algebras. The third uses positivity and hopping in fixed hole-number sectors. No claim of literature priority is made. Run `node verify.js` for independent finite-field sample checks; none of the theorems rely on them.

**Research follow-up.** [Odd-length, twisted t–J gap](ODD-PI-TJ-GAP.md): exact weak and strong coupling branches, noncommuting limits, the full three-site formula, and bounds elsewhere. This later addition is not in the preceding frozen release.
