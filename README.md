# Three independent third turns in six-dimensional kissing codes

Suppose a set of unit vectors in six dimensions has pairwise angles at least 60°. Split the space into three orthogonal planes. Rotating **any one** of them by 120° with the other two fixed must preserve the set. No transitivity, antipodality, or root subsystem is assumed.

| Number of 27-point orbits using all three planes | Exact maximum |
|---:|---:|
| 0 | 60 |
| 1 | 57 |
| 2 | 72 (the classical E₆ root set) |

More than 60 points force a **unique** extension to the 72-point E₆ code in the same space. Size 60 can fail to extend; up to isometry the 60-point non-E₆ example is unique. No uniqueness claim is made for the 57-point extremizer. These results do not cover a single simultaneous third turn and do not determine the unrestricted six-dimensional kissing number.

- [Proof, witnesses, and the analytic orbit exclusions](KissingThreeIndependentThirdTurns.md)
- [Author's exact checker](verify_kissing_three_independent_third_turns.py) and [separately implemented audit](independent-six-three-third-turns.py)
- [Independent review scope](AUDIT.md)

Run normal standard Python (no third-party packages; do not use `-O`):
```sh
python3 verify_kissing_three_independent_third_turns.py
python3 independent-six-three-third-turns.py
sha256sum -c SHA256SUMS
```
The finite checkers verify explicit configurations, not the continuum of all codes: the continuum upper bounds are proved in the manuscript.

**Context.** The 72-root configuration and its local rigidity are classical; see Cohn, Jiao, Kumar and Torquato, [Rigidity of spherical codes, §§3 and 4.3](https://msp.org/gt/2011/15-4/gt-v15-n4-p11-p.pdf). They also discuss noncongruent 72-point configurations in the unrestricted setting. The [earlier point-transitive theorem](https://github.com/mxym/math/blob/21ddf28035c77f159f6ea0032d7b0d868ab78d4a/research/euclidean-tensor-geometry/KissingSixVertexTransitive.md) assumes a different group property. This archive is about the independent three-plane action and its sharp rigidity threshold.

Research source: [4b782c9c](https://github.com/mxym/math/commit/4b782c9cb9f76b74fbb231d9fce0c91e7523a83d).
