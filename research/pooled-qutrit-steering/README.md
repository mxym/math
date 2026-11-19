# Two uniform gaps for qutrit steering via pooled majorization

**Yongxian Zhang.** AI-assisted research draft; independently checked within an AI workflow, not externally peer reviewed. No worldwide-priority claim.

[Yang and Qiao](https://doi.org/10.1038/s41534-026-01204-3) asked whether their direct-sum majorization test for two qutrits approaches the physical projective-steering thresholds of the Werner and isotropic states as the number of measurement settings grows. Neither value can be reached by the witness they optimized, regardless of the number or arrangement of the projective bases.

| State family | Known physical threshold | Threshold required by this witness |
|---|---:|---:|
| Werner | $2/3$ | at least $2/3+4/2223=1486/2223$ |
| Isotropic | $5/12$ | at least $5/12+\delta$ for a fixed $\delta>0$ |

The [Werner proof](PROOF.md) bounds the smallest third of the globally pooled outcomes by an explicit rational inequality. The [isotropic proof](ISOTROPIC.md) treats the largest third: attaining the physical value would force all support bases to share a ray, which is incompatible with saturation. Both results allow weighted settings and fractional ties. Neither determines the exact optimal pooled visibility or changes the physical steering thresholds. The isotropic proof does not estimate $\delta$. The results concern the specified aggregation and measurement alignment, not general steering tests.

See [Werner sources](SOURCES.md), [isotropic sources and earlier qutrit geometry](ISOTROPIC-SOURCES.md), [Werner review](REVIEW.md), [isotropic review and second proof](ISOTROPIC-REVIEW.md), and [a further check of the Laurent proof](ISOTROPIC-ROOT-REVIEW.md). The exact finite checks supplement the analytic proofs; they do not establish the continuum claims. From this directory:

~~~sh
sha256sum -c SHA256SUMS
python3 -O -B verify.py
python3 -O -B rational_check.py
python3 -O -B verify_isotropic.py
python3 -O -B independent_isotropic.py
~~~
