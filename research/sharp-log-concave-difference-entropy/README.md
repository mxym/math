# How much entropy can an independent difference add?

Draw two independent numbers $X,X'$ from the same distribution and subtract them. The result is symmetric even if the original law is not. How much more uncertain can it be? For **log-concave distributions on the integers**, the sharp Shannon entropy increase is **one bit**: the difference adds strictly less than one bit to each individual law, but one-sided geometric laws can get arbitrarily close. The statement also holds for every positive Rényi order, including min-entropy.

**On the real line**, the same one-bit bound holds for every positive order, and a one-sided exponential law attains it. At each order strictly between zero and one, the only maximizers are translations, rescalings or reflections of that exponential. The continuous result at orders at least one, including the Shannon classification used here, was already known. Throughout, formulas use natural logarithms, so one bit is $\log 2$.

The key fact is about *intervals*, not entropy. For a log-concave integer law, the mass of $X'-X$ in the $2k$ consecutive sites from $1-k$ to $k$ is at least the original law's largest mass on any $k$ consecutive sites. This follows by applying a familiar statistical comparison to a law and its translate. It gives an inequality for every ranked sum of probabilities, with all Rényi bounds following from that single statement.

The discrete result answers the difference question (63) in [Han–Zhan–Zhou–Zhu, §VIII-B](https://arxiv.org/html/2610.15716v1); those authors credit Jiange Li with suggesting the integer-valued direction. The continuous result determines their (61) **only in dimension one**. Neither settles the positive-sum questions, unequal input laws, higher-dimensional low orders, or stability. See [the proof and prior results](PROOF.md), [independent internal mathematical audit](REVIEW.md), and [search coverage](SEARCH.md).

**中文摘要。** 若 $X,X'$ 是取值于整数的独立同分布对数凹随机变量，则对任意正阶 Rényi 熵（含 Shannon 熵、最小熵），差 $X'-X$ 的熵增严格小于一比特；几何分布族说明常数最优但不取到。对连续实线上的对数凹密度，低于一阶时最优常数同为一比特，且恰由单侧指数分布的非退化仿射像取到。结果不涉及异分布、正和或高维低阶情形。

**Reproduction.** With the Python 3.8+ standard library, run:

```sh
python3 -BO verify.py
python3 -BO check_roc.py
```

The first checks exact product overlaps; the second computes exact areas of threshold-comparison polygons with the lattice tie correction. These finite tests complement the mathematical proof; they do not replace it.

**Status:** AI-assisted research draft. Independently checked within the project by AI, not externally peer reviewed or formally verified. No guarantee of historical priority.
