# When Poisson demand understates shortages at fractional supply

**Yongxian Zhang (张永贤) · Research draft · November 19, 2026.** AI-assisted analysis with a separate internal mathematical review, not external peer review.

Consider a soup kitchen with supply $K$ and independent diners, each requesting an amount in $[0,1]$. A stockout occurs if total demand $S$ is at least $K$. If two kitchens sell out equally often, must the one with ordinary Poisson total demand use the least soup on average? [Ganesh, Hartline, Sinha and vonAllmen (EC 2024)](https://arxiv.org/html/2402.19292v3) conjectured this comparison. For fractional supplies greater than one, the answer is **no**.

* **A finite counterexample at every interior stockout target.** For every noninteger $K>1$ and every stockout probability $s\in(0,1)$, finite iid bounded demands achieve exactly $s$ but use strictly less soup on average than *any* ordinary Poisson demand with stockout probability at least $s$. For example, with supply $3/2$, let each of three diners independently request $3/4$ with probability $1/4$, and zero otherwise. Availability is $27/32$ and expected fraction consumed is $47/128$. No Poisson mean has both quantities this small.
* **A sharp replacement near full availability.** For fixed $1<K\le2$, among all finite independent bounded demands with prescribed stockout probability $s$, the smallest possible expected amount consumed is asymptotic, as $s\downarrow0$, to
  $$\sqrt{\frac{2s}{\max\{4/K^2,\,1/[(K-1)(3-K)]\}}}.$$
  For $1<K<6/5$, two different positive request sizes, $K-1$ and $1$, do better than using only the size $K/2$. For $6/5<K\le2$, the latter size suffices to leading order. This switching point already appears in [Meester's two-iid-variable extremal theorem](https://arxiv.org/pdf/0808.1669). The proof shows why that two-variable calculation controls *arbitrarily many heterogeneous demands* in the sparse limit.

These results do not disprove the conjecture at integer $K\ge2$, determine the full tradeoff curve there, or contradict the original paper's proved concentration inequalities. Its distinct posted-price and transaction-fee applications are not the claimed counterexample.

**Read:** [theorems, witnesses and proof](PROOF.md) · [prior results, exact source scope and search limitations](SOURCES.md) · [independent internal review](REVIEW.md).

**Reproduce:** `python3 -O verify.py` (Python 3, standard library) gives the [expected output](CHECKS.txt). The checks cover the three-diner rational certificate, the pair inequality and its equality measures, and finite sparse designs. The general conclusions rest on the proof, not finite enumeration. `sha256sum -c SHA256SUMS` verifies the package. No historical-priority guarantee is made.

**中文摘要。** 在非整数容量 $K>1$ 下，对任意指定的售罄概率，都可用有限个独立同分布的需求构造反例：它们同样经常售罄，平均实际消耗却严格低于泊松基准。对于 $1<K\le2$，还给出罕见售罄时所有独立需求中的精确首项；容量低于 $6/5$ 时，两种大小的需求优于单一大小。这不否定整数容量下的全概率猜想。
