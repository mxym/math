# Bell-to-Bell preservation: uniform approximation and controlled gates

**研究草稿。** 任意两体酉门能否把某个最大纠缠态精确送到另一个最大纠缠态？局部维数为素数幂时，已发表的 Floer 理论给出肯定答案。本稿用它推出适用于所有维数的近似界；对于任意受控门，已有旗流形理论给出精确结果。一般混合素因子维数下的精确问题仍未在这里解决。

A Bell state here means *any* maximally entangled pure state on two local systems of dimension $d$, not a member of one prescribed basis. The question is whether every joint unitary $V$ takes some Bell input to a Bell output. This is the two-splitting conjecture of [Puchała et al., §V](https://doi.org/10.1103/PhysRevA.92.032109), restated geometrically by [Życzkowski, §III(d)](https://arxiv.org/pdf/2212.03903#page=4) and called UBB by [Brahmachari et al., Eq. (18)](https://arxiv.org/pdf/2210.13307#page=4).

### 1. What is guaranteed for every gate?

For $d\ge 2$, let $q$ be the smallest prime power at least $d$ and write $k=q-d$. Then $0\le k<d$. For every joint unitary on $\mathbb C^d\otimes\mathbb C^d$:

* Some **Bell input** has output with overlap amplitude at least $1-k/d$ with a Bell target. The guaranteed squared fidelity is $(1-k/d)^2$.
* Some pure input has **each of its two reduced density matrices preserved exactly** by the gate and has entanglement min-entropy at least $\ln(d-k)$, in nats. Equal marginals alone are trivial for an eigenvector; the high entanglement is the additional guarantee.

The two witnesses are **not guaranteed to be the same**. For example, $d=6$, $q=7$ give amplitude at least $5/6$ (fidelity at least $25/36$) and min-entropy at least $\ln5$, not an exact Bell-to-Bell theorem in dimension 6. As $d$ tends to infinity, both the amplitude deficit and the entropy deficit from $\ln d$ are $O(d^{-19/40})$, uniformly over the choice of gate.

[Proof: extension, compression and rounding](COMPRESSION.md). The exact prime-power input is prior work by [Iriyeh](https://arxiv.org/abs/1401.0777), [Evans–Lekili](https://doi.org/10.1090/jams/909), and [Smith](https://arxiv.org/abs/1905.04005); the rate uses [Baker–Harman–Pintz](https://doi.org/10.1112/plms/83.3.532).

### 2. What is exact for controlled gates?

For a gate controlled on an orthonormal basis, with arbitrary (not necessarily commuting) branch unitaries $U_i$, one can choose an orthonormal basis $x_i$ such that $U_i x_i$ also form an orthonormal basis. This gives an exact Bell-to-Bell input in every dimension. The ordered lines of a solution form a flag. If all intersections are transverse, there are at least $d!$ solution flags, and commuting examples attain this count. This is **not** a count of physical states or a claim that the gate preserves a complete Bell basis.

[Proof and sharpness example](CONTROLLED.md). The existence and signed count are applications of [An–Đoković’s universal-subspace results](https://arxiv.org/abs/0802.1915), not a new flag-intersection theorem.

### Review and reproduction

AI-assisted research draft with a [separate internal AI review](REVIEW.md); not externally peer-reviewed. A limited literature search did not locate the same finite-dimension compression formulation. That does not establish priority. Exact UBB for arbitrary gates in a fixed dimension having at least two distinct prime divisors is **not** proved or disproved here.

From this directory, using Python 3.12 (the second script also requires SymPy 1.14):

```sh
python -BO check.py
python -BO independent.py
```

Both scripts fail by explicit exceptions, including under Python optimization. They test finite instances and algebraic identities only; they do not verify the cited Floer theorem or replace the analytical proofs.
