# A shortest-path scaling cut for dyadic addition-chain stability

An addition chain starts at \(1\), is strictly increasing, and obtains each new value as a sum of two earlier values, possibly equal. A star chain requires that one summand be the immediately preceding value. Write \(\ell\) for either length function consistently.

**Theorem.** Let \(n\) be odd, with \(\lambda=\lfloor\log_2 n\rfloor\) and \(\nu\) ones in its binary expansion. Define the stable normalized length and its first index by
\[
 \ell_{\rm st}(n)=\min_{j\ge0}\{\ell(2^j n)-j\},\qquad
 J(n)=\min\{j\ge0:\ell(2^j n)-j=\ell_{\rm st}(n)\}.
\]
With \(r=\ell_{\rm st}(n)-\lambda\) and \(d=\lfloor 10r/3\rfloor\),
\[
          J(n)\ \le\ d\lambda+(d+1)(2^d-\nu).
          \tag{1}
\]
One may replace \(r\) by \(\ell(n)-\lambda\) or by \(\nu-1\) to obtain a bound without first knowing the stable length. This applies to ordinary and star chains. For an even starting integer, apply the bound to its odd part and subtract the already present number of trailing zero bits, with a floor at zero.

The main ingredient is a constructive certificate on an individual chain. A shortest path in its dependency graph gives the *largest* number of powers of two removable by nodewise scaling with all non-doubling gates retained, and gives a shortening by at least that many operations. The proof bypasses the factorial-sized coefficient bound in our [previous effective-stability proof](FactorEffectiveAdditionChainStability.md), yielding \(O(r\lambda+r\,2^{10r/3})\) instead of a factorial function of \(r\).

[Altman](https://arxiv.org/abs/1409.1627) proves eventual stabilization and asks about effectivity. [Thurber–Clift](https://doi.org/10.1016/j.disc.2020.112200) use formal dependency graphs and vector truncation for chain bounds; this note uses a different shortest-path problem for halving. [Clift's trailing-zero conjecture](https://additionchains.com/DoublingConjecture.html) would give the much sharper \(J(n)\le\max(0,\lambda-6)\); he reports the corresponding restricted check for at most five small steps using template enumerations. Bound (1) neither establishes that threshold nor resolves the Scholz–Brauer conjecture.

## 1. Exact scaling of a fixed dependency graph

Fix a chain of length \(L\), fix defining operands for every operation, and retain the vertices that are ancestors of the target. Call a gate a **doubling** only if it doubles the immediately preceding value in the original chain. Treat it as having one predecessor (the value it doubles); all other gates have two summands, even if they double some older value. Every vertex is reachable from the initial \(1\) along dependency edges.

Build a weighted directed graph on these vertices. For a doubling \(u\longmapsto v\) give the forward edge weight 1 and the backward edge weight 0. For each of the two summands in any other gate, give its edge to the gate and the reverse edge weight 0. Let \(h(v)\) be the shortest-path distance from the initial vertex to \(v\). All distances are finite nonnegative integers. For each doubling \(u\longmapsto v\), the weighted triangle inequalities give \(0\le h(v)-h(u)\le1\). Each other gate and its summands have the same \(h\).

Consider an integer label function \(H(v)\ge0\) with \(H(1)=0\), the same inequalities on doubling edges, and the same equalities on all other edges. If a vertex originally has value \(a_v\), replace it by \(a_v/2^{H(v)}\). Inducting along original dependencies proves integrality. A doubling stays a doubling when the labels agree, or becomes an equality of its two normalized values when the label increases by one. A non-doubling retains its two summands and remains an addition because all three labels agree.

Thus if the terminal label is \(A\), the target is divided by \(2^A\), and along any original dependency path from \(1\) to the target at least \(A\) distinct doubling operations disappear: the label only changes on doublings, and each increase is by one. Remove all such operations by replacing references to them by references to their retained ancestors with the same numerical value. For an ordinary chain, discard repeated values and sort. Each needed sum has two strictly smaller positive operands and all retained values are at most the target since they precede it along reweighted dependencies. This produces a chain of length at most \(L-A\). For a star chain all steps are ancestors and the original order is still increasing after collapsing consecutive equalities. Each surviving step uses the immediately preceding surviving value, so the result is again star.

The labels \(H=h\) are valid. Conversely any valid labels satisfy \(H(q)-H(p)\le w\) on each graph edge \(p\to q\) of weight \(w\), so summing along a shortest path gives \(H(v)\le h(v)\). This proves the exact terminal maximum, *for this restricted scaling operation*. Truncating \(h\) at any integer \(0\le A\le h(\text{target})\) gives exactly \(A\) powers removed. This is not a claim that other transformations cannot remove more operations or more powers. The shortest-path certificate itself uses only weights zero and one.

## 2. Bounding that shortest path by exponent spread

Unfold the retained computation into powers of two: the initial \(1\) contributes exponent 0, each designated doubling shifts all exponents by one, and any other gate concatenates the exponent multisets from its two summands. At a vertex \(v\), denote the least and greatest exponent before carrying by \(\mu(v)\), \(M(v)\). For the terminal vertex \(t\), put \(R=M(t)-\mu(t)\).

For any ancestor vertex \(v\), select one dependency path to the target. Along that path exponents are shifted only by doublings; at a non-doubling the old multiset is copied as part of the new one. Thus some translate of the whole multiset at \(v\) occurs in the target multiset, and \(M(v)-\mu(v)\le R\).

Take a simple shortest path in the weighted graph from \(1\) to \(t\); deleting cycles cannot increase its weight. The potential \(\mu\) changes as follows along its edges.

* A forward doubling contributes exactly \(+1\), its edge weight. The reverse contributes \(-1\).
* At a forward edge into a non-doubling, \(\mu\) cannot increase. At a reverse edge from such a gate to a summand, the increase is at most the exponent spread at the gate, which is at most \(R\).

A simple path encounters at most one reverse exit from each non-doubling gate. If there are \(e\) retained non-doublings, summing the changes from \(\mu(1)=0\) yields
\[
              h(t)\ \ge\ \mu(t)-eR.                           \tag{2}
\]
For target \(2^j n\), let \(q\) be the number of pre-carry leaves at the target, counting multiplicity. The binary unfolding has at most \(e\) branchings on a root-to-leaf path, hence \(q\le 2^e\). There are exactly \(q-\nu\) binary merges in a full normalization. A leaf exponent increases by at most \(q-\nu\) on its path to a final bit, so \(\mu(t)\ge j-(q-\nu)\). Positivity implies \(M(t)\le j+\lambda\), since otherwise a single term exceeds the target. Together with (2) this proves
\[
        h(t)\ \ge\ j-e\lambda-(e+1)(q-\nu).
        \tag{3}
\]
In particular a chain with an excessive trailing exponent can lose all the excess indicated by (3) at once. A convenient sharper input-specific bound is (2), using minimum and maximum exponents directly without enumerating leaves.

## 3. From a fixed chain to the first stable index

The normalized lengths \(\ell(2^j n)-j\) form a nonincreasing integer sequence bounded below, because appending a doubling costs one step, and any length-\(L\) chain ends at at most \(2^L\). Take a shortest chain at \(j=J(n)\); its length is \(J(n)+\lambda+r\).

The number of non-doublings in such a chain is at most \(\lfloor10r/3\rfloor\). To see this, a maximal run of non-doublings starts after a doubling with value \(a\) and previous value \(a/2\). A non-doubling has output at most the sum of the two most recent values. The first ratio in the run is at most \(3/2\), and induction bounds the net ratio for \(k\) steps by \(\varphi^k\), where \(\varphi=(1+\sqrt5)/2\). Multiplying over runs and doublings gives \(2^j n\le2^L(\varphi/2)^{e'}\) for \(e'\) original non-doublings. Since \(\varphi<34/21\) and \((21/17)^{10}>2^3\), we have \(\log_2(2/\varphi)>3/10\). Taking logarithms gives \(e'\le\lfloor10r/3\rfloor\), hence \(e\le d\).

Use \(q\le 2^e\), \(q\ge\nu\) in (3): the right-hand side is at least \(J(n)-d\lambda-(d+1)(2^d-\nu)\). If this were positive, Section 1 would give a length-\(L-1\) or shorter chain for \(2^{J(n)-1}n\), contradicting the first attainment of \(\ell_{\rm st}(n)\). This proves (1). The binary method gives \(\ell(n)-\lambda\le\nu-1\) even in a star chain, which justifies the unconditional replacement for \(r\). For fixed \(r\), the cutoff is linear in the bit length of the odd part. Computing exact shorter chains inside this cutoff can still be expensive.

## 4. Replaying the local certificate

Run `python3 verify_factor_addition_chain_scaling_cut.py` with standard Python 3. The check exhausts small formal ordinary and star chains, uses independent Bellman–Ford distances on the small graphs to confirm the zero-one deque computation, and tests scaling and subsequent deletion of operations on large seeded shifted chains. It verifies the target and every addition by integers. It is a cross-check of the local certificate, not a computation of stable lengths for the large seeded inputs.
