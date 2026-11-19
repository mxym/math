# For each coefficient below two, one fixed chore-cost law has a failing subsequence

Can a universal constant smaller than 2 guarantee an envy-free division of independent random chores? **No, for the full two-sided PDF-bounded class.** Fix any $1<c<2$. There is a single distribution $D_c$ on $[0,1]$ and an infinite sequence of market sizes with $m\ge cn$ and $m/n\to c$ such that with probability tending to one, no envy-free division exists. The $nm$ costs are independent draws from that same $D_c$ at every size, and its density is bounded above and below by fixed positive constants. The distribution can change with the proposed coefficient $c$, not with the size of a given market in the sequence.

[Manurangsi and Suksompong](https://doi.org/10.1137/25M180161X) had proved high-probability existence for **every** such law when $m\ge2n$ and asked whether that coefficient could be reduced. The two results together show that 2 is the best distribution-independent sufficient coefficient. They do **not** give a threshold for uniform costs, for every smooth density, or even for all market sizes under the constructed law.

**Why envy becomes unavoidable.** Below $2n$ some agents must receive only one chore. If a singleton is cheaper to an agent than every possible pair, that agent must take it or take an earlier singleton. Conflicting claims can thus rule out one singleton after another. Our fixed density has bands accumulating at zero. At selected market sizes, many agents simultaneously have long prefixes of cheap chores, and the conflicts certify that more chores must be placed in bundles of size at least two than the market allows.

- [Proof](PROOF.md) and [scope of prior results](SOURCES.md).
- [Independent internal review](REVIEW.md), [regression results](CHECKS.txt). Run python -O verify.py and python -O finite_requests.py; the Python standard library suffices. These finite checks test ownership and arithmetic, not the asymptotic probability theorem.

AI-assisted research with independent internal checking. It has not undergone external peer review, and no priority guarantee is claimed.
