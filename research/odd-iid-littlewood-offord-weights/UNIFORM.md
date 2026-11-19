# Extension: the same failure with a uniform law on a finite integer set

This strengthens the odd-$n$ conclusion of the main proof. The set need not be an interval. Both comparisons use iid samples from the **same uniform set**, not from an interval of the same cardinality.

**Proposition.** Fix an integer $n\ge3$, nonzero integer weights $a_i$ and any finitely supported integer law $p$. Put $Q_a(p)=Q(\sum a_iX_i)$ and $Q_\pm(p)=\max_{\varepsilon_i=\pm1}Q(\sum\varepsilon_i X_i)$ for iid $X_i\sim p$. There are nonempty finite sets $E_M\subset\mathbb Z$ such that
$$
 \liminf_{M\to\infty}\frac{Q_a(U_{E_M})}{Q_\pm(U_{E_M})}
 \ \ge\ \frac{Q_a(p)}{(\sum_i|a_i|)\,Q_\pm(p)}.
$$
Here $U_E$ is the uniform law on $E$. The constants in the proof may depend on the *fixed* $p,n,a$. In particular the main theorem, first choosing $p$ and only then taking $M$ large, gives unbounded ratios for uniform sets at every fixed odd $n\ge3$, with the same fixed coefficients.

**Proof.** Translate $p$ so its finite support $S$ is in $[0,D]$. Set $K=\sum|a_i|\ge n$. Fix an integer $T>KD$. For each $x\in S$ and $1\le y\le M$, independently select the integer $x+Ty$ with probability $p_x$. Distinct pairs represent distinct integers. Every coefficient vector used here is the given $a$ or a sign vector. In either case each total is uniquely identified by its low and high totals $t=\sum c_ix_i$ and $h=\sum c_iy_i$: the diameter of the feasible low totals is at most $KD<T$. Selected samples are drawn with replacement, as required for iid variables.

Write $N_x$ for the number chosen in fiber $x$. With probability tending to one, simultaneously $N_x/M=p_x+o(1)$ and $|E_M|/M=1+o(1)$, by binomial concentration with $S$ fixed (for example take errors $M^{-1/4}$). Under uniform sampling, the distribution of all low sites thus tends to $p$. Choose a low target attaining $Q_a(p)$. Its probability tends to $Q_a(p)$; its high totals take at most $1+(M-1)K$ integer values. Hence
$$
 Q_a(U_{E_M})\ \ge\ \frac{Q_a(p)-o(1)}{1+(M-1)K}.
$$

For a sign vector and prescribed $(t,h)$, denote by $Z$ the number of ordered selected $n$-tuples at these totals. For a fixed low tuple, at most $M^{n-1}$ high tuples sum with these signs to $h$ since the last coordinate is determined by the others. At any tuple with all *sites* $(x_i,y_i)$ distinct the expected indicator of selection is exactly $\prod_i p_{x_i}$. For every fixed pair of positions required to coincide, their high labels become one variable and the high equation is still nontrivial: at least one of the $n-2\ge1$ other positions retains coefficient $1$ or $-1$. There are therefore at most $M^{n-2}$ high choices in that exceptional class for each low tuple. Summing over finitely many site pairs and low tuples, including repetitions just once or bounding them by the union bound, gives uniformly
$$
 \mathbb E Z\ \le\ M^{n-1}\mathbb P_p\!\left(\sum\varepsilon_iX_i=t\right)+O(M^{n-2}).
$$

Changing one site selected or unselected changes $Z$ by at most $n|S|^{n-1}M^{n-2}$: specify one occurrence of that site, choose the other low coordinates and all but one remaining high coordinate, and the last coordinate is determined. The bounded-differences inequality on $|S|M$ independent selectors now gives
$$
 \Pr\{Z>\mathbb EZ+ M^{n-1-1/4}\}\le \exp(-c\sqrt M)
$$
for some $c>0$ independent of the totals and signs. There are finitely many low targets, $2^n$ sign choices and $O(M)$ possible high targets. A union bound and $|E_M|/M\to1$ show that with probability tending to one every signed atom is at most $(Q_\pm(p)+o(1))/M$. For every large $M$ choose a realization with both properties. This proves the proposition.

The uniform-set conclusion concerns maximum **representation multiplicities of the fixed set**. The theorem that an interval optimizes multiplicity among all sets *of fixed sizes* is different: it does not compare coefficients for the same set. The construction is existential for uniform sets; the rational weighted counterexample in the main proof is explicit.
