# No common sublinear envelope for the logarithm of the fixed-law prophet ratio

More precisely, there is no common sublinear envelope for the logarithms: for every nonnegative sequence $h(n)=o(n)$ there is **one** probability law $F$ on $[0,1]$, without atoms, and an increasing sequence $n_j$ such that
$$
  \log(G_{n_j}(F)/M_{n_j}(F))>j\max\{1,h(n_j)\}\qquad(j\ge2).
$$
The law may depend on $h$ but does not depend on the horizon once constructed. This complements the pointwise $\log(G_n(F)/M_n(F))=o(n)$ for every nonnegative integrable law not identically zero, proved in PROOF.md. The lower statement is along a subsequence; the law here need not have full support on the interval.

Let $p_j=2^{-j}$ for $j\ge1$. Assign this mass uniformly to each interval $[A_j,2A_j]$; begin with $A_1=1/4$, and choose disjoint, rapidly shrinking subsequent intervals as follows. At stage $j\ge2$ the eventual mass below the $j$th interval is $\sum_{i>j}p_i=p_j$, its own mass is $p_j$, and the mass of all higher intervals is $q=1-2p_j>0$. Abbreviate $p=p_j$, $H=A_{j-1}$, and $v=q/(1-p)\in(q,1)$. For the current horizon candidate $n$ set
$$
 A=v^n,\qquad b=\left\lfloor n\,\frac{\log v}{2\log q}\right\rfloor .
$$
Then $0<b<n$ for all sufficiently large $n$. Because $q^b\ge v^{n/2}$, one has $Hq^b\ge A$ for all sufficiently large $n$, as $H>0$ is fixed at this step. Also $b/n$ tends to a positive constant and $-\log(1-p)>0$. We may therefore take $n=n_j$ larger than all previous horizons and large enough that
$$
 H q^b\ge A,\qquad
 b[-\log(1-p)]-\log4> j\max\{1,h(n)\},\qquad 2A < H.
$$
Starting with $j=3$ also require $2A\le q_{j-1}^{n_{j-1}}$, where $q_i=1-2p_i$. This is possible since $A\downarrow0$ as $n$ grows. Set $A_j=A$ and proceed. The intervals are disjoint and determine the claimed atomless probability law, with all values at most one. At each stage every future value lies at or below $q_j^{n_j}$.

Fix such a stage. With probability $q^n$ all observations are in the high intervals and the prophet pays at most one. If no future (lower) interval is seen but a middle value is, the minimum is at most $2A$; the probability is at most $(1-p)^n$. If any future value is seen, the cost is at most $q^n$. Hence
$$
 M_n(F)\le q^n+2A(1-p)^n+q^n=4q^n.
$$
For an online lower bound couple each draw with the smaller ternary variable $Y$, equal to $0,A,H$ on the low, middle, high intervals, respectively. Cost monotonicity follows directly by induction on the Bellman recurrence $x\mapsto\mathbb E\min(X,x)$, including the initial one-draw mean; it does not assume an online rule fails to observe its exact costs. Write $g_i$ for the optimal $i$-draw cost for $Y$. Then $g_1\ge qH$, all $g_i\le H$, and $g_{i+1}\ge qg_i$ because the high draws alone cause this cost. Consequently $g_b\ge q^bH\ge A$. For $0\le x\le A$, the Bellman map of $Y$ is exactly $(1-p)x$, since both positive outcomes are at least $A$. Its monotonicity implies that restarting at $A$ gives a lower bound on all further iterates, so $G_n(F)\ge g_n\ge A(1-p)^{n-b}$. Dividing by $4q^n$ gives $(1-p)^{-b}/4$, as promised.

This construction uses the familiar low/middle/high cost mechanism from the horizon-dependent hard instances of Esfandiari–Hajiaghayi–Liaghat–Monemizadeh. The distinction is retaining every scale in a *single* atomless law while beating an arbitrary prescribed sublinear logarithmic envelope on a subsequence. It is not a single fixed-law exponential-in-$n$ lower bound.
