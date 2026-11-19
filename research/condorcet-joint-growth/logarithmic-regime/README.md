# A parity-dependent limit for Condorcet winners with logarithmically many voters

In an election with $m$ independent uniform rankings of $n$ candidates, let $Q(m,n)$ be the probability that one candidate wins **every** pairwise contest by a strict majority. An even-electorate tie is not a win.

Suppose $m/\log n\to c$ for a fixed $0<c<\infty$, with natural logarithms. Let $a>0$ be the unique root of $a\coth a-1=1/c$, and let $\eta=m\bmod 2$. Then
$$
 Q(m,n)\ \sim\ \frac{\sqrt m}{n}\,\frac{\sqrt{6\pi}}9
 \frac{(1-e^{-2a})^2 e^{2a\eta}}{\coth a-a/\sinh^2 a}.
$$
In particular, compare an odd electorate with an adjacent even electorate **at the same $n$**. If both voter counts divided by $\log n$ tend to $c$, the odd-to-even probability ratio tends to $e^{2a}$. Thus the tie rule affects the leading multiplicative constant, not just a smaller correction. The formula does not cover $c=0$ or $c=\infty$.

The earlier [joint-growth note](../README.md) gives an exponent but not this equivalent. The proof combines a shared shift of all voters’ log odds with a change of variables onto a slice where the mean conditional vote count is exactly $m/2$. A local limit estimate there retains the half-lattice step distinguishing odd from even voter totals. The [source comparison](SOURCES.md) credits prior log-odds and ranking representations, the Gaussian limit of May, Kim–Shin’s monotonicity theorem, known finite-electorate parity effects, and equivalent skyline terminology.

[Proof](PROOF.md) · [Independent internal review](REVIEW.md) · [Expected regression results](CHECKS.txt). Run both scripts with the Python standard library: python -O verify.py and python -O independent.py. Their finite tests check identities, not asymptotic estimates.

AI-assisted research with independent internal review; not externally peer reviewed. No guarantee of priority.
