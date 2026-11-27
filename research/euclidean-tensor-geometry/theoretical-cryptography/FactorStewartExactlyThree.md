# Exactly three perfect powers in the square-root interval

This supplement strengthens the [explicit proof of Stewart's existence conjecture](FactorStewartSquareCubeFifth.md). For every fixed $1/\sqrt5<\lambda\le1$, the same family gives
$$
\left(\frac{\lambda-1/\sqrt5}{2\sqrt5}+o(1)\right)X^{1/30}
$$
distinct square starts $N\le X$ for which $[N,N+\lambda\sqrt N]$ contains **exactly** three distinct perfect powers: the three constructed in the original proof. We do not assert that all sufficiently large square-root intervals contain at most three.

Use the notation $F_n=(125n^6+3n)^5$, $C_n=(3125n^{10}+125n^5+1)^3$, $q_n=\lfloor\sqrt{F_n}\rfloor$, and consider $I_n=[q_n^2,q_n^2+q_n]$. Among the successful parameters for the given $\lambda$, the subinterval of $I_n$ of length $\lambda q_n$ contains the square $q_n^2$, the fifth power $F_n$, and the cube $C_n$. For all large $n$, every $I_n$ contains at most one square, one cube and one fifth power, since the spacings of those powers near $q_n^2$ exceed $q_n$. If any other perfect power occurs, its exponent has a prime divisor $e\ge7$; an exponent divisible by $2$, $3$ or $5$ would already give a square, cube or fifth power.

For a fixed prime $e\in[7,29]$, suppose $u^e\in I_n$. Both $u^e$ and $F_n$ are within $O(\sqrt{F_n})$ of one another, whether or not $n$ is a successful parameter. The mean value theorem, applied to the $e$-th root, gives
$$
|u-F_n^{1/e}|\ll_e F_n^{1/e-1/2}\longrightarrow0.
$$
On the other hand
$$
F_n^{1/e}=5^{15/e}n^{30/e}+O_e(n^{30/e-5}).
$$
The error tends to zero, and $30/e$ is positive and not integral. Consequently the fractional parts of $F_n^{1/e}$ are equidistributed. In particular the proportion of parameters up to $T$ for which $I_n$ contains an $e$-th power tends to zero: for each fixed $\epsilon>0$, all sufficiently large such parameters have $\|F_n^{1/e}\|\le\epsilon$, and the upper density of these is at most $2\epsilon$.

For completeness, the equidistribution fact used here follows directly from Weyl's criterion and van der Corput's differencing inequality. If $0<\beta<1$ and $c\ne0$, comparing the sum of $e^{2\pi i h c n^\beta}$ with its integral costs $O_{c,h}(T^\beta)$ by integrating the absolute derivative. Integration by parts bounds the integral by $O_{c,h}(T^{1-\beta})$ for each fixed $h\ne0$, so both are $o(T)$. For nonintegral $\gamma>1$, take $\lfloor\gamma\rfloor$ positive finite differences with fixed shifts. The result is a nonzero constant times $n^{\{\gamma\}}$ plus $O(n^{\{\gamma\}-1})$, by repeated integration of the derivatives of $n^\gamma$. The error is $o(1)$. Successive applications of the differencing inequality lift the vanishing normalized exponential sums back to $c n^\gamma$. Finite errors tending to zero do not affect Weyl's criterion.

Finally deal with all $e\ge31$ at once. For $n\le T$ every $I_n$ lies below $O(T^{30})$. Intervals for sufficiently large distinct $n$ are disjoint: $q_n^2=F_n+O(n^{15})$ and $F_{n+1}-F_n\sim30\cdot5^{15}n^{29}$. Thus the number of parameters up to $T$ with an $e$-th power in $I_n$ for any $e\ge31$ is $O(T^{30/31}\log(2T))=o(T)$, by counting all such powers up to a constant times $T^{30}$, even without restricting $e$ to be prime. The finitely many smaller exponents above and this last estimate remove only $o(T)$ of the parameters. The exact count from the original result is unchanged in its main term.

The [finite check](verify_factor_stewart_exactly_three.js) makes 180,380 integer assertions, enumerating powers by exact roots on 2,500 fixed parameters. All 667 successes for $\lambda=1$ have exactly three powers in this sample. The density-zero arguments above, not the sample, exclude fourth powers for all but $o(T)$ parameters in the family.
