# Quadratic speed bound for tight two-entry Lonely Runner modifications

**Yongxian Zhang.** AI-assisted proof development and internal checks; no external peer review or priority claim.

For a finite set \(V\) of positive integer speeds, write
\[
\mathrm{LR}(V)=\max_{t\in\mathbb R}\min_{v\in V}\|vt\|,
\]
where \(\|\cdot\|\) denotes distance to the nearest integer.

**Theorem.** Let \(n\ge5\), let \(1\le r<s\le n-1\), and set \(B=[n-1]\setminus\{r,s\}\). If \(n\le u<v\) and \(\mathrm{LR}(B\cup\{u,v\})\le1/n\), then
\[
v\le130(n-1)^2.
\]
If \(r=1\), the only such case for \(n\ge5\) is \(n=5,\ s=3,\ (u,v)=(6,8)\), giving the scaled consecutive set \(\{2,4,6,8\}\). This answers the polynomial-bound alternative in [Yuhan Zhang, Question 8.2](https://arxiv.org/html/2608.13599v3#S8) for exactly two replacements, even without assuming the instance attains \(1/n\). It also classifies the \(r=1\) subcase of Question 8.1 in this range. The asymptotic order, the remaining classification, and the cases of three or more replacements are not settled. In the degenerate case \(n=3\) both original speeds can be deleted, and scaling \(\{1,2\}\) gives no bound on the replacements; the theorem's lower threshold avoids that issue.

## 1. Bad-band measure and a strict one-insertion witness

Put \(N=n-1\), and let \(D_w=\{t\in\mathbb R:\|wt\|\le1/n\}\). It consists of disjoint closed intervals of length \(2/(nw)\), repeated with period \(1/w\). If \(J\) is an interval of length \(L\), then
\[
|D_w\cap J|\le \frac2nL+\frac2{nw}\left(1-\frac2n\right).
\tag{1}
\]
In fact on one period, an antiderivative of \(\mathbf1_{D_w}-2/n\) increases on the bad band by exactly \((2/(nw))(1-2/n)\) and decreases by the same amount on the complement. It is periodic and has this oscillation, yielding (1). This refines the slack term in [Zhang's Lemma 6.1](https://arxiv.org/html/2608.13599v3#S6.SS1).

For any deleted \(q\in[n-1]\) there is a time at which all speeds of \([n-1]\setminus\{q\}\) have distance at least \(1/N\). If \(2q>N\), use \(t=1/q\), since no remaining speed is a multiple of \(q\). Otherwise choose an integer \(D\in[n+q,2n-2]\) coprime to \(q\): there are at least \(q\) consecutive integers in this range, since \(n\ge2q+1\). For \(t=a/D\) with \(aq\equiv1\bmod D\), no retained speed has residue 0 or \(\pm1\) after multiplication by \(a\): a residue \(\pm1\) would force that speed to be \(q\) or \(D-q\ge n\). Thus all distances are at least \(2/D\ge1/N\). This is the rational witness of Zhang's Theorem 2.9, also consistent with [Davis's exact deletion formulas](https://itsdavis.com/solved-conjectures/results/zhang-deletion-values/). We do not claim a new deletion theorem.

Consequently the strict good set for \(B\) at threshold \(1/n\) contains an open interval of length \(2/(nN^2)\), by the \(N\)-Lipschitz bound on every distance function. It must be covered by \(D_u\cup D_v\). Applying (1) twice and using \(v>u\) proves
\[
u\le \frac{2(n-2)N^2}{n-4}.
\tag{2}
\]

We also need that \(B\cup\{u\}\) has **strictly** larger loneliness than \(1/n\). Use [Zhang's one-entry classification](https://arxiv.org/html/2608.13599v3#S1) as follows. For any fixed \(n,w\) with \(w\ge n\), at most one deleted speed \(q\) can give a one-entry modification of loneliness at most \(1/n\). The classified alternatives are the Goddyn–Wong type \(w=mq\) with no integer coprime to \(q\) in \([n-q,m(n-q)-1]\), or one of the two Wills cases \((n,q,w)=(5,2,7),(6,2,9)\). To justify using “at most” rather than just equality, the exclusion arguments in Zhang's Lemma 2.4 and Propositions 3.4–3.5 only need that the uncovered region is contained in \(D_w\), which already follows from \(\mathrm{LR}\le1/n\) by Lemma 2.2. The divisible cases are covered by Goddyn–Wong (Zhang's Theorem 1.1), which gives the lower bound \(1/n\) in every divisible case.

If two Goddyn–Wong cases existed for \(q_1<q_2\), write \(w=m_iq_i\). Then \(m_1>m_2\ge2\) and
\[
(m_1-1)(n-q_1)>(m_1-1)(q_2-q_1)
=q_1(m_1-1)(m_1-m_2)/m_2\ge q_1.
\]
The interval for \(q_1\) would contain a complete residue system, a contradiction. The Wills case \(w=7,n=5\) has no other eligible divisor except 1, which cannot satisfy the coprimality condition. For \(w=9,n=6\) the only other divisor to test is \(q=3\), and the interval \([3,8]\) contains 4. This proves uniqueness. Since \(B\cup\{u\}\) is contained in each of the two one-entry modifications made by removing \(r\) or \(s\) and inserting \(u\), at least one of those two supplies the strict witness.

Take a component of the strict good set for \(B\cup\{u\}\). In \([0,1]\) both its endpoints are of the form \((jn\pm1)/(nw)\) for speeds \(w\) of that set, since 0 and 1 are bad for all speeds. When the endpoint speeds differ, their product is at most \(Nu\), and the endpoint difference is a positive integer divided by \(n\) times that product. When the speeds agree, the difference is at least \(1/(nu)\). Thus the component has length at least \(1/(nNu)\). It must lie inside a single bad band for \(v\); its length is at most \(2/(nv)\). We obtain the useful bound
\[
v\le 2Nu\le\frac{4(n-2)N^3}{n-4}.
\tag{3}
\]

## 2. Improve the maximum to quadratic

Assume first \(n\ge32\) and \(r\le N/2\). By the Jacobsthal bound used in [Zhang, Corollary 2.10](https://arxiv.org/html/2608.13599v3#S2.SS3), we may choose the coprime denominator \(D\) between \(n+r\) and \(n+r+2\sqrt r\), inclusive. In this range \(D\le7n/4\). The same rational witness gives distance at least \(8/(7n)\) on the retained speeds, so there is a base-good interval of length \(2/(7nN)\). Using (1) on this longer interval gives \(u\le14(n-2)N/(n-4)\). Therefore \(v\le28(n-2)N^2/(n-4)\) by (3).

Now suppose \(n\ge32\) and \(r,s>N/2\). Let \(H=1/(nN^2)\). By (2),
\[
\tfrac1n+uH\le(3n-8)/(n(n-4))<1/6.
\tag{4}
\]

If \(u\) is not divisible by one of the deleted speeds \(q\in\{r,s\}\), there is a unit \(p\bmod q\) with \(\|up/q\|\ge1/6\). Indeed let \(d=q/\gcd(q,u)>1\). The reduction of units modulo \(q\) onto units modulo \(d\) is surjective by the Chinese remainder theorem, and multiplication by \(u/\gcd(q,u)\) permutes the latter units. A unit at normalized distance at least \(1/6\) modulo \(d\) is 1 for \(d=2\), \((d-1)/2\) for odd \(d\), \(d/2-1\) for \(4\mid d\), and \(d/2-2\) for \(d\equiv2\bmod4\), \(d\ge6\). Since \(q>N/2\), no retained speed is divisible by \(q\), so all have distance at least \(1/q\ge1/N\) at \(t=p/q\). The entire open interval of radius \(H\) remains base-good by Lipschitz continuity, and is good for \(u\) by (4). As \(v\) must cover it with one bad band, \(v\le N^2\).

Finally suppose both \(r,s\) divide \(u\), and put \(g=\gcd(r,s)\). At \(t=1/r\) the base is good throughout the open interval of radius \(\Delta=(n-r)/(nrN)\). Since \(u\ge rs/g\) and \(g\le s-r\),
\[
\Delta-\frac1{nu}
\ge\frac{s(n-r)-gN}{nrsN}
\ge\frac{r(N-s)+s}{nrsN}
\ge\frac1{nrN}\ge H .
\]
The open interval of shifts \(h\in(1/(nu),1/(nu)+H)\) from \(1/r\) thus stays base-good. As \(u/r\) is an integer and \(1/n<uh<1/n+uH<1-1/n\), it is good for \(u\) as well. This forces \(v\le2N^2\). For \(n\ge32\), the preceding bounds give \(v\le30N^2\). For the remaining \(5\le n<32\), (3) gives \(v/N^2\le4(n-2)N/(n-4)\le130\), which follows by evaluating the endpoints of the convex function \(4n+4+24/(n-4)\) on that interval. This proves the stated constant.

## 3. When speed 1 is deleted

Every retained speed is between 2 and \(N\), so \((1/(2n),1/n)\) is base-good. The same application of (1) with length \(1/(2n)\) now gives \(u\le8(n-2)/(n-4)\), less than \(n\) for \(n\ge11\). For \(5\le n\le10\), use this bound and \(v\le2Nu\) from (3). The [exact coverage verifier](verify-lonely-runner-two-entry.js) merges the bad intervals on \([0,1]\), comparing endpoint rationals by integer cross multiplication. It examines all 22,706 possibilities in this finite range; the only full cover has \(n=5,s=3,u=6,v=8\). The speeds are twice the consecutive set \([4]\), which attains \(1/5\) (for example at \(t=1/10\)); the cover verifies the matching upper bound.
