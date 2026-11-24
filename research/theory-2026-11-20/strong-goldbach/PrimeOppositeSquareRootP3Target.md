# Square-root P3: a trimmed prime-marked moment, exact budget, and a residue check

**Status:** the sufficiency implication and endpoint costs below are unconditional; the required middle-moment bound is **open here**. This is not a P3 theorem. The objective is literal fixed N and literal fixed root window, not an averaged even target or a different source length.

## Setup and precise target

Fix 0<a<b. Let N be even, H=sqrt(N), L=log N, I=(aH,bH], and X=Li(bH)-Li(aH). Let S_N=2 prod_{l>2}(1−1/(l−1)^2) prod_{l>2,l|N}(l−1)/(l−2) and B=2X S_N/L. In the notation of [the square-root P4 proof](PrimeOppositeSquareRootP4.md), use

    d0=.249, mu=.07, beta=.4, eta=4−1/beta=3/2,
    z=N^mu, alpha=.11, gamma=.37.

For a prime q, use t=log q/L and C(q) as the count of actual primes p in I, p not dividing N, such that q|(N−p) and P^−(N−p)>=z. If q>=z then C(q) is exactly the corresponding count of integers j with p=N−qj in I prime, p not dividing N, and P^−(j)>=z. Here q|N makes the count zero because q< N^.4 while p~H. Define the middle mark moment

    M_N = sum_{q prime, N^.11<=q<N^.37} (1−t/.4) C(q).

**Target estimate M_N <= (2.95+o(1))B, for all sufficiently large even N.** That one estimate implies at least a positive constant times B genuine primes p in the literal window with squarefree N−p, P^−(N−p)>=N^.07, and Omega(N−p)<=3.

This is easier to state and allows more slack than the previous P2 target: the marked q never enters the q~H or q>H degenerate range, the cofactor interval length is always H/q >= N^.13 times the window constant, both ends of the mark range are discharged independently, and 2.95 exceeds the upper Buchstab reference coefficient 2.293 by about 29%. The reference is not asserted to be an upper bound for actual N.

## 1. Endpoint costs and sufficiency

Take the signed Richert weight

    w(m)=1−eta^(-1) sum_{z<=q<N^.4, q|m} (1−log q/(.4 L))

on genuine z-rough m=N−p. On squarefree m, the mark sum is at least Omega(m)−log m/(.4L); thus w<=0 for Omega>=4, and w<=1 always. The same integer square-divisor removal as in the P4 paper costs O(H/z+N^(1/3))=o(B), even for the signed weight because the fixed rough cutoff bounds |w|. It therefore suffices to have a positive signed weighted count.

For the base rough count, BV at source length H gives all moduli <=N^.249, as before, and the linear-sieve s=.249/.07 lies in (2,4). Thus in units B the lower coefficient is exactly

    A = log((.249/.07)−1)/.249 = 3.7706448... > 3.77.

For t in [.07,.11), condition on the true prime divisor q. With residual level N^.249/q and reduced sifting cutoff min(z,(N^.249/q)^(.5)), the upper linear-sieve parameter is s'=max(2,(.249−t)/.07) in [2,2.558…). Accordingly the upper marked coefficient in units B is exactly bounded by

    L0 = integral_.07^.11 (1−t/.4)/(t(.249−t)) dt <2.20.

Weighted BV errors sum as before: each qd<=N^.249 has at most one prime factor q>=z because all primes of d are <z, and fixed divisor weights are absorbed with Cauchy–Schwarz. Uniform main term errors from the linear sieve are o(B) after the weighted 1/q sum. Shrinking the cutoff near the cap t=.11 is necessary to avoid invoking an upper sieve outside its assured range, and costs no extra normalized factor because sF(s)/(2e^gamma_E)=1 for 2<=s<=3.

For t in [.37,.40), switch to the literal affine j interval [(N−bH)/q,(N−aH)/q). Select K=N^((.5−t)/2−.001)<z. Every actual survivor avoids j=0 and N−qj=0 modulo all primes l<=K. These are two distinct roots except when l|N, when they coincide; q>K. Thus this is the full two-form Selberg denominator G_0(K) of [the P4 proof](PrimeOppositeSquareRootP4.md), with G_0(K)=(log K)^2/(2S_N)+o(L²/S_N) uniformly on this strip. In particular we don't need an asymmetric-loss formula here. The Selberg error O(K² L^C) per fixed q sums to O(H N^(-.002) L^C) since K²=HN^(-.002)/q. From X=(2+o(1))(b−a)H/L the normalized bound for C(q), in units B/q, is

    (1+o(1)) 2/(.498−t)^2

apart from those summable absolute errors. So the contribution of this upper strip has coefficient

    H0 = integral_.37^.4 2(1−t/.4)/(t(.498−t)^2) dt <.43.

If M_N has coefficient <=2.95 then the total three-part cost is <= (5.58+o(1)) B, whereas eta A >5.655. Thus the signed weighted sum on actual squarefree numbers is >(.05+o(1))B, after division by eta. It follows that the same unweighted positive count has Omega<=3. Existing narrow-angle exclusions can additionally be deducted from that unweighted family if desired; angles are not part of this sufficiency proof.

## 2. Rational arithmetic and reference model

For L0, partial fractions give (1/d0)log(.11/.07)+(1/d0−1/beta) log((d0−.07)/(d0−.11)); both log coefficients are positive. To upper-bound H0 on every subdivision [a1,b1], evaluate the positive decreasing factor (1−t/beta)/t at a1 and the increasing factor 2/(.498−t)^2 at b1. 1000 equal subdivisions rounded upward individually to 10^−9 give the rational upper 21491957/50000000 = .42983914. The log enclosure uses u=(x−1)/(x+1) and y=2 sum_{k=0}^{11} u^(2k+1)/(2k+1), giving y<=log x<=y+2u^25/(25(1−u²)) for x>1. This gives A>3.77, L0<2.20, H0<.43 without floating checks. BigInt rational replay returned upper L0 ≈2.1986319506.

The heuristic cofactor model has coefficient

    (1/(2*.07)) integral_.11^.37 omega((1−t)/.07) (1−t/.4) dt/t.

It assumes the expected local prime-root density and Buchstab rough cofactor distribution on the true switched arithmetic intervals and is not an asymptotic established here. The generic rigorous inequality omega(u)<=.57 for u>=2 yields reference upper <2.293: on [2,3] the formula (1+log(u−1))/u is at most .57 (minimize .57u−1−log(u−1), using .57+log(.57)>0), and the delayed integral recurrence propagates this bound. Evaluating the elementary upper integral gives (.57/.14)[log(37/11)−.65]<2.293 by the log enclosure above.


## 3. A precise obstruction to merely rerunning the P4 cap

In the middle strip, the old hybrid only supplies the minimum of the two normalized cap functions

    U_BV(t) = 1/(.249−t) on t<.249, and +infinity otherwise,
    U_aff(t) = 1/(4 mu² J(v)),  v=(.249−t/2)/mu.

For v>1 use the asymmetric Selberg lower denominator J(v) from the P4 proof, which is <=v²/2; for v<=1 use the full denominator and J=v²/2. (Using log support (.5−t)/2 rather than (.5−t)/2−.001 in the asymptotic limit would not change the following argument materially.) On t∈[.20,.30], U_BV>=1/.049 wherever it exists, while U_aff>=2/(.498−t)^2>=2/.298²>1/.049. Hence the integral of the best pointwise cap in this single substrip is greater than

    (log(3/2)−1/4)/.049 > 3.17 > 2.95.

This is a limit of the two available cap formulas at the stated parameters, not a lower bound for actual middle mass or an impossibility theorem for other weight optimizations. Already this stable subinterval, not q~H, is the analytic obstacle.

For the small-factors-only pointwise reduction, an Omega=4 vector with all factor coordinates >d0 can be balanced and invisible to every nontrivial divisor d<=D; deleting a tiny tie neighborhood would remove this balanced example, but not the full positive W4 mass. An honest separated feasible exponent configuration (.09,.19,.28,.44), with no nearly coincident factors and no two near sqrt N, still has P4 Richert weight 1−(3−.56/.3)/(5−1/.3)=.32>0. This demonstrates why the existing structural removals cannot upgrade the P4 proof merely by pointwise inspection. It is not a claimed realization by a true p.

## 4. Genuine residue N~H² versus available prime distribution

The marked AP residue is always p=N mod qd. Source variable in any prime AP theorem is x~H, so N~x². Taking the least residue separately modulo each qd does not fit a theorem for one fixed small integer a across the weighted modulus sum.

* Lichtman arXiv:2309.08522 Theorem 1.7 (1.6)/(1.7) explicitly assumes |a|<x^epsilon or |a|<x^(1+epsilon) in the two ranges. The latter remains incompatible with N~x². Lemma 4.6 identifies the use of this size even before the spectral stages; a reciprocal rewrite contains e(ah/(qr1r2 n1)), replaced there at cost proportional to a/x up to logs under its stated regime. This is not a missing notational convention. The result also requires triply well-factorable weights, not implied by an arbitrary marked q and leftover sieve coefficient. [Primary source](https://arxiv.org/pdf/2309.08522).
* Maynard, Primes in arithmetic progressions to large moduli III, Theorem 1.2, is genuinely legal in the shifting residue: for each q1,q2 choose b=N mod q1q2, independent of q3, and then for each coprime product choose a=N mod q1q2q3. However Q1Q2Q3=x^(.5+delta), with delta<.001, Q2<x^.05 and Q2Q3>x^(.1+12delta), so Q1<x^(.4−11delta); Q3<x^.1. A prime q almost as large as N^.20 cannot be in any of those factors (for any fixed delta>0), let alone q in large parts of [.20,.37]. In addition to modulus shape, even the total level only reaches N^(.25+.0005), up to constants depending on a,b, not N^.37. Theorem 1.1 does have a full supremum but has the displayed weak O(delta*pi(x)+x(log log x)^2/log²x) error and a two-factor restriction, not a source of the o(B) remainders required here. Theorem 1.3 is a minorant in p, whereas the mark costs need an upper, and its moduli also require two factors. [Primary source](https://arxiv.org/pdf/2006.08250).
* Runbo Li arXiv:2602.20917v6, Theorems 2.1 and 2.2, develops upper/lower prime coefficients for some larger moduli. The setup leading to the general-moduli coefficients (p. 1, immediately after (2), and §2) fixes a nonzero integer a and does not supply uniformity for a~x²; in particular the constituent discussion below Lemmas 2.3–2.4 explicitly invokes fixed a. Theorems stated for almost-all q are not automatically valid on the prime subset (unless separately proved at sufficient uniformity), and even a marginal upper bound for pi(I;q,N mod q) does not keep the 1/log N factor from the actual rough cofactor; to use it one needs control of the sifted joint mark or a coefficient estimate for the relevant qd shapes. Some three-factor subcases import Maynard's genuine residue uniformity but inherit its factor/level domain, as in Theorem 5.4(3); we make no blanket statement about all separate inputs. [Primary source](https://arxiv.org/pdf/2602.20917).

Thus a precise subsequent objective is the tested M_N inequality, or any valid near-model average for a sufficient part of the true q,j middle range to pay 2.95B. No substitution of a moving N into a theorem for a fixed residue, no result for averaged N, and no rank-3 lower bound asserted.
