# Fifth high even exponent unless 5 occurs exactly squared

**Yongxian Zhang.** AI-assisted proof development and internal verification; no external peer review or priority claim.

**Theorem.** If an odd perfect number \(N\) is coprime to \(3\) and \(v_5(N)\ne 2\), then at least five distinct non-Euler primes have exponent at least \(4\). Equivalently, if an odd perfect number coprime to \(3\) has just four higher even exponents, then \(5^2\parallel N\). This does not settle the case \(5^2\parallel N\) or the existence of odd perfect numbers.

Use the same proof as [the four-exponent result](OddPerfectFourNotableCoprimeThree.md), with the changes given here and verified by the [exact companion checker](verify_odd_perfect_five_notable_no_ordinary_five.py). In the contradiction hypothesis there are now at most four notable primes, so the total distinguished list is padded to five. Its \(t\) residue-one primes contain the support of every ordinary divisor sum. The ordinary primes are \(5\bmod6\) and cannot equal 5 under the theorem's premise. The special prime is \(1\bmod12\), so 5 is still allowed in the distinguished list as a notable prime, and the checker allows it. Thus the cases \(5\nmid N\) and \(v_5(N)\ge4\) are both covered without breaking the upper bound.

Choose cutoffs \(X=1000\), \(Y=10000\), \(Z=30000\). Trial division gives 85 ordinary candidates in the first range, 530 in the second, and 1017 in the third, each with support size at most five. The same pruned support closure gives 172,928 unions \(U\) in the first range. For each possible \(t\) and \(U\), use the same disjoint distinguished-slot upper bound \(B\). Use the first five eligible Euler surrogates outside \(U\) if the Euler prime is outside it: at most four can coincide with other distinguished primes. For sorting the \(5-t\) residue-two gains, the first \(|A|+4\) primes suffice, where \(A\) is the set of ordinary first-range candidates with support contained in \(U\).

For the logarithm beyond each cutoff, use the componentwise minima \((7,13,19,31,37)\) as needed. Sum exponent degrees up to 22 using the exact upward rounding as in the four-exponent result. For degree \(k\ge23\) use \(2\binom{k+t-1}{t-1}(2/5)^k\); successive terms have ratio at most \(1/2\). The verifier computes upper bounds by this integer arithmetic. Convenient rational budgets used in the filters are:
\[
\begin{array}{c|ccccc}
 &t=1&t=2&t=3&t=4&t=5\\
X& .008&.033&.086&.173&.305\\
Y& .001&.006&.017&.039&.076\\
Z& .001&.006&.017&.018&.037
\end{array}
\]
For the \(X\)-filter, compare \(B\) with \(2(1-L_X)\). Exactly \(8,1497,12075\) cases survive for \(t=3,4,5\), respectively. For the \(Y\)-filter, add to \(L_Y\) the grouped bound for the range \(X<s\le Y\) \(D\) obtained by grouping each ordinary candidate on its least support prime outside \(U\), using the empty group plus the \(t-|U|\) largest nonempty groups; continue only if \(B\ge 2(1-D-L_Y)\). Just six rows remain, all \(t=4\) with Euler prime represented by \(13\) (fixed or surrogate). Finally apply the same grouping separately to \(Y<s\le Z\) and call its log-contribution bound \(E\). Adding bounds over two bands rather than identifying the same target groups in both only enlarges the bound. The checker verifies
\[
 B/(1-D-E-L_Z)<1993/1000<2
\]
in all six rows. This excludes the assumed at-most-four notable primes under the stated condition.
