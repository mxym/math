# An unrough weighted Möbius covariance criterion using the actual Chen lower

Let \(N\) be an individual large even integer, \(L=\log N\),
\(J\Subset(1/3,2/3)\) a fixed interval of positive length,
\(x\in NJ\), \(y=N-x\), and \(M=|J|N\mathfrak S(N)\).
All pairings below keep the true target units \((x,N)=1\).
Write \(\Pi(n)=(\log n)1_{n\ {\rm prime}}\) and
\(R_J=\langle\Pi,\Pi\rangle\). Define the literal weights
\[
 \begin{split}
 W(n)&=(\log n)\mu^2(n)
          \prod_{p\mid n}\left(\frac{\log p}{\log n}\right)^3,\\
 V(n)&=(\log n)\mu(n)
          \prod_{p\mid n}\left(\frac{\log p}{\log n}\right)^3,\qquad
 K(n)=V(n)+\Pi(n).
 \end{split}
\]
Thus \(V=-\Pi\) on a genuine prime, whereas \(K=0\) there and
\(|K|=W\) on squarefree composites. There is no roughness
cutoff, artificial primality approximation, or parity model.

**Theorem.** Put \(s=(.204\cdot .796)^3\). Uniformly through the
even targets, the true lower comparison is
\[
 R_J\ \ge\ \frac{\langle V,V\rangle+.005\,M}{1+2s}+o_J(M).
                                                               \tag{1}
\]
In particular the **unproved** fixed-target bound
\(\langle V,V\rangle>-.0049M\) would suffice for a positive binary
prime count at every sufficiently large even target. The arithmetic
argument below only gives (1); it does not prove that signed
covariance bound. The score is distinct from the compensated sextic
and its \(.954\) comparison. The two certified lower comparisons,
being for the same \(R_J\), can be used via their maximum or a
convex combination, not by adding two copies of \(R_J\).

## 1. Literal prime and semiprime terms

The [actual .204 Chen lower](../moved_affine_cutoff/Proof.md#1-stop-the-actual-forced-prime-packing-earlier)
gives
\[
                 R_J+D_2(.204)>.755M,                            \tag{2}
\]
where \(D_2(.204)\) is the true prime--semiprime sum with
each semiprime factor \(>(N/2)^{.204}\), and both logs present.
We use (2) for \(J\) and its reflection. The source note states
it on the high half of the central interval, but its proof of (2)
works on either half or any fixed central interval, as follows.
In the linked original sieve §§1–2 the input to every
arithmetic residue sum is a genuine prime prefix or difference of
prefixes for the actual reflected interval \(N-NJ\). The packing
inequalities and the notional residue bound use \(N=2X\), not the
ordering of the two coordinates; source products in all such
prefix differences lie between \(2X/3\) and \(4X/3\). The genuine
endpoint partitions therefore have the same fixed-aspect parameters
and the principal is the prime log mass in that interval, asymptotic
to \(|J|N\). The true least-prime cut, the support of its sieves,
and the \(p_1^2\) prefix test all use \(X\), so none changes on
reflection. The rank cap \(5(.204)>1\) and the square removal use
only the true upper bound \(4X/3\). The two subtracted positive angular
caps in the .204 proof already allow any fixed subinterval of
\([N/3,2N/3]\). Finally all logs have the same \(1+O_J(L^{-1})\)
relative changes. This verifies (2) with exactly the same constant
on \(1-J\) as well. No shrinking spatial interval is used.

Write \(u_i=\log p_i/\log n\) for the literal own-log angles.
On a genuine squarefree semiprime in (2) the weight in \(K/\log n\)
is \([u(1-u)]^3\ge s-O_J(1/L)\), since its smaller angle is at
least \(.204-O_J(1/L)\). Even composite ranks have nonnegative
\(K\); only the odd ranks at least three require subtraction.

For rank \(j\), the ordinary angular mass of \(W\) normalized by
the spatial length is
\[
 I_j=\frac1{j!}\int_{\sum u_i=1,\ u_i>0}\prod_i u_i^2\,
                      du_1\cdots du_{j-1}
      =\frac{2^j}{j!(3j-1)!}.
\]
The \(1/j!\) uses unordered true primes, and the \(1/u_i\)
densities come from reciprocal prime harmonics and PNT on the
largest factor, including the outer \(\log n\).
The [actual \(3.446\) product-prime upper](../angular_prime_first_composite/Proof.md)
on each compact angular rank bounds the odd debit by
\(3.446\sum_{j\ge3,\ j\ {\rm odd}}I_j M+o(M)<.000114M+o(M)\).
The extension to all ranks and least factors is justified in §3,
not by a postulated uniform rank dependence of the \(3.446\) proof.
It follows for both orientations that
\[
       \langle\Pi,K\rangle,\ \langle K,\Pi\rangle
             \ \ge\ (.755s-.000114)M-sR_J+o_J(M).                 \tag{3}
\]
This uses (2) only once in each orientation. In particular the
prime subtraction in \(V\) is the physical prime atom.

## 2. True upper for the opposite weighted composite

Put \(\theta=.499\) and \(a=\theta/3\).
For any nonnegative compact, fixed-rank angular product source
\(Z\) at positive least-factor floor, put
\(M_Z=\mathfrak S(N)\sum_{x\in NJ,(x,N)=1}Z(x)\).
The following upper is for the **actual** receiver \(|K|\):
\[
 \langle Z,|K|\rangle\le U M_Z+o(M),\qquad
       U=\int_0^a u(1-u)^3\,du+\frac2{\theta}\,4^{-3}<.072406.    \tag{4}
\]
The same estimate holds with the spatial interval reflected
and the weights reversed.

In fact first fix a positive receiver least-factor floor.
On a true composite squarefree \(n\) having least prime of
own angle \(u\), the other factors have total angle \(1-u\).
Their product of angles is at most their sum and hence at most
\(1-u\); thus \(W(n)/\log n\le [u(1-u)]^3\).
On the portion \(u\le a\), open the **one actual least prime** \(p\)
and upper-sift the quotient \(n/p\) to just below that prime,
with quotient level \(N^{2u+o(1)}\). On each fixed exponent bin
use lower endpoints for the sifting and level, with fixed
arbitrarily small margins before refinement. The full modulus is
the literal \(p d\), of exponent at most \(3a+o(1)<1/2\);
the upper sieve parameter tends to 2. This gives conditional
density at most
\((1+o(1))\mathfrak S(N)/(p u L)\), by
\(e^{-\gamma_E}F(2)=1\). Multiply by \(L[u(1-u)]^3\) and the
prime reciprocal harmonic \(du/u\), giving the first integral
in (4). No upper at an unresolved semiprime endpoint is needed.

On \(u>a\) one has \(W(n)/\log n\le4^{-3}\):
for two factors this is AM–GM, and for \(j\ge3\) use
\(\prod_i u_i\le j^{-j}\le1/4\).
Forget the composite restriction for this positive upper
and sift the full receiver to exponent \(a\) at level \(\theta\),
with ratio 3 and coefficient \(2/\theta\) in units \(1/L\).
This gives the second term in (4). The exact \(sF(s)=2e^{\gamma_E}\)
is used only at the two allowed ratios.

Both steps use standard ordinary below-square-root product
Bombieri–Vinogradov on the **genuine** source \(Z\), exactly as
in the [actual receivers of the quartic ledger](../halfzero_detector/CompensatedDebit.md#1-uniform-positive-receivers-for-the-three-exact-rough-ranks).
At fixed angle floor and rank choose a true prime slot and
group the others as a divisor-bounded independent coefficient;
prefixes, smooth spatial weights, and the fixed bins are handled by
that product comparison. Divisor multiplicity at the joined \(pd\)
is harmless with the arbitrary-log reserve. The reduced model is
on the actual source mask \(Nx\). Its other-prime roots are
\(1/(r-1)\) off \(Nx\) and absent on \(Nx\); at the marked
prime \(p\) the outside factor is \(1/\varphi(p)\), with the
dividing-\(Nx\) alternatives absent. They cost a power in the
positive reciprocal harmonic at a fixed polynomial floor.
In particular \(p\) itself is excluded from the quotient sieve,
and \(\mathfrak S(Nx)=(1+o(1))\mathfrak S(N)\) on every fixed
compact source rank. All local factors and errors are at the
same physical target, not at a model prime opponent.
Bins of zero-width boundary may be approached through fixed
collars before the limits; the displayed integrals then follow.

## 3. Uniform actual tails and final comparison

Here it suffices to extend the compact inputs to the particular
weighted scores \(W,|K|\) and genuine \(\Pi\), not to arbitrary
unbounded weights. For fixed \(D>1\) the squarefree positive
multiplicative factor
\[
       D^{\omega(n)}\prod_{p\mid n}(\log p/L)^3
\]
has bounded prime reciprocal harmonic uniformly in \(N\),
since \(\sum_{p\le N}(\log p/L)^3/p\ll1\).
Its prime-power values may be set to zero for the original
squarefree weight. Replacing target logs by own logs costs
only a bounded factor even over all ranks: \(\omega(n)\ll L\)
and \(\log n=L+O_J(1)\).
Apply the positive two-affine upper of the
[half-zero proof, §2](../halfzero_detector/Proof.md), i.e. the
corrected Henriot estimate on \(x,N-x\), with this multiplicative
function on each weighted composite arm. If the other arm is
a true prime, dominate its prime indicator by a genuine
small fixed-power rough indicator; its Euler product contributes
\(O(1/L)\) in place of the other composite weight.
With the two logs restored, the total is \(O_{D,J}(M)\).
This gives \(O_{D,J}(D^{-k}M)\) above fixed rank \(k\).

For an actual small prime \(p\le N^\eta\) in a weighted arm,
extract its factor \(D(\log p/L)^3\) once and reset all further
powers of that prime to weight 1 on that quotient.
The true affine progression is the one coming from
\(x=p m\), \(y=N-pm\), or its reflection, of length
\(\asymp_J N/p\). It has the same local factor up to the
bounded one-leading-prime correction; \(p\mid N\) is absent
on the actual unit support. Its positive upper with both
logs is \(O_{D,J}(M/p)\) before the extracted factor.
The total marked reciprocal sum is \(O_D(\eta^3+L^{-3})\),
by the ordinary prime log harmonic and partial summation.
The analogous single-integer argument proves the ordinary
tail bound. This justifies taking \(N\to\infty\) at a fixed
floor and rank first, followed by \(\eta\downarrow0,k\to\infty\)
in (3) and in the application of (4) to \(Z=|K|\).
In particular it does not require a uniform error in the
large-rank input theorems before the order of limits is taken.

Now the [exact rational certificate](check.py) gives
\[
 \sum_{j\ge2}I_j<.01670,\qquad U<.072406,\qquad
       \langle|K|,|K|\rangle<.001210M+o(M).
\]
Finally use the **literal** signed expansion
\[
 \langle V,V\rangle
   =R_J-\langle\Pi,K\rangle-\langle K,\Pi\rangle+\langle K,K\rangle
   \le (1+2s)R_J
           -\bigl(2(.755s-.000114)-.001210\bigr)M+o(M).
\]
The displayed coefficient exceeds \(.005\), giving (1).

There is no dyadic numerical obstruction to the proposed new
lower. In fact the ordinary signed angular mean of \(V\) is
\(\sum_{j\ge1}(-1)^j I_j=-.98336\ldots\); independent ordinary
PNT on the genuine prime-product slots after summing the targets
gives its squared value as the dyadic normalized mean of
\(\langle V,V\rangle\). This is only a feasibility check,
not a fixed-target evaluation. In particular the analytically
missing statistic is precisely the two-argument weighted Möbius
correlation in (1).
