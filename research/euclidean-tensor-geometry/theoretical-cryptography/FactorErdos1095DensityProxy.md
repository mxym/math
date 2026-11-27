# Exact logarithmic density and adjacent dependence for the Erdős–Selfridge proxy

For \(k\ge2\), call \(n\ge k\) *admissible* if no prime \(p\le k\) divides \(\binom nk\). The first admissible \(n>k+1\) is the Erdős–Selfridge function \(g(k)\) in [Erdős Problem 1095](https://www.erdosproblems.com/1095). In this note \(k\) is held fixed when taking the natural density in \(n\). We study the true density \(D(k)\) of admissible \(n\) and the density \(D_2(k)\) of pairs \(n,n+1\) that are both admissible.

[Sorenson–Sorenson–Webster (2020), Theorems 5.2 and 6.1](https://msp.org/obs/2020/4-1/obs-v4-n1-p23-s.pdf) define the inverse-density proxy \(\widehat g(k)=1/D(k)\) and prove the bounds \(0.530684+o(1)\le \log\widehat g(k)/(k/\log k)\le1+o(1)\). We determine its exact leading constant, with an expansion to every fixed logarithmic order, and compute a local dependence statistic of the periodic admissible set. These results concern the density proxy, not the first admissible \(n>k+1\).

## 1. The asymptotic for the inverse density

For \(0<u\le1\) define the nonnegative weight
\[
w(u)=-\log(1-\{1/u\}), \qquad
C_j=\int_0^1 w(u)(-\log u)^j\,du\quad(j=0,1,\ldots).
\]
For every fixed nonnegative integer \(d\), as \(k\to\infty\),
\[
\boxed{\quad
\log\widehat g(k)=k\sum_{j=0}^{d}\frac{C_j}{(\log k)^{j+1}}
       +O_d\!\left(\frac{k}{(\log k)^{d+2}}\right).
\quad} \tag{1}
\]
In particular,
\[
C_0=\sum_{a=1}^{\infty}\frac{\log(1+1/a)}{a+1}
    =\sum_{a=2}^{\infty}\frac{\log a}{a(a+1)}
    =0.7885305659\ldots. \tag{2}
\]

### Local digit product

For \(p\le k\) prime let \(e=e_p=1+\lfloor\log_p k\rfloor\) and write \(k=\sum_{i=0}^{e-1}a_{i,p}p^i\), \(0\le a_{i,p}<p\). Lucas's theorem, or equivalently the no-carry condition from Kummer's theorem, gives \(p\nmid\binom nk\) precisely when every one of the first \(e\) base-\(p\) digits of \(n\) is at least its corresponding \(a_{i,p}\). Thus the admissibility indicator is periodic with period \(\prod_{p\le k}p^{e_p}\); the Chinese remainder theorem gives the known formula
\[
D(k)=\prod_{p\le k}\prod_{i=0}^{e_p-1}\left(1-\frac{a_{i,p}}p\right).
\]
The contribution of all digits for \(p\le\sqrt{k}\) to \(-\log D(k)\) is \(O(\sqrt k)\), since each factor contributes at most \(\log p\), and \(e_p\log p\le2\log k\). For \(\sqrt{k}<p\le k\) there are two digits. The higher digits contribute \(O(\sqrt k)\) in total: for \(\sqrt{k}<p\le2\sqrt{k}\) use the pointwise bound \(\log p\) and the prime-counting upper bound; for \(p>2\sqrt k\) use \(a_{1,p}/p\le k/p^2<1/4\) and sum \(2k/p^2\). Therefore, after extending the low-digit sum down to \(p=2\) at additional cost \(O(\sqrt k)\),
\[
\log\widehat g(k)=\sum_{p\le k}w(p/k)+O(\sqrt k). \tag{3}
\]

### From the prime sum to an integral

Put \(L=\log k\). We use the classical [de la Vallée Poussin prime number theorem with error term](https://books.google.com/books?id=_O0GAAAAYAAJ),
\(\pi(t)=\operatorname{li}(t)+O(t e^{-c\sqrt{\log t}})\) for an absolute \(c>0\). Let \(A=\lfloor e^{\eta\sqrt L}\rfloor\), with \(0<\eta<c/(4\sqrt2)\), and \(x_0=k/(A+1)\). Terms with \(p\le x_0\) total \(O(k/A)\), because \(w(p/k)\le\log p\le L\) at prime arguments and \(\pi(x_0)\ll x_0/L\).

On \((x_a,y_a]=(k/(a+1),k/a]\), \(1\le a\le A\), the weight on the prime-sum scale is
\[
f_a(t)=w(t/k)=\log\frac{t}{(a+1)t-k}.
\]
This decreases to zero at \(y_a\) and has a logarithmic singularity just to the right of \(x_a\). Remove the first unit \((x_a,x_a+1]\), which contains at most one integer and contributes \(O(L)\) to the prime sum. Its corresponding contribution to the integral against \(dt/\log t\) is \(O(1)\), using \(f_a(x_a+s)\le L+|\log s|\) for \(0<s\le1\) and \(\log t\asymp L\). All retained intervals have length greater than one for large \(k\). On the remainder \(f_a\) is nonnegative and decreasing with supremum and total variation \(O(L)\). Partial summation thus replaces the prime sum there by \(\int f_a(t)\,dt/\log t\) with error \(O(kL e^{-(c/\sqrt2)\sqrt L})\), uniformly for \(a\le A\), since \(x_a\ge x_0\ge\sqrt{k}\) for large \(k\). Summing the errors over \(A\) blocks and including the cutoffs gives, for some absolute \(c_1>0\),
\[
\log\widehat g(k)
=k\int_{1/(A+1)}^1\frac{w(u)}{L+\log u}\,du
   +O(k e^{-c_1\sqrt L}). \tag{4}
\]
The weight was kept intact throughout partial summation; in particular there is no need to balance separate approximations for two prime sums of order \(k\).

On a normalized block \((1/(a+1),1/a]\), elementary integration gives
\[
\int_{1/(a+1)}^{1/a}\log\frac{u}{(a+1)u-1}\,du
=\frac{\log(1+1/a)}{a+1}.
\]
Hence the block contribution to \(C_j\) is at most \(O_j((\log(a+1))^j/a^2)\), all \(C_j\) are finite, and their tails over \(a>A\) are \(O_j((\log(A+1))^j/A)\). For \(v=-\log u\) in the retained range, \(v\le\log(A+1)\le L/2\). Expand
\[
\frac1{L-v}=\sum_{j=0}^{d}\frac{v^j}{L^{j+1}}
      +O\!\left(\frac{v^{d+1}}{L^{d+2}}\right).
\]
Using the finiteness of \(C_{d+1}\) and the tail bounds in (4) proves (1). Summing the block integrals gives the first series in (2); shifting its positive and negative logarithms in the partial sums gives the second. The stated numerical prefix is enclosed by exact rational bounds in the companion check.

## 2. Adjacent admissible values are not independent

Write \(t_p=v_p(k)\) and \(a_{t_p,p}\) for the first nonzero base-\(p\) digit of \(k\). There is the exact identity
\[
\boxed{\qquad
\frac{D_2(k)}{D(k)}
=\prod_{p\le k}\left(1-
 \frac{1}{p^{t_p}(p-a_{t_p,p})}\right).
\qquad} \tag{5}
\]
It follows that \(D_2(k)=0\) if and only if \(k+1\) is composite. On the infinite subsequence where \(k+1\) is prime, the conditional density has the bounds
\[
e^{-O((\log k)^2)}\le\frac{D_2(k)}{D(k)}\le1. \tag{6}
\]
In particular, \(-\log D_2(k)\sim C_0 k/\log k\) on that subsequence, not \(2C_0 k/\log k\). Equivalently, the ratio of the actual adjacent joint density to the independent prediction \(D(k)^2\) is \(\exp((C_0+o(1))k/\log k)\) along those \(k\), while it is exactly zero for \(k+1\) composite.

To prove (5), fix \(p\), choose a uniform allowed residue modulo \(p^{e_p}\), and add one. Its first \(t_p\) digits are unrestricted by admissibility because the corresponding digits of \(k\) vanish. Unless they are all \(p-1\), addition stops below the first restricted digit and cannot spoil admissibility. If they are all \(p-1\), an event of probability \(p^{-t_p}\), addition reaches the digit at \(t_p\). That digit has \(p-a_{t_p,p}\) allowed values. It spoils admissibility only if it equals \(p-1\), in which case it rolls over to zero, below the positive \(a_{t_p,p}\); otherwise addition stops and all digits remain allowed. This argument includes \(t_p=0\) and wraparound of the residue. The local conditional success probability is the displayed factor; multiplication is exact by the Chinese remainder theorem.

A factor vanishes exactly when \(t_p=0\) and \(a_{0,p}=p-1\), that is, \(p\mid k+1\). The existence of a prime divisor \(\le k\) of \(k+1\) is equivalent to compositeness. If \(k+1\) is prime, put \(r_p=p-a_{0,p}\in[2,p]\), and note \(p\mid k+r_p\). The subtracted term in (5) is at most \(1/r_p\): this is equality for \(t_p=0\), and for \(t_p\ge1\) it follows from \(r_p=p\). Thus, with \(\omega(m)\) the number of distinct prime divisors of \(m\),
\[
-\log(D_2(k)/D(k))
 \le 2\sum_{p\le k}\frac{1}{r_p}
 \le 2\sum_{r=2}^{k}\frac{\omega(k+r)}r
 = O((\log k)^2).
\]
The last step uses just \(\omega(k+r)\le\log(2k)/\log 2\). Formula (6) and then (1) finish the proof.

## Scope

The exact one-point density is the previously introduced proxy; (1) sharpens the range in the published Theorem 6.1. The adjacent statistic (5) identifies a strong local dependence in the actual periodic residue sets. This does not estimate the location of the first residue beyond \(k+1\), and does not by itself refute a conjectured scale for \(g(k)\) inferred heuristically from \(\widehat g(k)\). No bound for \(g(k)\) is claimed here.

[verify_factor_erdos1095_density_proxy.js](verify_factor_erdos1095_density_proxy.js) uses exact integer arithmetic to check local and full-period digit counts and enclose \(C_0\) by rational inequalities. It does not infer an asymptotic from finite trials.
