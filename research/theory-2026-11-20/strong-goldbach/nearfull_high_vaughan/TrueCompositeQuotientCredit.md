# A matched negative quotient reserve in the original giant score

Use the original genuine two-prime score and strict \(Q_y(m)\)
of [TinyMOriginalGiant.md](TinyMOriginalGiant.md). Thus
\(y=N-x\), \(S=\exp((\log\log N)^4)\), \(B=N/S\),
\(T_y=y/B\), and
\[
       Q_y(m)=\sum_{\substack{d\mid m\\d<T_y}}\mu(d).
\]
Fix a nondegenerate compact central interval \(J\), \(C_0>1\),
and \(B_0>0\). All conclusions concern individual even
\(N\) with \(\operatorname{rad}(N)\le(\log N)^{B_0}\),
and the **original** \(r\)-interval
\(I=[N/S^{C_0},N/S]\). Set \(L=\log N,\ \ell=\log L\).

**Theorem.** There are a fixed even integer \(K\ge2\), a fixed
\(\delta>0\) with \(1+2\delta<C_0\), and fixed disjoint actual
prime-factor bands described below such that the following
holds. In the same literal quotient annulus
\[
                         S^{1+\delta}\le m\le S^{1+2\delta},   \tag{1}
\]
take the union of the genuine prime \(m\)'s and those genuine
squarefree rank-\(K\) quotients with one real prime from each
selected band. The original signed score on this union is
\[
                         \le -c\,N\mathfrak S(N)               \tag{2}
\]
for a fixed \(c>0\) at all sufficiently large such targets.
Both populations avoid every original tiny bank of
[TinyTagProjection.md](TinyTagProjection.md) with
\(\theta_+<2\). The prime-\(m\) population has positive sign;
the selected genuine composites have negative sign.
The remaining composites in (1) are **not** evaluated, so
(2) is not a bound for the whole annulus or the whole
giant score. No binary positivity follows.

## 1. A variant of the tiny operator at geometric logarithmic scales

For finitely many actual prime colors replace the scale windows
of TinyTagProjection by
\[
 [S^{v_\nu^-},S^{v_\nu^+}],\quad
 0<v_\nu^-<v_\nu^+\le C_2,\qquad
                  10\sum_{\nu<s}v_\nu^+<v_s^-\quad(s>1),      \tag{3}
\]
where these are fixed constants and \(C_2\) is fixed.
Allow each reciprocal color mass \(V_\nu\) to be bounded above
and below by fixed positive constants, not necessarily \(1/4,1/2\).
Require source slots rough beyond \(5Y\) on any retained
tag shell; here we use \(Z=\exp(L^{.24})\), larger than every
\(Y\) and all the alphabet primes.
The projected comparison, with the **same full target** major,
has the same error \(O_R(NY L^{-R})\) for fixed sufficiently large
\(K\) after \(R\). The dependence of the implicit constants
and eventual threshold on the fixed band data is harmless.

Here are the changes in the cited audit. A nonempty tag shell
has \(c_2\ell^4\le\log Y\le C_3\ell^4\) for fixed positive
\(c_2,C_3\); \(\log p_0\gg\ell^4\). Keep both auxiliary
depths \(m_0=1+\lfloor L^{.01}\rfloor\), \(T\asymp\sqrt L\).
In the second separation condition use the tolerance
\(100\exp(-v_s^-\ell^4)\). At any fixed initial tuple, the
number of shared-product choices is still \(\le m_0^K\),
so
\[
 \log|\mathcal N_s|\le K\log m_0+\ell^4\sum_{\nu<s}v_\nu^+
                        \le (1/10+o(1))v_s^-\ell^4 .
\]
The union over pairs and Markov at
\(\exp(-v_s^-\ell^4/4)\) therefore pay arbitrary logs,
also uniformly rather than only on average over the
auxiliary tuples. The first separation, bad repetitions,
Fourier/tensor and Schur evaluations of the cited audit use
only \(p_0,Y\) superpolynomial in \(L\), the stated second
separation, and the unchanged \(m_0,T\). In particular the
row and column estimates contain the identical
\(B_*m_0^{-K}\) term, \(B_*=KT\), and the just estimated
exponential tail. No fixed lower bound on \(V_\nu\) independent
of the fixed data is needed: in the normalization
\(\sum_{p\in\mathcal P_\nu}(V_\nu(p+1))^{-1}\le1\).
Other fixed powers of \(V_\nu^{-1}\) and their absolute
path-coefficient exponential cost \(e^{O_{K,V}(T+m_0)}\)
do not enter the saving exponent.

Also \(\log H=O_K(m_0\ell^4)=o(T)\);
the frame mesh frequencies and path products/counts still
fit the upper budgets in TinyTagProjection, §§1–2.
The full character high moment has \(j=O(L/\ell^4)\),
so \(j\log j+j\log L=o(L)\) as required.
Both source factors are genuinely \(Z\)-rough, the tag
primes are target units, and the signed long character
and restricted Gram inputs below are unchanged. This is
a proof-scale substitution in the full-target comparison,
not a use of the printed original-scale theorem with
its hypotheses omitted.

## 2. Actual prime pairs with one fixed set of geometric tag colors

Let \(\mathcal M\) be the actual products of one prime from
each band in (3) that also lie in (1). Suppose \(1+2\delta<C_0\).
At every such \(m\) and each \(x\) in the fixed compact
central support, \(r=y/m\) is in the original \(I\) whenever
it is an integer, because \(m\) has fixed strict exponent
margins from both ends. All true \(x,r\) are macroscopic
or \(N^{1-o(1)}\), and so are prime to \(N\) at these
small-radical targets. The same is true of the actual \(m\)
since all its primes exceed every fixed power of \(L\).
The true unscored count has the asymptotic
\[
 \sum_{\substack{x+mr=N,\ x\in NJ,\ m\in\mathcal M\\
                    x,r\ {\rm genuine\ primes}}}
      (\log x)(\log r)
 =
 |J|N\mathfrak S(N)\sum_{m\in\mathcal M}\frac{c(m)}m
       +O_D(NL^{-D}),\qquad
 c(m)=\prod_{p\mid m}\frac{p-1}{p-2},                        \tag{4}
\]
for prescribed fixed \(D>0\) and sufficiently large fixed \(K\).
The \(K\) used here is chosen after \(D\), then the bands
and \(\delta\) may be chosen as fixed constants.

To prove (4), keep the actual \(r\) prime. Replace the true
\(x\) by \(\Lambda(x)1_{P^-(x)>Z}\), with negligible power
error from the actual proper powers and divisor moments.
Use the exact rough Vaughan identity of TinyMOriginalGiant
with \(U=V=N^{.10}\). In the last (Type II) term the two
source slots are the actual rough \(\mu(a)\) and rough
\(\sum_{f\mid b,f>V}\Lambda(f)\). They have fixed positive
polynomial lengths. The **entire** \(m\) is the genuine tag,
not a hypothetical neutral divisor or a modeled prime.
The residual is the genuine logarithmically weighted \(r\),
with norm squared \(O((N/Y)L^{O(1)})\) at each tag shell.
Use the full small-radical long-\(\mu\) character bound and
restricted Gram estimate as in TinyMOriginalGiant. The
geometric tag comparison of §1 and Cauchy give arbitrary
prescribed log saving after increasing the fixed \(K\).
The two cutoffs in (1) can be smoothed in relative
\(L^{-G}\) collars: changed \(m\)'s are true divisors of
\(y\); their count is \(O(N(L^{-G}+1/M)+M)\) at either
scale \(M=S^{1+O(\delta)}\), hence negligible by fixed
divisor moments. The smooth gate on the entire \(m\)
separates by one Mellin integral into individual bounded
tag-prime multipliers; the same treatment of the central
test is ordinary. All distinct tag products are still
genuine squarefree products of disjoint colors.
The precision and number of log-power cells are fixed
before \(K\); a dyadic cover of the tag products needs
only \(O(\ell^4)\) shells and no distribution of
primes \(r\) in a projected inverse progression.

For each of the two Type I terms use actual prime \(r\)
Bombieri--Vinogradov at scale \(N/m=N^{1-o(1)}\), with
literal modulus \(q=a f e\le N^{.20+o(1)}\).
Here \(f=1\) in the first term, \(a,f\) are \(Z\)-rough,
and \(e\) opens the remaining rough free coordinate.
Use successive Bonferroni degrees \(C_D\ell\) with
sufficiently large fixed \(C_D\), since the reciprocal
mass of this \(Z\)-alphabet is \(O(\ell)\).
These labels are subpower and the true factor
\((m,Nq)=1\) is necessary. Only the factors of \(e\)
can meet \(m\) or a prime of \(N\), since all such
primes are below \(Z\). At the true fixed \(m\) and \(x\),
the first model therefore is
\[
 \left(\prod_{\substack{p\le Z\\p\nmid Nm}}
                        (1-\tfrac1{p-1})\right)
     \sum_{\substack{a\le U\\P^-(a)>Z}}
             \frac{\mu(a)}{\varphi(a)}\log(x/a),
\]
integrated in \(dx/m\). This keeps the literal \(\log(x/a)\);
it does not put the roughness label inside its argument.
The second model has exactly the same finite Euler product
and instead
\(\sum_{f\le V,\ P^-(f)>Z}\Lambda(f)
  \sum_{a\le U,\ P^-(a)>Z}\mu(a)/\varphi(a f)\).
Repeated \(p\) in \(a f\) is counted by the actual product
totient. All error estimates are at scale \(N/m\), summed
over the actual \(m\)'s by \(\sum_{m\in\mathcal M}1/m=O(1)\).
The usual divisor-weighted BV and positive omitted-degree
bounds apply with the same power reserve as in the
cited original Type I proof.

For clarity, the exact first-model Dirichlet series before the
harmonic \(1/a\) is
\[
 A(s)=\sum_{P^-(a)>Z}\frac{a\mu(a)}{\varphi(a)a^s}
   =\zeta(s)^{-1}G_Z(s),\qquad
 G_Z(s)=\prod_{p\le Z}(1-p^{-s})^{-1}
         \prod_{p>Z}\left(1-\frac1{p-1}
                               \sum_{j\ge1}p^{-js}\right).
\]
For the harmonic at fixed \(f\) use
\(\varphi(f)a\mu(a)/\varphi(a f)\) instead. Its local
factor in \(G_Z\) is \(1\) at \(p\mid f\) (all such
\(p>Z\)), and is unchanged elsewhere. This follows
from \(\varphi(p f)=p\varphi(f)\) at \(p\mid f\).
Both absolute convolution norms are \(L^{O(1)}\)
uniformly in \(f\) at \(1-c/\log Z\) for small fixed
\(c>0\): the small-prime inverse factors cost a power
of \(\log Z\), and the remaining prime factors
are absolutely summable there. Classical Mertens
and convolution splitting at the square root of a prefix
give arbitrary-log tails at \(a\ge U=N^{.10}\), also
with the extra \(\log a\). Thus the zero at \(s=1\)
kills the \(\log x\) term and the second model, and
\(-\sum_{P^-(a)>Z}\mu(a)\log a/\varphi(a)=A'(1)=G_Z(1)\)
in the first. The external \(\sum_{f\le V}\Lambda(f)/
\varphi(f)\) is only a fixed log loss. Finally,
\[
 G_Z(1)=\prod_{p\le Z}(1-\tfrac1p)^{-1}
               \prod_{p>Z}(1-\tfrac1{(p-1)^2}),
\]
and multiplying by the retained finite rough product
gives exactly \(\mathfrak S(N)c(m)\). This verifies
the Type I main and proves (4).

## 3. A same-annulus composite reserve larger than its prime debit

Choose fixed constants
\[
 0<a_{K-1}<b_{K-1}<a_{K-2}<b_{K-2}<\cdots<a_1<b_1<1 .
\]
For \(i<K\) take the actual color of primes
\([S^{\delta^{b_i}},S^{\delta^{a_i}}]\), and for \(i=K\) take
\([S^{.9},S]\), for fixed sufficiently small \(\delta>0\)
chosen **after** \(K\) and these constants.
The geometric separation (3) holds because every preceding
upper exponent is of strictly higher power of \(\delta\) than
the next lower exponent, and the sum of all \(K-1\) small
upper exponents is \(<.05\). The least exponent
\(\delta^{b_1}\) exceeds \(4\delta\).
Each actual product in (1) therefore has every proper
divisor \(\le S^{1+2\delta-\delta^{b_1}}<T_y\), but
\(m>T_y\) because the physical \(r=y/m<B\) as checked in
§2. These inequalities hold for every retained row for all
sufficiently large \(N\), with uniform compact-support margins. It is squarefree of even
rank, so \(Q_y(m)=-\mu(m)=-1\) pointwise.
All these \(m\)'s miss the original tiny banks, since
their least primes exceed \(\exp(\delta^{b_1}\ell^4)\).

For every fixed actual choice of the first \(K-1\) primes,
writing \(t=\log_S\prod_{i<K}p_i\), the final genuine
prime interval for (1) is
\([S^{1+\delta-t},S^{1+2\delta-t}]\). It lies wholly in
\([S^{.9},S]\), since \(4\delta<t<.05\).
Writing \(u=1+\delta-t\), the prime reciprocal sum there is
\(\log((u+\delta)/u)+O_D(L^{-D})\) uniformly in the real
\(u\in[.9,1-\delta]\). Indeed partial summation of the
classical prime number theorem has error
\(\exp(-c\sqrt{\log(S^{.9})})\) up to a power of \(\log S\).
The main is at least \(\delta\). The same argument gives
\((b_i-a_i)\log(1/\delta)+O_{D,K,\delta}(L^{-D})\) for every
small color, since its lower log-scale is a fixed positive
multiple of \(\ell^4\). Each actual product is counted
exactly once by its disjoint colors. Thus
\[
         \sum_{m\in\mathcal M}\frac{c(m)}m
                  \gg_K\delta(\log(1/\delta))^{K-1}.
\]
All reciprocal prime bounds here take \(N\) large after
the fixed \(\delta\). By (4), the selected real composites
supply at least this multiple of \(|J|N\mathfrak S(N)\)
with a **negative** sign.

For the genuine prime \(m\)'s in the very same annulus,
\(Q_y(m)=1\). At each actual prime \(m\), the true two
prime values \(r,N-mr\) have the two-form positive sieve
bound of [TinyMWholeWindows.md, §2](TinyMWholeWindows.md),
here on the full compact central interval. Accordingly
the positive prime-\(m\) score is at most
\(C_J N\mathfrak S(N)\sum_{p\ {\rm in}\ (1)}c(p)/p
 \ll_J \delta N\mathfrak S(N)\).
Here the reciprocal prime sum is
\(\log((1+2\delta)/(1+\delta))+O_D(L^{-D})\) with
\(c(p)=1+O(S^{-1-\delta})\).
This is an upper for the genuine prime-\(m\) population,
not its presumed asymptotic. Choose \(\delta\) so small that
the proven negative coefficient exceeds this bound by
at least a fixed positive multiple of \(\delta\).
This is possible for fixed \(K\ge2\).
It gives (2) on the exact disjoint union and leaves
all other actual composite quotient signs open.

For comparison, fix the admissible \(K\) and \(K+1\) before
choosing \(\delta\), and run the same construction with
\(K+1\) separate colors chosen for that rank. The same divisor
margins now give \(Q_y(m)=+1\). In either construction the last
reciprocal prime interval has mass between fixed positive
multiples of \(\delta\), since its log endpoints lie in
\([.9,1]\). Thus the selected reciprocals in rank \(k\) are
of order \(\delta(\log(1/\delta))^{k-1}\), with constants
depending on its fixed color profiles, for \(k=K,K+1\) and
\(N\) sufficiently large after \(\delta\). Both ranks meet
the tag condition in (4), and their physical populations
are disjoint. Consequently an independently selected
positive odd-rank cohort can even exceed the negative
one for \(\delta\) sufficiently small after both choices.
This does not change (2), which includes the prime debit
but excludes these higher odd-rank rows; it explains why
no total composite sign follows from the reserve.
