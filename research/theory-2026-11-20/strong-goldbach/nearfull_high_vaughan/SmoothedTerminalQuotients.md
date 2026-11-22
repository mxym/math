# Averaged giant cutoffs and the whole terminal quotient cohort

Let \(N\) be an individual sufficiently large even target, \(J\Subset
(0,1)\) a fixed nondegenerate compact interval, \(L=\log N\),
\(\ell=\log L\), \(H=\ell^4\), and \(S=e^H\). Write \(x\in NJ\),
\(y=N-x\), and \(\mathfrak S=\mathfrak S(N)\) for the binary singular
series in the [original giant reduction](../giant_prime_divisor_remainder/Proof.md).
The labels \(x,r\) below are genuine primes, and \(m=y/r\) is the
actual integer quotient. The two prime-logarithmic weights are unchanged.

Fix a nonnegative \(w\in C_c^\infty((0,1/2))\) with \(\int w=1\).
For \(0<\delta<.01\) set \(\tau(u)=1+\delta u\),
\(B_u=N/S^{\tau(u)}\), and \(T_u(y)=y/B_u\). Define
\[
 \overline Q_y(m)=
       \int w(u)\sum_{\substack{d\mid m\\d<T_u(y)}}\mu(d)\,du
       \qquad(m>1).
\]
For any prescribed \(D>0\), take a sufficiently large fixed \(C_D\)
and put \(U_*=\sqrt N/(S^{1+\delta/2}L^{C_D})\). If
\(R_J(N)\) is the original weighted binary count, then **at every
even target**
\[
 R_J(N)=|J|N\mathfrak S
 -\sum_{\substack{x+mr=N,\ x\in NJ,\ m>1\\
                   x,r\ {\rm prime},\ r>U_*}}
      (\log x)(\log r)\overline Q_y(m)
 +O_D(NL^{-D}).                                                   \tag{1}
\]

**Whole terminal cohort.** For each fixed \(B_0>0\) there are
\(\delta_0>0\) and \(\kappa>0\) such that, for each fixed
\(0<\delta\le\delta_0\), at every even \(N\) with
\(\operatorname{rad}(N)\le L^{B_0}\), the absolute value of the signed
subsum of (1) on
\[
                             r\ge N/S^{1+2\delta}                 \tag{2}
\]
is bounded by
\[
                 O_{J,w}(N\mathfrak S\,\delta^\kappa)
                      +o_{\delta,J,w,B_0}(N\mathfrak S).           \tag{3}
\]
There is no remaining roughness, rank, sign, or bank condition
on \(m\) in (2). This is the averaged score, not a bound for its
sharp counterpart at any particular \(u\). The remainder of (1)
over \(U_*<r<N/S^{1+2\delta}\) is not bounded by (3).
In particular (3) is not a binary lower bound.

**All-even positive upper bounds.** More generally use any fixed
smooth compactly supported nonnegative probability weight in
\(\tau\in[a,b]\), \(1\le a<b<\infty\), to define \(\overline Q\).
For any fixed \(C>0\), the sum of \((\log x)(\log r)|\overline Q_y(m)|\)
over the true rows with \(1<m\le S^C\) is \(O(N\mathfrak S)\).
The additional conditions in the following three separate
positive sums improve the bound by the factors shown:
\[
 \begin{array}{c|c}
 P^-(m)\le S^\eta & O(\eta)\\
 m\text{ not squarefree}& O(H^{-1})\\
 \omega(m)\ge k & O_t(t^{-k})\quad(t>1\text{ fixed}).
 \end{array}                                                       \tag{4}
\]
Constants can depend on the fixed smooth weight and \(C,J\),
and on \(t\) in the last row, but not on \(\eta>0,k,N\).
These are bounds on the true prime rows. They do not control
ranks on an unsmoothed score.

## 1. Common lower cutoff and a positive real-prime upper

The uniform marked-prefix estimate (2) in the original giant
reduction is valid for \(S^{\tau(u)}\ge S\) in the fixed range here.
Its admissible lower-mark cutoff
\(\sqrt N/(S^{\tau(u)}L^{C_D})\) is always at least \(U_*\).
In that estimate take \(a_d=1_{d\le U_*}\). The former complementary
upper model is uniform: \(T_u(y)\gg_J S\), its signed harmonic
tails start beyond a fixed multiple of \(S\), and its B--V moduli
are \(dn\le U_*S^{\tau(u)}\le\sqrt N/L^{C_D}\).
The subsequent discard of proper-power marks \(>U_*\) keeps the
same \(N^{3/4+o(1)}\) bound. The proof of the original formula
therefore applies for every \(u\), at this *same* lower mark \(U_*\).

In that formula the upper gate is \(r\le B_u\). If \(m>1\)
and \(r>B_u\), then \(T_u(y)>m\) and every divisor is included,
so the full Möbius sum is zero. The case \(r=B_u\) retains the
strict-divisor convention. If \(m=1\), then \(r=y\gg_J N>B_u\)
uniformly, so this row is never in the original remainder and
must (as in (1)) stay excluded. Integrating against \(w\) now
gives (1). For the general weights use \(b\) in place of
\(1+\delta/2\) in the common \(U_*\), by the same argument.

Discard \(x\mid N\) at \(N^{o(1)}\) cost on the real prime rows:
there are \(O_J(1)\) such central primes, with at most
\(\tau(y)\) possible \(r\) and \(|\overline Q|\le\tau(m)\).
Then \((y,N)=1\) and all live \(m,r\) are target units and odd.
At fixed \(1<m\le S^C\), the genuine \(r\) and \(x=N-mr\)
count, with both prime logs, satisfies
\[
 \sum_{\substack{x+mr=N,\ x\in NJ\\x,r\ {\rm prime}}}
       (\log x)(\log r)
  \ll_{J,C} \frac{N\mathfrak S}{m}\,c(m),\qquad
                c(m)=\prod_{\substack{p\mid m\\p>2}}\frac{p-1}{p-2},
                                                                  \tag{5}
\]
on the retained units. This is the positive fixed-\(m\)
dimension-two sieve in [TinyMWholeWindows, §2](TinyMWholeWindows.md):
at \(p\mid Nm\) there is one root, elsewhere two; at 2
there is one root. The interval length is of order
\(N/m=N^{1-o(1)}\) and the floor has a fixed power reserve
uniformly for \(m\le S^C\). We use (5) only as a positive upper,
and may enlarge to all \(m\) after it, with the convention \(c(2)=1\).

## 2. Positive Fourier--Euler envelope and absolute rank bounds

For \(B\ge1\) fixed, \(X\ge1\), and \(\xi\in\mathbb R\), write
\(Z_\xi(n;X)=\prod_{p\mid n}|1-e^{i\xi\log p/X}|\).
Uniformly at \(\sigma=1\), and at \(\sigma=1-1/X\) for \(X\ge2\),
\[
 \prod_{p\le e^{BX}}
 \left(1+c(p)|1-e^{i\xi\log p/X}|
                         \sum_{j\ge1}p^{-j\sigma}\right)
                       \ll_B (2+|\xi|)^{O_B(1)}.                    \tag{6}
\]
Indeed the prime-power sum is \(\ll_B p^{-1}\): use
\(p^{1/X}\le e^B\) and \(1-p^{-\sigma}\ge1-2^{-1/2}\).
Also \(c(p)\le2\). Put \(v=\max(1,|\xi|)\). The log product
is bounded by a constant times
\[
       (|\xi|/X)\sum_{p\le e^{X/v}}\frac{\log p}{p}
               +2\sum_{e^{X/v}<p\le e^{BX}}\frac1p
        \ll_B 1+\log(2+|\xi|).
\]
If \(e^{X/v}<2\), the first sum is empty, and use
\(\log X\ll\log(2+|\xi|)\) in the second. Otherwise use prime
Mertens and its \(\log p\)-weighted bound. This also covers
\(1\le X<2\) at \(\sigma=1\).

For (4), let \(F(t)\), \(t\ge0\), be the upper cumulative of the
\(\tau\)-weight, smoothly cut off to the left of zero. The
extension does not affect any \(\log(dN/y)/H\). For the transform
\(\hat F(\xi)=\int F(t)e^{-i\xi t}\,dt\), Fourier inversion gives
\[
 \overline Q_y(m)=\frac1{2\pi}\int_{\mathbb R}\hat F(\xi)
           e^{i\xi\log(N/y)/H}
            \prod_{p\mid m}(1-e^{i\xi\log p/H})\,d\xi .             \tag{7}
\]
All powers are exact because \(\mu(d)\) is squarefree-supported.
Take absolute values inside the integral, use (5), and enlarge
the positive harmonic sum to all integers supported on
\(p\le S^C\). Its Euler product is (6) with \(X=H\)
and \(B=\max(1,C)\). Schwartz decay proves the first bound.

Marking any \(p\le S^\eta\) occurring in \(m\) costs, in its
summed marked local term at \(\sigma=1\), at most
\((|\xi|/H)\sum_{p\le S^\eta}O(\log p/p)\ll\eta|\xi|\).
It is zero if \(S^\eta<2\). Marking a square costs instead
\(O(|\xi|H^{-1}\sum_p(\log p)/p^2)\).
In each case all other prime factors are bounded by (6).
For the last line insert \(t^{\omega(m)}t^{-k}\) once:
each nonconstant Euler term is multiplied by \(t\). Thus
only the fixed polynomial exponent in (6) changes. Schwartz
integration gives (4), with no \(y\)-mesh in these bounds.

## 3. The true covered terminal sum

Choose a fixed logarithmic comparison precision after the
fixed divisor and separation losses below, then its sufficiently
large fixed \(K\), then \(\delta\le\delta_0(K)\).
Take the geometric banks of
[RoughQuotientWholeAnnulus, §1](RoughQuotientWholeAnnulus.md):
\(z_\delta=S^{4\delta}\), every bank prime is in
\((z_\delta,S^{2\sqrt\delta}]\), each color has reciprocal
mass in \([1/4,1/2]\), and there are \(\asymp_K\log(1/\delta)\)
disjoint families. Their fixed geometric separation and
prime-weight norms are those of
[TrueCompositeQuotientCredit, §1](TrueCompositeQuotientCredit.md).
Let \(E(m)\) mean that some family has every color hit by a
genuine prime dividing \(m\).

At each fixed \(u\), retain both real prime endpoints
\([N/S^{1+2\delta},B_u]\); at fixed \(y\) the \(m\) range is
\([T_u(y),yS^{1+2\delta}/N]\).
Apply the left rough Vaughan expansion of
[TinyMOriginalGiant, §§1--2](TinyMOriginalGiant.md) to the actual
\(x\), with \(Z=\exp(L^{.24})\) and both cutoffs \(N^{.10}\).
The Type II factors are genuinely \(Z\)-rough, and all prime
factors of \(m\) are \(<Z\). Use the first actually successful
family, and, after excluding actual bank squares, extract
one real prime per color in \(a\mid m\), with \(m=a m'\).
The exact allocation is \(\prod_i(1+\omega_i(m'))^{-1}\);
earlier-family failures are unchanged on \(m'\) because the
families are disjoint. The square incidence and its restoration
after opening selected-tag coprimality cost arbitrary logs:
each changed row still has \(a\mid m\mid y\) and actual
\(p^2\mid y\) for some bank prime \(p>S^{4\delta}\), and uses
only the fixed divisor-power envelope.

The short score becomes precisely
\(\sum_{s\mid a}\mu(s)\sum_{d\mid m',\,ds<T_u(y)}\mu(d)\).
Freeze the \(m\)-window and \(T_u(y)\) on a log-fine central
mesh and smooth the literal boundaries in thinner collars,
as in TinyMOriginalGiant §1. Each changed endpoint concerns
an actual \(m\mid y\) or \(ds\mid y\) at scale \(\gg_J S\)
and size \(S^{O(1)}\); its global multiple count and the fixed
crossed divisor moments are the same, uniformly for all \(u\).
For each of the \(2^K\) fixed subset positions \(s\mid a\),
separate the \(a m'\)-window and the \(ds\)-threshold by
their own Mellin integrals. The tag weights are bounded
products of individual color multipliers, and the single right
coefficient on \(m'r\) retains genuine \(\log r\), the masks
and the \(d\)-score. The square norm on \(a\asymp Y\) is
\(O((N/Y)L^{O(1)})\) by the fixed divisor envelope.
No separate \(m\)- or \(r\)-average is used. The fixed number
of Mellin tests and mesh/divisor powers are independent of
\(\delta\); the finite bank count can enter the implied constant.
The geometric projection yields \(O_{\delta,D'}(NL^{-D'})\)
at a preassigned fixed \(D'\), after fixing \(K\) large enough,
by the uniform long \(\mu\)-character and restricted Gram
inputs for polylogarithmic radical in the cited proofs.
This is where the radical hypothesis enters.

For the Type I terms use genuine prime \(r\) maximal BV
at scale \(N/m=N^{1-o(1)}\), modulus \(q\le N^{.20+o(1)}\),
in the true class \(N\bar m\bmod q\) with \((m,Nq)=1\),
as in [TrueCompositeQuotientCredit, §2](TrueCompositeQuotientCredit.md).
At fixed \(m\) the opened strict \(d<T_u(y)\) and the two
\(r\)-endpoints are real prefix restrictions; the free log
costs only bounded log variation. The sum of BV errors
takes the scale \(N/m\) and the harmonic
\(\sum_{m\le S^{1+2\delta}}\tau(m)/m\), not the cardinality.
The same Euler derivative applies on \((m,N)=1\):
all prime factors of \(m\) are \(<Z\), and the short \(Z\)-rough
Möbius variables and long rough free factor give exactly
\(\mathfrak S c(m)\) as in that proof. Target-dividing
\(m\)'s are not included.
Change from \(r\) to \(x=N-mr\), with Jacobian \(1/m\).
The true covered sum at fixed \(u\) is therefore
\[
 \mathfrak S\int_{NJ}
    \sum_{\substack{T_u(y)\le m\le yS^{1+2\delta}/N\\
                    (m,N)=1,\ E(m)=1}}
           \frac{c(m)}m
           \sum_{\substack{d\mid m\\d<T_u(y)}}\mu(d)\,dx
                   +O_{\delta,D'}(NL^{-D'}).                      \tag{8}
\]
On integrating in \(u\) we may drop the lower \(m\)-gate
at \(m>1\) because its outside score is zero pointwise.
The remaining model uses the same \(\overline Q_y(m)\)
and \(1<m\le yS^{1+2\delta}/N\).

## 4. No-hit bound without roughness of the quotient

For \(r=y/m\), put \(v=(\log(N/r)-H)/(\delta H)\),
and denote the lower cumulative \(\int_{u<t}w(u)\,du\)
by \(G(t)\). It is zero for \(t\le0\).
On (2) one has \(v\le2\). Complementing the divisor
sum at \(m>1\) gives exactly
\[
 \overline Q_y(m)=-\sum_{q\mid m}\mu(m/q)\,
                        G\!\left(v-\frac{\log q}{\delta H}\right).
                                                                  \tag{9}
\]
Indeed, the complementary weak bound \(q\le m/T_u(y)=B_u/r\)
is equivalent to \(u\le v-\log q/(\delta H)\);
changing equality affects no mass in \(u\).
The score is zero if \(v\le0\) and otherwise only
\(q\le S^{2\delta}\) can contribute. In particular all
possibly nonzero rows have \(m\ge c_J S\) for a fixed
\(c_J>0\), since \(v>0\) implies \(r<N/S\).

Factor \(m=A n\) into the full prime-power part on
\(p\le z_\delta\) and its full complementary rough part \(n\).
All \(q\)'s in (9) divide \(A\). The score is \(-\mu(n)\)
times the \(A\)-sum using \(\mu(A/q)\), and is zero
when \(n\) is not squarefree. Put \(s=A/\operatorname{rad}(A)\).
Exactly the \(q\)'s of the form \(s d\), \(d\mid\operatorname{rad}(A)\),
have \(\mu(A/q)\ne0\); there is no extra coprimality condition
between \(s,d\).
For \(X=\delta H\) and \(0\le v\le2\) set \(g_v(t)=G(v-t)\)
for \(t\ge0\) and extend by a fixed smooth cutoff below zero.
Its support lies in a common compact interval, and
\(|\hat g_v(\xi)|\le C_j(1+|\xi|)^{-j}\) uniformly in \(v\)
for every fixed \(j\).
The Fourier integrand of the \(A\)-sum contains exactly
\(\mu(\operatorname{rad}A)e^{i\xi\log s/X}
 \prod_{p\mid A}(1-e^{i\xi\log p/X})\).
This holds for \(A=1\), with the empty product equal to 1.
If \(W(A)\) is \(1/(2\pi)\) times the integral of
\(C_j(1+|\xi|)^{-j}Z_\xi(A;X)\) for a sufficiently large fixed
\(j=j(w)\), then by (6) with \(B=4\)
\[
  |\overline Q_y(m)|\le W(A),\qquad
  \sum_{P^+(A)\le z_\delta}\frac{c(A)W(A)}A\ll_w 1,\qquad
  \sum_{\substack{P^+(A)\le z_\delta\\A>S^{1/2}}}
       \frac{c(A)W(A)}A\ll_w e^{-1/(2\delta)}.                     \tag{10}
\]
For the last inequality insert \((A/S^{1/2})^{1/X}\)
and use (6) at \(1-1/X\). All constants here are independent
of small fixed \(\delta\), after \(N\) is large enough for \(X\ge2\).

Since every bank prime exceeds \(z_\delta\), its hit or
failure status depends only on \(n\). For \(A\le S^{1/2}\)
enlarge the actual \(n\)-range to
\([c_J S/A,S^{1+2\delta}/A]\).
The harmonic measure of true \(z_\delta\)-rough no-hit
integers \(n\) in this interval is
\(O(\delta^\kappa)+o_\delta(1)\), uniformly in such \(A\).
Indeed the nonnegative Boolean majorant and disjoint
roughness upper sieve of
[RoughQuotientWholeAnnulus, §2](RoughQuotientWholeAnnulus.md)
have genuine product labels \(bd\le S^{.2}\).
Their total harmonic floor here is
\(O_\delta(S^{.2}/(c_JS^{1/2}))\). The exact integer main
is a failure factor \(O(\delta^\kappa)\) times rough
density \(O(1/\log z_\delta)\) times interval log width
\(2\delta H+O_J(1)\). Thus its constant is uniform in
small fixed \(\delta\). Moreover \(c(n)=1+O_\delta(z_\delta^{-1})\),
since \(n\le S^{1+2\delta}\) and is rough.
For \(A>S^{1/2}\) allow all rough \(n\), including \(n=1\);
their positive \(c(n)/n\) sum for \(n\le S^{1+2\delta}\)
is \(O(1/\delta)\), by the full Euler product on primes
in \((z_\delta,S^{1+2\delta}]\).
Multiply the respective bounds by (10), using
\(c(An)=c(A)c(n)\). This proves
\[
 \sum_{\substack{c_J S\le m\le S^{1+2\delta}\\E(m)=0}}
 \frac{c(m)}m\sup_{\substack{y/N\in 1-J\\r=y/m\ {\rm in}\ (2)}}
                 |\overline Q_y(m)|
          \ll_{J,w} \delta^\kappa +o_\delta(1),                    \tag{11}
\]
where an empty supremum means zero. The Rankin part
\(O(\delta^{-1}e^{-1/(2\delta)})\) is absorbed.
Only in this positive upper were target masks dropped.
By (5) it pays the actual missed score in absolute value,
and it also pays the model cost of replacing \(E(m)=1\)
by all \(m\) in the integrated (8).

## 5. The exact full model

At fixed \(x,u\), the complete signed \(m\)-harmonic in (8)
with \(E(m)=1\) removed is \(O_\delta(L^{-D'})\).
Use the weighted harmonic (4) of
[the high-cut calibration, §1](Proof.md) with \(T=T_u(y)\)
and \(X_0=yS^{1+2\delta}/N\). Its proof extends verbatim:
\(T\gg_J S\), \(X_0/T\ge S^{3\delta/2}\), and both endpoints
are \(S^{O(1)}\), so the absolute Euler-floor tail and the
signed harmonic derivatives save arbitrary fixed log powers
uniformly in \(u\) after fixed \(\delta\).
The model up to \(X_0\) has the sole lower atom \(+1\) at
\(m=1\); subtract it, since every \(1<m<T\) individually
vanishes. Retain the possible strict-score term at \(m=T\)
if \(T\) is integral. Thus this model cancellation occurs
before integration against \(w\) and includes the exact
\(c(m)\) factors. Now combine (8), (11) and the bound for the
actual missing primes to prove (3).

The terminal conclusion prices the nonrough and rough parts on
one exact **smoothed** score; it is not an additive credit with
the earlier sharp rough-annulus theorem. For context on smoothed
truncated divisor weights, compare
[Granville--Koukoulopoulos--Maynard, Theorems 1.4 and 10.4](https://dms.umontreal.ca/~koukoulo/documents/publications/sieveweights.pdf).
The reciprocal absolute estimates here use the elementary
Fourier--Euler calculation (6)--(7). The fixed-target signed
conclusion additionally needs the successful-bank projection,
the genuine greatest-mark prime BV, and the literal
two-prime upper.
