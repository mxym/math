# Square-root-window prime roots with an exact small-factor profile and a rough P4 quotient

This extends the [square-root-window weighted-sieve result](PrimeOppositeSquareRootP4.md) by imposing a moving local profile on the same actual complements. The number of prime factors is bounded by four **after removing the prescribed factor**, not before removing it.

Fix \(0<a<b\) and \(A>0\). Let \(N\) be sufficiently large and even, \(H=\sqrt N\), \(L=\log N\), \(I=(aH,bH]\) and \(X=\operatorname{Li}(bH)-\operatorname{Li}(aH)\). Let \(d,m\) be positive integers with \(dm\le L^A\) and \(\operatorname{rad}(d)\mid m\). Choose a residue \(r\bmod m\) such that
\[
 (r,m)=1,\qquad (N-dr,dm)=1.
\]
Write \(S_N\) for the singular factor in the parent proof and put
\[
 X_0=\frac{X}{\varphi(dm)},\qquad
 S_1=S_N\prod_{\substack{\ell\mid m\\\ell\nmid N}}
                \Bigl(1-\frac1{\ell-1}\Bigr)^{-1},
 \qquad B_0=\frac{2X_0 S_1}{L}.
\]
Then there are at least \((3/40+o(1))B_0\) distinct primes \(p\in I\), \(p\equiv N-dr\bmod dm\), for which the actual integer
\[
 Q=\frac{N-p}{d}
\]
is squarefree, has no prime factor below \(N^{1/20}\), and satisfies \(\Omega(Q)\le4\). The error is uniform in these choices for fixed \(A,a,b\). On all these rows \(Q\equiv r\bmod m\); hence \(v_\ell(N-p)=v_\ell(d)\) for every \(\ell\mid m\).

## Short marks: preserve prime distribution at the real source scale

Restrict the actual prime inputs to the stipulated reduced progression, dropping the \(O(L)\) primes that divide \(N\). For a squarefree test divisor \(s\) coprime to \(dmN\), \(s\mid Q\) is equivalent to \(p\equiv N\bmod s\); the new combined progression modulo \(dm\,s\) is reduced by CRT. The modeled density is \(1/\varphi(s)\), relative to \(X_0\). A test prime dividing \(m\) is not needed because \(Q\equiv r\bmod m\) is a unit there. A prime dividing \(N\) but not \(m\) also cannot divide the quotient on a retained prime row.

With \(s\le N^{.249}\), the combined modulus is \(\le L^A N^{.249}\), still below the ordinary Bombieri–Vinogradov range at actual source length \(H\). The map \(s\mapsto dm\,s\) is injective, so the same fixed divisor-weighted error bound follows by Cauchy–Schwarz as in the parent paper. This remains true when the uniquely marked prime \(q\) and its complementary sieve modulus occur with combined modulus \(q s\le N^{.249}\): it is that product to which \(dm\) is adjoined. For the \(O(L)\) omitted source primes, the only nonzero count errors are on divisors of their actual \(N-p\); even with fixed divisor powers their total is \(N^{o(1)}\). Dividing by \(B_0\), whose reciprocal loss beyond \(H\) is at most a fixed log power, still leaves any desired log saving.

In the one-form local product, omission of the primes of \(m\) replaces \(S_N\) by \(S_1\). All these primes lie below each cutoff used in the proof for large \(N\); their omission can only improve the uniform upper bound on the dimension-one product ratio. Thus the normalized rough-prime lower and the short-mark upper coefficients from the parent paper are unchanged, now in units \(B_0\) and \(B_0/q\).

## Switched long marks: the two local corrections cancel exactly

For a long prime mark \(\ell_0=q\), keep the same cutoffs \(.22<\log q/L<.30\) and \(K=N^{(.5-\log q/L)/2-.001}\) as in the parent argument. Here \(q>K\), \(q\nmid dm\), and \(q\mid N\) yields no retained input because \(q\ne p\). Write \(Q=qj\). The actual residue for \(j\) is \(j\equiv r q^{-1}\bmod m\); write \(j=j_0+m k\). The real \(k\)-interval has length
\[
 \frac{(b-a)H}{dqm},
\]
and the two polynomials to sieve are \(j=j_0+mk\) and \(p=N-dq(j_0+mk)\). At each prime \(\ell\mid m\) both give fixed nonzero residues. At each other prime \(\ell\le K\), both nonconstant coefficients are units, and the two bad roots coincide precisely when \(\ell\mid N\). The sieve treats both roots below \(N^{1/20}\), and above that cutoff only the root forbidden by primality of \(p\), exactly as before.

Write \(\nu(\ell)=1\) if \(\ell\mid N\) and \(2\) otherwise, and \(g(\ell)=0\) if \(\ell\mid N\) and \(1/(\ell-1)\) otherwise. The full two-form Selberg denominator now has local singular factor
\[
 S_2=S_N\prod_{\ell\mid m}\bigl(1-\nu(\ell)/\ell\bigr)^{-1}.
\]
Indeed the local squarefree weight at an omitted prime is replaced by 0 on its positive powers. In the Euler-convolution proof this adds only an \(O(1/\ell)\) change to the local log-moment estimates; the exceptional primes are among those of \(Nm\), whose logarithm is \(O_A(L)\). The uniform logarithmic-moment argument is unchanged. All omitted primes are below the rough cutoff, so the one-root telescoping loss at larger primes retains the same integral \(J(v)\). Floors in the actual \(k\)-progressions still contribute \(O(K^2 L^C)\) per \(q\); summing produces \(O(HN^{-.002}L^C)=o(B_0)\). No prime distribution at the shorter \(k\)-scale is assumed.

The switched count in units \(B_0/q\) has the old exact coefficient because
\[
 \frac{\varphi(dm)}{dm}\frac{S_2}{S_1}
 =\prod_{\ell\mid m}
   \frac{(1-1/\ell)(1-g(\ell))}{1-\nu(\ell)/\ell}=1.
\]
For \(\ell\mid N\) the numerator and denominator are both \(1-1/\ell\); for the other case they are both \(1-2/\ell\). Since \(N\) is even, \(\ell=2\) is included only in the first case. Also \(\operatorname{rad}(d)\mid m\), so no extra factor remains in \(\varphi(dm)/(dm)\).

## Weighted extraction and one concrete family

Apply the same Richert weight to \(Q<N\), with the same sieve cutoff and the same normalization constants \(A_0,C,\eta\) as in the parent paper. The positive margin \(A_0-C/\eta>3/40\) remains unchanged. A square divisor \(w^2\mid Q\) with \(N^{1/20}\le w\le N^{1/3}\) costs \(O(H/(dN^{1/20})+N^{1/3})\) in the literal quotient interval. For larger \(w\), write \(Q=cw^2\) with \(c\le N^{1/3}\); the interval for \(w\) has length \(O(H/\sqrt{dNc})\). Its total integer cost is \(O(N^{1/3}+H/(\sqrt d\,N^{1/3}))\). These errors are \(o(B_0)\) even with the bounded Richert weight. Its sum is thus positive on genuine squarefree quotient rows. Each such row with \(\Omega(Q)\ge5\) has nonpositive weight, and every weight is at most 1, giving the asserted bound.

For \(N=2^k\), set \(d=m\) to the product of all odd primes at most \(c\log\log N\), for any fixed \(c>0\), and choose \(r=1\). The conditions hold and \(dm\le (\log N)^{2c+o(1)}\). Thus on many real square-root-scale prime rows, \(N-p\) contains every one of those growing small primes exactly once, followed by at most four distinct prime factors, all at least \(N^{1/20}\). For general even \(N\) the analogous construction can omit primes dividing \(N\). This does not imply three or fewer prime factors in the quotient, a prime quotient, a Goldbach pair, or a bound of four on the full \(N-p\) when \(d>1\).

The local sieve and its normalized inequality are classical ingredients reused from the parent proof. Related results on prime inputs in progressions at a much longer source scale include [Runbo Li's work](https://arxiv.org/abs/2309.03218). The present statement imposes the exact prescribed quotient residue in a fixed square-root-scale interval; no priority claim is made.
