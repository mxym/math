# The true prime-reflected layer at a power of two has a sharp weighted scale

Written research note, 2026-11-24. Companion to the [dyadic target obstruction](G23PowersOfTwoMultiplicativeObstruction.md). This note contains no surrogate. All source slopes and both prime reflections are genuine. It obtains an upper matching the preserved prime-layer lower scale and identifies the signed compensation needed for actual \(\lambda\).

Let \(P=2^j\) and use the full true prime slope range \(P^\sigma<p\le P^{1/2}e^{-(\log P)^{3/5}}\), \(W(p,k)=1_{pk\in PJ}\log(pk)/\log P\), and \(R_z,\kappa_z,L\) from that note. For \(C=1\) or the actual translated first-cover indicator with fixed \(M\ge400\), put
\[
 B_C(k)=\sum_p W(p,k)C(P,pk)1_{\{P-pk\ {\rm prime}\}}.
\]
Then uniformly as \(P=2^j\) becomes large,
\[
 \sum_k kR_z(k)B_C(k)^2\asymp_{\sigma,J} P^2\kappa_z/L^3 .
 \tag{1}
\]
For the lower bound, the companion note's actual Bombieri–Vinogradov/rough sieve count (4)–(5) gives \(\sum_k R_z(k)B_1(k)\gg P\kappa_z/L\) from a subangle of eligible true slopes. Mark deletion costs \(o(P\kappa_z/L)\) in that count by the actual rough-and-packet integer co-sieve (with each source integer counted only \(O_\sigma(1)\) times). Cauchy against \(\sum_{k\ \mathrm{in\ scope}}R_z(k)/k\ll \kappa_z L\) gives the lower part of (1). The logarithmic weights are uniformly bounded below on a fixed interior subwindow. No paired-prime lower bound is invoked.

For the upper bound we may drop \(C\) and \(\log(pk)/L\), since \(B_C\) is nonnegative. Partition the first slope \(p\) into \(O(L)\) dyadic intervals \(p\asymp U\); the physical \(k\)-window forces \(p'\asymp_J U\) and \(k\asymp_J K=P/U\). The weighted diagonal is \(O(P^{2-\sigma})\), by summing \((P/p)^2\) for genuine \(p>P^\sigma\).

Fix distinct genuine \(p,p'\), \(d_0=|p-p'|>0\). Use the same elementary finite Selberg square as in the companion note at divisor level \(P^{1/100}\) and prime cutoff \(W_0=P^\theta\), with fixed \(\theta<\sigma\) sufficiently small for the denominator Markov argument. Thus \(z<W_0<\min(p,p')\). The lattice variable is \(k\) with an actual interval of length \(O_J(K)\). Relevant conditions are \(k\) \(z\)-rough and both \(P-pk,P-p'k\) actual primes in the reflected physical range. At each odd \(\ell\le z\) the bad roots are \(0,Pp^{-1},Pp'^{-1}\); two nonzero roots coincide exactly when \(\ell\mid d_0\). For \(z<\ell\le W_0\) only the latter two roots are forbidden. The sole prime dividing \(P\) is 2, at which the roots all coincide. At 3 the generic case forbids all residue classes, so there are no true rows in that case; the other case has a fixed positive survival. All these kills are valid since all sought primes exceed \(W_0\). For \(\ell\ge 5\) the generic survival is bounded above by \((1-1/\ell)^3\) below \(z\) and \((1-1/\ell)^2\) above \(z\), and is bounded below by those factors times \(1-O(\ell^{-2})\). Coincidence of nonzero roots increases these generic factors by at most \(1+C_0/\ell\) for a fixed \(C_0\). The CRT Selberg upper bound is therefore
\[
 \ll_J K\,\frac{\kappa_z}{L^2}\,S(d_0)+P^{.04+o(1)},\qquad
 S(h)=\prod_{\ell\mid h,\ \ell\ge5}(1+C_0/\ell).
 \tag{2}
\]
The weight bound and floors are uniform: on the surviving case the local product is \(\gg\kappa_z/L^2\), so the Selberg coefficients are \(L^{O(1)}\); CRT remainder is at most \(\nu([s,t])\le[s,t]\) per ordered pair \(s,t\le P^{1/100}\), as before. This gives the stated floor \(P^{.04+o(1)}\).

We need the genuine prime-pair average \( \sum_{p,p'\asymp_J U,\ p\ne p'} S(|p-p'|)\ll_{\sigma,J} U^2/L^2\). Indeed \(S(h)=\sum_{d\mid h}g(d)\), where \(g\) is squarefree supported on primes \(\ge5\) and \(g(d)=C_0^{\omega(d)}/d\). For \(d\le U^{.1}\), fix the first true prime \(p\) and count the second true prime in the reduced class \(p\bmod d\), since \(p\gg_J U>d\). The elementary Brun–Titchmarsh upper \(O_J(U/(\varphi(d)\log U))\) also follows from the one-dimensional Selberg proof above: work on the actual lattice \(p'=p+dt\), sieving primes \(\ell\nmid d\) to \(U^\theta\), with divisor level \(U^{1/100}\); the root count is 1, and omitted primes dividing \(d\) multiply the density by at most \(d/\varphi(d)\), with floor \(U^{.04+o(1)}\) absorbed uniformly at \(d\le U^{.1}\). The initial number of true \(p\) is \(O_J(U/\log U)\), giving the claimed bound for this \(d\) after summing with \(\sum_d g(d)/\varphi(d)<\infty\). For the large-divisor tail, each nonzero \(|h|\ll_J U\) satisfies \(\sum_{d\mid h,d>U^{.1}}g(d)\le U^{-.1}(1+C_0)^{\omega(h)}=U^{-.1+o(1)}\); even the integer pair count \(O_J(U^2)\) suffices. This proves the prime-pair average without a prime-pair asymptotic.

Multiplying (2) by \(O_J(K)\) for the weight and summing genuine pairs gives \(O(P^2\kappa_z/L^4)\) per dyadic scale. The cumulative lattice floors are \(O(P^{.04+o(1)} K U^2)\) per scale, which is \(O(P^{1.54+o(1)})\) since \(KU=P\), \(U\ll\sqrt P\), and the log number of scales is absorbed. This proves the upper half of (1).

To see the fixed-target consequence, write the actual Liouville slope vector as \(H_C-B_C\), where \(H_C\) restricts to composite reflections and retains the true rough and signed weights. If the desired squared \(kR_z\)-energy is \(o(P^2 V_y(P)^2/(\kappa_z L^5))\), then
\[
 \langle B_C,H_C\rangle_{kR_z}
 =\|B_C\|_{kR_z}^2(1+o(1)),\qquad
 \|H_C\|_{kR_z}^2=\|B_C\|_{kR_z}^2(1+o(1)).
\]
The desired error scale is smaller than the prime reflected energy scale by \(L^{-1.52-2\delta}\). Both identities require compensation in the exact \(k\)-weighted space, not merely two scalar totals of opposite sign. No estimate of this required signed prime/composite correlation is claimed.