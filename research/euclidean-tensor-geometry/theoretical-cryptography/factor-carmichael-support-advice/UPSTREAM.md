# Sources, correction, and scope

## Stronger smooth-subgroup route

**Bartosz Źrałek**,
*A deterministic version of Pollard's p-1 algorithm*,
Mathematics of Computation 79 (2010), 513--533,
arXiv: https://arxiv.org/abs/0707.4102 ,
DOI: https://doi.org/10.1090/S0025-5718-09-02262-5

In arXiv v5, Lemma 8.3 (printed p. 18) gives the key implication used
in [SUPERSEDED.md](SUPERSEDED.md): if the tested bases give no
Fermat--Euclid witness, their common order \(A\) satisfies
\[
 A=\#\langle B\rangle_p\ge\Psi(p,y),
 \qquad p=1+mA.
\]
Combining this with the standard smooth-number lower bound and
geometrically increasing \(y\) gives the support-adapted
\[
 L_{P_{\mathcal S}(N)}[1/2,1+o(1)]\operatorname{poly}(B)
\]
bound. This is strictly stronger than the old power-time theorem
retained here.

## Analytic input for the retained proof

**Yuk-Kam Lau and Jie Wu**,
*On the least quadratic non-residue*,
International Journal of Number Theory 4 (2008), Theorem 1,
author preprint:
https://hkumath.hku.hk/~imr/IMRPreprintSeries/2007/IMR2007-4.pdf

Equation (1.5) and Theorem 1 yield the
\(1/(4\sqrt e)+\varepsilon\) exponent for prime conductors. This
validates the retained character-separation argument but no longer gives
the best bound for the advice model.

## Closely related oracle discussion

**François Morain, Guénaël Renault, and Benjamin Smith**,
*Deterministic factoring with oracles*,
arXiv:1802.08444v2 (13 August 2021),
https://arxiv.org/abs/1802.08444

Section 6.1 (printed pp. 19--20) discusses complete factorizations of
\(\varphi(N)\) and \(\lambda(N)\) and explains why naive divisor
enumeration need not be polynomial.

**Jacek Pomykała and Maciej Radziejewski**,
*Integer factoring and compositeness witnesses*,
Journal of Mathematical Cryptology 14(1) (2020), 346--358,
DOI: https://doi.org/10.1515/jmc-2019-0023 ,
conference preprint:
https://nutmic2019.imj-prg.fr/confpapers/FactoringWitnesses.pdf

Their small-prime-order and power-difference witness framework is
closely related to the refinement used here.

## Exact novelty status

The support-to-exponent step
\[
 E_{\mathcal S}(N)=
 \prod_{r\in\mathcal S,\ r\le N}r^{\lfloor\log_rN\rfloor},
 \qquad \lambda(N)\mid E_{\mathcal S}(N),
\]
is a direct input conversion. Applying established factored-exponent
algorithms to it is a corollary, not an independent factoring method.
The old Burgess proof is retained only as a valid weaker route.
