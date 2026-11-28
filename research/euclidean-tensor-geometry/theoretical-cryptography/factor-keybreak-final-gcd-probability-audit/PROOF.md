# Exact audit of KeyBreak equations (5.4)–(5.5)

## Scope

The source is the 26 November 2026 version of *Provable Integer Factorization via Multilevel Descent: Approaching Heuristic Bounds*. This note checks only the transition from equation (5.4) to equation (5.5), plus the downstream numerical threshold used in Theorem 6.1.

It does not audit the rest of the relation-count, square-certificate, or complexity proof.

## 1. Conditional final-GCD probability

Let (omega=omega(N)) be the number of distinct prime divisors of the odd current input (N). After the public record and the verified public root (Y) have been fixed, the paper's private-root lemma makes (X) uniform among the (2^omega) unit roots of (Y^2).

CRT identifies those roots with independent sign choices at the (omega) prime-power components. Exactly two sign vectors give a trivial gcd:

* all plus: (X=Y), so (gcd(X-Y,N)=N);
* all minus: (X=-Y), so, because (N) is odd and (Y) is a unit, (gcd(X-Y,N)=gcd(-2Y,N)=1).

Every other sign vector separates a nonempty proper set of prime-power components. Therefore the exact conditional probability of a proper factor is
[
q_omega=rac{2^omega-2}{2^omega}
=1-2^{1-omega}.
]
This agrees with the source's equation (5.4).

## 2. The mismatch in equation (5.5)

Write
[
B=left[rac34(1-epsilon)-epsilon_{m pub}ight]_+.
]
The immediately preceding derivation supplies public success mass at least (B), followed, when the final gcd is reached, by conditional success probability (q_omega). Thus the direct lower bound is
[
q_omega B
=(1-2^{1-omega})B.
]

Printed equation (5.5) replaces (q_omega) with (1-2^{-omega}). For every finite (omegage2),
[
1-2^{-omega}>1-2^{1-omega}.
]
No lower bound for earlier immediate-factor outcomes is supplied that would make up this exact difference. Those outcomes add nonnegative probability but cannot justify the printed stronger factor from the stated information.

At (omega=2), the discrepancy is already explicit:
[
q_2=rac12,qquad 1-2^{-2}=rac34.
]

## 3. Downstream consequence

For the paper's thresholds,
[
epsilonlerac14,qquad
epsilon_{m pub}lerac1{16},
]
we have
[
Bge rac34cdotrac34-rac1{16}=rac12.
]
The splitting procedure is applied only after the current input is known not to be a prime power, so (omegage2) and
[
q_omegagerac12.
]
Consequently the corrected lower bound remains
[
q_omega Bgerac14.
]

Appendix F.8 independently uses precisely the two factors (1/2) (public mass) and (1/2) (hidden-root extraction), and the running-time proof later uses only the weaker (p_0=1/128). Hence this correction does not change Theorem 6.1's stated success input or the (L_N[1/3,10^{13}]) constant.

## Conclusion

* Equation (5.4): correct.
* Printed equation (5.5): local overstatement.
* Correct replacement: ((1-2^{1-omega(N)})B).
* Main unconditional complexity theorem: unaffected by this local correction, within the audited dependency chain.
