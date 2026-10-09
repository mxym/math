# An exact pure qutrit counterexample to ECQC

**Yongxian Zhang** — School of Computer Science and Engineering, South China University of Technology. Email: mxymmxym1@gmail.com. ORCID: 0009-0000-3864-3536.

Written proof recorded on October 8, 2026 (America/Los_Angeles). AI-assisted research; no external funding; no external professional peer review claimed. Original material copyright 2026 Yongxian Zhang, all rights reserved.

## Source and scope

Hasan Iqbal, *On the CQC Conjecture: A sufficient condition and an extension*, arXiv:2509.08286v2, Conjecture 3.1 / equation (6), proposes ECQC. Its Section 5 separately asks for an analytic proof for pure states. Journal DOI: https://doi.org/10.1007/s11128-026-05258-2 .

Wang, Wang, and Chen, arXiv:2608.03828v2, already give a **mixed**, classical–classical ECQC counterexample at local dimension seven and unbounded mixed-state overrun. The result below is not claimed as the first disproof of unrestricted ECQC. It refutes the pure-state question at local dimension three. The original **two-basis** CQC statement for pure states is not contradicted.

This note is a complete written proof for the actual quantum state, bases, Born tables, and entropies. It is not a claim of a complete Lean formalization. A finite literature search does not establish historical priority.

## Definitions

For a bipartite density matrix rho, let Q(rho)=S(rho_A)+S(rho_B)-S(rho), with natural logarithms. For an orthonormal basis M used identically on both parties, let I_M be the Shannon mutual information of its Born outcome table. For a complete family M of four mutually unbiased bases in dimension three, ECQC asserts

    E_M(rho) := sum_{M in family} I_M(rho) - max_{M in family} I_M(rho) <= Q(rho).

Thus exactly the three smallest of the four scores are retained. Division by log(2) expresses all quantities in bits.

## The state and the bases

Let omega=exp(2 pi i/3). Use the computational basis and, for a=0,1,2,

    |b_(a,j)> = (1/sqrt(3)) sum_(x=0)^2 omega^(a*x^2+j*x) |x>,  j=0,1,2.

These are complete MUBs. Within one basis, orthogonality is the geometric-sum identity. Between quadratic bases, writing A=a-a' != 0 and B=j-j',

    |sum_x omega^(A*x^2+B*x)|^2
      = sum_u omega^(A*u^2+B*u) sum_y omega^(2*A*u*y) = 3.

Normalization gives squared overlap 1/3; computational overlaps are also 1/3.

Consider the real-coefficient pure state

    |psi> = (|01> + |02> - |10> - |20>)/2.

Its coefficient matrix is

    C = (1/2) [[ 0, 1, 1],
               [-1, 0, 0],
               [-1, 0, 0]].

The four nonzero amplitudes have modulus 1/2, so the state is normalized. Both reduced density matrices are

    R = (1/4) [[2, 0, 0],
               [0, 1, 1],
               [0, 1, 1]],

with eigenvalues (1/2,1/2,0). The global state is pure, so Q=2 log(2).

## Exact Born probabilities in every setting

In the computational basis the table is

    P = (1/4) [[0, 1, 1],
               [1, 0, 0],
               [1, 0, 0]].

The same literal table occurs in all three quadratic bases. To see this without numerical calculation, set

    r_j = omega^(-j) + omega^(-2j),
    r_0=2, r_1=r_2=-1.

Every supported computational pair in |psi> has x^2+y^2=1 modulo three. Hence its amplitude in basis a is exactly

    (<b_(a,j)| tensor <b_(a,k)|)|psi>
       = omega^(-a) (r_k-r_j)/6.

Its squared modulus is 1/4 when exactly one of j,k is zero, and zero otherwise. This proves the claimed table for every a.

The row and column distributions of P are (1/2,1/4,1/4), each of entropy (3/2) log(2), while the joint distribution has four masses 1/4 and entropy 2 log(2). Therefore every one of the four settings has

    I_M = log(2).

Deleting any largest term leaves

    E_M = 3 log(2) > 2 log(2) = Q.

The strict excess is exactly one bit. No numerical approximation, surrogate entropy model, unproved conjecture, or finite-to-infinite inference is used.

## Sharpness at dimension three and the dimension-two boundary

The standard pure-state Holevo bound gives I_M <= S(rho_A)=Q/2 for each local measurement setting: measuring one side of a pure state prepares an ensemble of pure conditional states on the other side, whose accessible classical information is at most its average-state entropy. Consequently every pure-state three-dimensional ECQC score satisfies E_M <= (3/2)Q, and the displayed state attains this ratio. This upper bound uses the established Holevo theorem, not an assumed ECQC inequality.

In dimension two, the ECQC score retains only two terms, so the same bound gives E_M<=Q for all pure states. Thus local dimension three is the smallest prime dimension admitting a pure-state ECQC counterexample. The all-prime extension, other exact witnesses, checkers, and manuscript are separate materials; they are not needed for this proof.

## References

- H. Iqbal, arXiv:2509.08286v2, https://arxiv.org/html/2509.08286v2 , Conjecture 3.1 and Section 5.
- J. Wang, Q. Wang, K. Chen, arXiv:2608.03828v2, https://arxiv.org/html/2608.03828v2 , Section IV and Appendix B (prior mixed-state ECQC counterexamples).
- J. Schneeloch, C. J. Broadbent, J. C. Howell, *Uncertainty relation for mutual information*, Physical Review A 90, 062119 (2014), https://doi.org/10.1103/PhysRevA.90.062119 (the original CQC statement and its pure-state case).
