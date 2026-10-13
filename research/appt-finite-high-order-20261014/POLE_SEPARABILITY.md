# Explicit finite product decomposition of the known white-noise pole

Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology; mxymmxym1@gmail.com;
ORCID 0009-0000-3864-3536. 14 October 2026. No external funding.
OpenAI AI assistants assisted. Original exposition all rights reserved;
prior mathematical results remain credited. Ordinary proof, not Lean.

## 1. Endpoint and attribution

For every bipartite pair 2≤m≤n, D=mn, and every unit vector v,

    ρ_v=(I+2vv*)/(D+2)                                  (S1)

is absolutely separable, and hence APPT. This endpoint is already known
from pure-state white-noise robustness. In
[Vidal–Tarrach, Section 4.B, equation (41), and Appendix B](https://arxiv.org/html/quant-ph/9806094),
the required white-noise robustness is D s_1s_2≤D/2, for ordered Schmidt
coefficients. Their Appendix B.1 supplies the product-phase construction.
The finite product formula below verifies the endpoint directly for the
present proof packet; it is not claimed as a new separability threshold.

We do not use a presumed equality of general APPT and ASEP sets. Showing S1
is separable for every v suffices: any global unitary takes ρ_v to ρ_(Uv).

## 2. A finite phase average

Local basis changes preserve separability, so write

    v=Σ_(i=1)^m s_i |ii>,   s_i≥0,   Σ_i s_i²=1.

Zero Schmidt coefficients are allowed. Let ζ be a primitive cube root of
unity, and for t∈{0,1,2}^m put

    a_t=Σ_i √s_i ζ^(t_i)|i>,
    b_t=Σ_i √s_i ζ^(−t_i)|i>,
    Ω=3^(−m) Σ_t |a_t⊗b_t><a_t⊗b_t|.                   (S2)

These product vectors need not be normalized; Ω is a finite nonnegative
combination of product projectors. Its matrix element at |ij><kl| contains
the phase ζ^(t_i−t_j−t_k+t_l). Independent averaging of each t_r kills a
nonzero charge. Each charge is an integer in [−2,2], so vanishing modulo
three is equivalent to being zero as an integer. The surviving indices
satisfy either i=j and k=l, or i=k and j=l. Counting the intersection only
once gives

    Ω=vv*+Σ_(i≠j) s_i s_j |ij><ij|.                    (S3)

This holds for arbitrary finite m, not just the finite diagnostic cases.

## 3. Nonnegative residual product terms

Complete the local Schmidt bases and let I_out be the sum of product basis
projectors outside their m×m square. Then

    I+2vv*
      =2Ω+Σ_i |ii><ii|
           +Σ_(i≠j)(1−2s_i s_j)|ij><ij|+I_out.         (S4)

Every coefficient is nonnegative, since
2s_i s_j≤s_i²+s_j²≤1. Every term is a product projector. The sum has trace
D+2. Normalize each nonzero product vector, multiply its coefficient by its
squared norm, and divide by D+2: the weights are nonnegative and sum to one.
This is an explicit finite convex combination proving S1 separable.
Applying the same argument to Uv for every global U proves absolute
separability, with no sampled-unitary or model-replacement assumption.

## 4. Connection with the finite entropy theorem

The ordered spectrum of S1 is (3,1 [D−1 times])/(D+2), so

    Tr(ρ_v^α)=(3^α+D−1)/(D+2)^α.                        (S5)

This supplies actual ASEP attainment for the general-dimensional high-order
minimum in [FINITE_SPIKE_PHASE.md](FINITE_SPIKE_PHASE.md). Its optimality
and uniqueness in the stated bands require the additional arguments there;
separability alone does not prove a power maximum.

The white-noise endpoint and phase-averaging method are prior mathematics.
The general APPT-versus-ASEP problem is not solved here. No new formal module
or old audit claim is attached to this decomposition.
