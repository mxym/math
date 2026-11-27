# Proof of the noisy-link fidelity bounds

## 1. Setting

Use the equal-dimension three-region stabilizer setting of the companion
noiseless result. A prime-p stabilizer code is an isometry Q → ABC. The secret
Q and target B each consist of m ≥ 1 qudits, so d = p^m. Erasure of each of
A, B, and C separately is exactly correctable. The helper A measures, chooses
an input x to one use of a finite classical channel W:X→Z, and the target
applies a CPTP decoder depending on the received symbol z. Randomized encoding
of a finer helper outcome is absorbed into a POVM indexed by x. Conditioning
on independent preshared classical randomness gives the same bounds, and
averaging cannot improve them.

Let b be the canonical cleaned logical-to-target Pauli isomorphism and let

    D(v,w) = Omega_B(bv,bw) - Omega_L(v,w),
    rank(D) = 2r.

Set q = 2m-r and N = p^q. The figure of merit is entanglement fidelity for the
maximally mixed secret.

For the channel define

    C(W) = sum over z in Z of max over x in X of W(z|x)

and

    C_N(W) = max over S subset X, 1 ≤ |S| ≤ N, of
             sum over z in Z of max over x in S of W(z|x).       (1)

Repeated inputs never help in (1). Since every row of W sums to one,

    C_N(W) ≤ min(C(W),N).                                       (2)

## 2. Stabilizer-algebra lemma

We record the precise part of the noiseless proof used below. After a
maximally entangled reference is introduced and C is traced out, every helper
POVM outcome x leaves an unnormalized positive state sigma_x on RB such that

    sum_x sigma_x = I_RB/d^2.                                  (3)

All sigma_x belong to a fixed twisted-Pauli algebra A. Its commutator form is
D, and its noncommutative factor has matrix size p^r. Consequently, if
p_x = Tr(sigma_x) > 0, then

    operator_norm(sigma_x/p_x) ≤ p^(-r).                       (4)

For every target decoder, the pullback T of the maximally entangled projector
is positive and has trace one. The trace-one statement uses that the target
and output dimensions are both d.

There is also a canonical attaining measurement. A maximal D-isotropic
subspace gives N equiprobable branches

    sigma_y = Pi_y/d^2,    y = 1,...,N,                         (5)

where the Pi_y are pairwise orthogonal rank-p^r projections and sum to the
identity. For each y, a target unitary has a trace-one pullback T_y supported
on Pi_y, with

    Tr(sigma_y T_y) = 1/d^2.                                   (6)

These statements follow by measuring commuting helper Paulis from a maximal
D-isotropic subspace. The symplectic extension/Clifford argument puts a
maximally entangled vector in every Pi_y.

When r = 0, the algebra is abelian, N = d^2, and the projections Pi_y in (5)
are rank one. Every positive element of A is diagonal in this Bell basis.

## 3. Universal upper bound

After the classical channel, the unnormalized state associated with received
symbol z is

    tau_z = sum_x W(z|x) sigma_x.                               (7)

Put alpha_z = max_x W(z|x). Positivity and (3) give

    0 ≤ tau_z ≤ alpha_z I/d^2.                                 (8)

Also, tau_z is another positive element of A. Applying (4) to the
coarse-grained outcome z, and writing p_z = Tr(tau_z), gives

    operator_norm(tau_z) ≤ p_z p^(-r).                         (9)

If T_z is the decoder pullback, then T_z is positive and Tr(T_z)=1. Thus

    Tr(tau_z T_z) ≤ min(alpha_z/d^2, p_z p^(-r)).              (10)

Summing the first terms and the second terms separately yields

    F*_W ≤ min(C(W)/d^2, p^(-r))
         = min(C(W),N)/d^2.                                    (11)

The last equality uses N/d^2 = p^(-r).

## 4. Channel-code lower bound

Choose a subset S = {x_1,...,x_k}, k ≤ N, attaining C_N(W). Use the canonical
measurement (5) and assign x_i to a different branch y_i. Assign the other
branches arbitrarily. For each received z, choose i(z) with

    W(z|x_i(z)) = max over x in S of W(z|x),

and apply the decoder associated with branch y_i(z). Orthogonality of the
Pi_y removes every other branch, while (6) gives

    F_W = (1/d^2) sum_z max over x in S of W(z|x)
        = C_N(W)/d^2.                                          (12)

Combining (11) and (12) proves

    C_N(W)/d^2 ≤ F*_W ≤ min(C(W),N)/d^2.                       (13)

The value is exact whenever C_N(W)=min(C(W),N).

## 5. Exact value for zero defect

Assume r=0. By the last paragraph of Section 2, every helper ensemble has a
unique expansion

    sigma_x = (1/d^2) sum_y e(x|y) Pi_y,                       (14)
    e(x|y) ≥ 0, and sum_x e(x|y) = 1.

Thus e is a stochastic encoder for N classical hypotheses. For any decoder
pullback define

    t_z(y) = Tr(Pi_y T_z).

The t_z(y) are nonnegative and sum to one over y. Therefore

    F_W
      = (1/d^2) sum_(z,y,x) t_z(y)e(x|y)W(z|x)
      ≤ (1/d^2) sum_z max_y sum_x e(x|y)W(z|x).                (15)

The right side is convex in the N rows e(·|y). A convex function on their
product of probability simplexes has a maximizer at an extreme point, so an
optimal encoder can be deterministic: each y chooses one channel input. Its
distinct chosen inputs form a set of size at most N. Hence (15) is at most
C_N(W)/d^2, and (12) attains this value. Because r=0 gives N=d^2,

    F*_W = C_N(W)/N.                                           (16)

This is the optimal one-use N-message classical channel-coding success
probability, expressed as entanglement fidelity.

## 6. Exact common channels

For an N-ary erasure channel with 0 ≤ eta ≤ 1,

    W(z|x) = (1-eta) if z=x, and 0 otherwise,
    W(erasure|x) = eta.

Using all N input rows in (1) gives

    C_N(W) = C(W) = N(1-eta)+eta.

Thus

    F*_W = (1-eta)p^(-r) + eta/d^2.                            (17)

The second term is the best fixed correction when the helper message is
erased; it is not zero.

For N ≥ 2 and 0 ≤ eta ≤ 1, the N-ary symmetric channel is

    W(z|x) = 1-eta       if z=x,
             eta/(N-1)  if z differs from x.

Here

    C_N(W) = C(W) = N max(1-eta, eta/(N-1)),

and consequently

    F*_W = p^(-r) max(1-eta, eta/(N-1)).                       (18)

At high error the decoder uses a most likely different input, exactly as
ordinary maximum-likelihood decoding does.

Finally, a noiseless L-symbol channel has C_N(W)=min(L,N) and C(W)=L.
Equation (13) is exact and becomes

    F*_W = min(p^(-r), L/d^2),

which is the earlier finite-message result.
