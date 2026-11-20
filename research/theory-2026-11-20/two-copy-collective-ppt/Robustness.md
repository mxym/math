# A certified two-copy PPT error floor

For the uniform ensemble of the nine specified maximally entangled two-qutrit states in [the two-copy theorem](README.md), every collective PPT measurement on two identical copies has average error strictly greater than **1/20,000,000**. The bipartition is Alice's two qutrits versus Bob's two qutrits. This also bounds collective SEP and LOCC. It is a conservative lower bound, not an evaluation of the optimum. This is not about the separate two-qubit Watrous ensemble.

## Approximate moment constraints

Use the notation and vec convention of [the original proof](two-copy.tex). Group outcomes by the claimed label, let `E_i` be the resulting PPT effects, and write `p_i` for the conditional probability of a correct report on label `i`. Put `Δ = 1 - (Σ_i p_i)/9`. We may assume `Δ ≤ 1/20,000,000` to obtain a contradiction.

With `R_i = (I⊗V_i†) E_i (I⊗V_i)`, `J_i = R_i^Γ`, and `S` the swap between the two 9-dimensional labs, write `P_±=(I±S)/2`, `J_i^+=P_+J_iP_+`, `t_i=tr(J_i^+)`, and `a_i=tr(P_-J_i)`. The correct-label probabilities give `9p_i = t_i - a_i`. Taking the sum of the traces of the effects gives `Σ_i a_i = 81Δ/2`. Also `p_i≥1-9Δ` for each label.

Block-decompose `J_i≥0` into symmetric and antisymmetric subspaces. Its off-diagonal block has trace norm at most `√(a_i t_i)`: write `J_i=LL†` and use the Hilbert–Schmidt product inequality on `P_+L (P_- L)†`. Multiplication by `S` only changes the signs of the antisymmetric block row. Thus
```
|| S J_i - J_i^+ ||_1 ≤ a_i + 2√(a_i t_i) ≤ 39√Δ .
```
Here `a_i≤81Δ/2`, `t_i≤9+a_i`, and the last numerical inequality follows, for example, from `(81/2)√Δ<1/100`, `t_i<901/100`, and `√((81/2)(901/100))<96/5`.

Without assuming symmetric support, the indexed contraction in the original proof reads
```
<<A|R_i|T>> = tr[(S J_i)(A†⊗T)].
```
Indeed contracting the indices gives `Σ_abcd conj(A_ba) (J_i)_cb,ad T_dc`; swapping the first two row indices rewrites this as the displayed trace. If `A=V_i†V_j` for a wrong label `j≠i`, then `<<A|R_i|A>>=9 Pr(i|j)≤81Δ`. Since `0≤R_i≤I`, Cauchy–Schwarz bounds the contraction by `9√Δ ||T||_F`. Replacing `SJ_i` by `J_i^+` adds at most `39√Δ ||A||_∞ ||T||_∞`. The bound for `A⊗T` follows by complex conjugation when `T` is Hermitian.

For `W=F-I/3`, with `F` swapping the two qutrits within one lab, each `V_i` commutes with `W`. Consequently `Σ_i tr[J_i(W⊗W)] = (tr W)^2 =0`. The sum of the nonnegative contractions `<<W|R_i|W>>` equals `Σ_i tr[(S-I)J_i(W⊗W)]`. Because `W⊗W` commutes with `S`, this sees only the antisymmetric blocks. The sum is at most `2||W||_∞² Σ_i a_i=144Δ`, using `||W||_∞=4/3`. Each individual `W` contraction against `T` is therefore bounded by `12√Δ ||T||_F` before replacing `SJ_i` by `J_i^+`.

## Witness and mismatch

For the original clock-label certificate `K_*`, its 20 symmetric-sector blocks stay positive definite after subtracting 120 times the diagonal Gram matrix of the unnormalized orthogonal basis in each block. All 45 leading principal minors are strictly positive, the smallest 88. Thus `K_*>120 I` on the symmetric subspace. The standard-library [exact replay](robust_check.py) applies the Gram shift to the existing integer certificate, and checks these minors and every constant below. Run `python3 -O robust_check.py` in this directory.

For the Hermitian second-factor matrices `T_1,T_3,T_4`, absolute row-sum bounds are `26,109,30`, and squared Frobenius norms are `944,16132,1100` (their square roots are less than `31,128,34`). The difference terms `49ν(A-A†)`, where `ν=i√3`, have operator norm at most `98√3<170`. Their contraction bounds follow by summing the bounds for the two unitary summands. The remaining term is `147W`, with operator norm 196. Conjugating by the unitaries in the original witness leaves these estimates intact: the allowed short list of wrong-label unitaries is permuted up to phases, those phases have modulus one, and `W` is fixed.

The three unnormalized cyclic conjugates and normalized remaining averages give
```
|tr(J_Z^+ K_*)| ≤ 3 [39(170(26+109)+196·30)
                  + 9·170(31+128) + 147·12·34] √Δ
                = 4,282,848√Δ < 974 .
```
The compression to the symmetric subspace does not affect this trace. But `tr(J_Z^+ K_*) ≥ 120 t_Z ≥ 120(9-81Δ)>1079` by positivity. This is the contradiction.

With the same uniform prior, replace each single-copy state by any density operator within trace distance `1/80,000,000` (trace distance means half the trace norm). Its two identical copies are within `1/40,000,000` of the old pair by the tensor-product triangle inequality. The success probability of any fixed measurement is 1-Lipschitz in that distance for each input. Thus even without purity or orthogonality the perturbed ensemble has collective two-copy PPT average error strictly greater than **1/40,000,000**.
