# N0 checkpoint 2: a global certificate route and its exact obstruction

15 October 2026 (Asia/Shanghai). Yongxian Zhang (张永贤), South China
University of Technology. No external funding. OpenAI AI assistants
assisted. All original rights reserved. External work is attributed below.

**Complete N0 is still open in this packet; new major solutions = 0.**
These notes preserve a failed sufficient route and finite controls while
research continues on the original all-copy, all-complex-rank-two target.

## 1. Why an entangled-reference Schur certificate would suffice

On two auxiliary copies of H=(C^d)^{tensor k}, put

    R = product_i (I-F_i/2) > 0.

For a fixed unit u in H and arbitrary x, let

    A=(<u| tensor I) R (|u> tensor I),
    L=(<u| tensor I) R (|x> tensor I),
    D=(<x| tensor I) R (|x> tensor I).

For C=|u><v|+|x><y|, the rank-two Werner form is

    Q_k(C)=<v,Av>+<y,Dy>+2 Re<y,Lv>.

Thus D-L A^{-1} L* >=0 would imply Q_k(C)>=0. It is the switched
order: ordinary block positivity of R only supplies D-L* A^{-1} L>=0.
For product u, the one-site co-Choi contraction argument in
[Wu–Zou, Section7.2](https://arxiv.org/html/2608.02647v1#S7.SS2)
controls the switched order. Its tensor-contraction mechanism is an
attributed input, not a claimed new major theorem here.

Let R_ab=(<a| tensor I)R(|b> tensor I), L_a=(<u| tensor I)R(|a> tensor I).
Define maps

    Lambda(E_ab)=R_ba,
    M_u(E_ab)=L_a A^{-1} L_b*.

Then D=Lambda(|x><x|), L A^{-1}L*=M_u(|x><x|). The strong certificate

    R - sum_ab E_ba tensor L_a A^{-1} L_b* >= 0                 (S)

would make Lambda-M_u completely copositive and hence positive. Proving
(S) for every u and every k at one physical d>=3 would therefore prove
endpoint undistillability and settle N0 affirmatively. That is why this
was tested as a full-target route rather than just a fixed-copy exercise.
Numerous generic and highly entangled tests satisfy (S), but the universal
statement is false. The following exact control rejects it.

## 2. Exact 10-term rejection of (S)

It is enough to use three qubit sites. Write e_i for the three bit strings
of weight one and f_i=111-e_i for the weight-two strings, i=1,2,3. Set

    u=(e_1+e_2+e_3)/sqrt(3),
    w=sum_ij (4-3 delta_ij) f_i tensor e_j +111 tensor 000.

There are ten nonzero terms and ||w||^2=100. Here R is the product of
three I-F_i/2 factors. Direct SWAP counting gives, for each i and each
distinct pair i,j,

    <w,F_i w>=66,  <w,F_i F_j w>=34,  <w,F_1 F_2 F_3 w>=0.

For the first count, four off-diagonal (f_a,e_b), a!=b, are fixed by
F_i and contribute 4*4^2=64; the f_i tensor e_i and 111 tensor000 terms
are exchanged and contribute another2. For the second count, two
off-diagonal terms are fixed and contribute32; two diagonal terms are
exchanged and contribute2. Global exchange moves the support outside
itself. Therefore

    <w,Rw>=100-(3/2)66+(3/4)34=53/2.

For the other term in (S), A preserves total qubit weight and

    A|000>=(1/4)|000>,  A^{-1}|000>=4|000>.

This follows either by expanding the three factors or by contracting the
three equal diagonal entries of u. Put L_a^int=sqrt(3)L_a. For the
weight-two reference strings,

    L^int_{f_i}|000>=-(1/4) sum_{j!=i}|e_j>.

One of the two occupied bits must be swapped out, while the unused zero
bit contributes the factor1-1/2. On the support of w, the only surviving
inverse-A contractions pass through |000>: a weight-two first string and
weight-one second string are required on both sides. The term with
first string111 gives zero in this contraction. If w_a is the second-leg
coefficient vector attached to first string f_a, put

    t_ab=<w_a,L^int_{f_b}000> = -2, a=b;  -5/4, a!=b.

Consequently, with Mhat_u=sum_ab E_ba tensor L_a A^{-1}L_b*,

    <w,Mhat_u w>=(4/3)[3*4+6*(25/16)]=57/2,
    <w,(R-Mhat_u)w>=-2.                                    (R)

The rational script independently reconstructs the64-by-64 co-Choi matrix
and verifies (R) exactly. The proof above only needs the displayed
weight-zero inverse entry, so it does not depend on numerical eigenvalues.

This counterexample embeds unchanged into qubit supports of three
qutrit sites: the required contractions never leave those supports.
It rejects the **universal complete-copositivity certificate (S)**.
It does not reject positivity of Lambda-M_u on positive inputs. Indeed,
the physical qubit endpoint W_2=I-|Omega_2><Omega_2|/2 is a projection;
W_2^{tensor k}>=0 for every k and every coefficient rank. Hence there
is no distillation counterexample here. This separation is a required
adversarial control against confusing a sufficient matrix relaxation
with the actual N0 condition.

## 3. An exact high-copy probe, with the restriction made explicit

For a qutrit occupation type u=(u_0,u_1,u_2), sum u_i=k, let |D_u> be the
normalized Dicke ray, and M(u)=k!/(product u_i!). Consider only four rays

    A1=|D_u><D_v|, A2=|D_r><D_s|,
    r-u=s-v=Delta, u!=r, v!=s.

This gives legitimate collective rank-two coefficient matrices z1 A1+z2 A2;
it does not cover arbitrary complex rank-two matrices. Schmidt
orthogonality holds within each pair because the types differ.

For a traced subset of j slots, the squared Dicke Schmidt coefficient at type a is

    P_u(a)=[j!(k-j)! product u_i!]/[k! product a_i!(u_i-a_i)!].

The partial-trace cross term pairs a with a+Delta, which has the same
total j. At lambda=1/2 define the integer

    J(u,s,Delta)=sum_a (-1)^j 2^{k-j} j!(k-j)!
                  product_i binom(u_i,a_i)binom(s_i,a_i+Delta_i),
    j=sum a_i.

Terms outside the binomial ranges are zero. Multiplying the squared
crossed-Gram determinant by a positive factorial factor reduces its sign
exactly to the sign of

    M(v)M(r) J(u,v,0)J(r,s,0) - M(u)M(s)J(u,s,Delta)^2.        (D)

The script uses polynomial convolution with integer coefficients; there
is no alternating floating-point cancellation in (D). It checks the
cross formula against actual complex coefficient-matrix contractions
on45 small examples, and rejects the known lambda=51/100 one-copy
negative control. At the endpoint it exhausts every four-type pair in
this specified sector for k=2,...,14. It also samples3,083–3,266 admissible
pairs at each k=20,30,50,80,120. No negative determinant was found.
This is neither an all-type theorem for unbounded k nor a full-rank-two
result. The complete target remains N0 rather than (D).

## 4. Additional active approaches and their unresolved gates

The original numerical Rayleigh search is complemented by a complex
Stiefel search of |cross|^2/(diagonal1*diagonal2). Temporary log-det
barriers keep all local qutrit supports full during preconditioning;
they are released before the final objective is recorded. Directional
gradients, including the barrier, are checked independently. The observed
maximizers flow to known zero families. These trajectories do not prove
that no other component exists.

The fixed-dimension all-copy problem also cannot be inferred by taking
finite-k intervals lambda<=gamma_k, because known gamma_k shrink like1/k.
The NPT threshold is1/d for a fixed physical d. Letting d grow with k
changes the state and fails the existential/universal quantifier order.
Nonstandard/hypercomplex existence likewise does not furnish the
required fixed standard finite-dimensional state. Recent PPT-operation
distillation theorems do not establish an LOCC theorem.

The all-copy proof still needs a positive-input switched-Schur mechanism
that survives entangled reference rays, a different global certificate,
or a full-domain distillation theorem. Certificate (S), arbitrary-copy
inference from finite searches, and the parity-compression proof are now
explicitly excluded routes; no corresponding false closure is claimed.
