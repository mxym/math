# Sum-of-squares obstruction for local encodings of dense negacyclic equations

A full ring equation gives a correlated orbit of scalar equations, not independent scalar rows. Earlier sum-of-squares arguments for this setting assumed sparse coefficients, and substituting the dense partial sums into a low-degree functional gives no growing local-gate lower bound. Here we work directly in the expanded variable space. Tracking only the provenance of terminal pins gives a growing-degree obstruction even for uniformly dense ring coefficients.

## 1. Setting and result

Fix any integer \(q\ge2\) and \(A>0\). In \(R=(\mathbb Z/q)[X]/(X^d+1)\), take \(1\le k\le d^A\) independent uniform rows \(A_i\). The unknown coefficient vector is \(s\in(\mathbb Z/q)^d\). The design supplies all \(kd\) scalar equations from \(A_i s=B_i\). Denote their row vectors by \(a_r\) and right-hand sides by \(b_r\), with \(r=(i,j)\) ranging over the designs and shifts.

Encode each scalar equation by its own binary tree of partial additions, with a scaled leaf for each of the \(d\) coordinates (including those whose public multiplier happens to be zero). Each leaf is a variable constrained to equal \((a_r)_u s_u\), and each internal variable equals the sum of its two children. Distinct trees do not share auxiliary variables, though their leaves use the same original coordinate variables \(s_u\). The trees are fixed independently of the sampled \(A_i\); their shape can otherwise be arbitrary. The output of the root is compared to \(b_r\). Use the ordinary one-hot encoding of each variable over \(\mathbb Z/q\), enforce the local gate equations exactly, and maximize the fraction of root terminals that agree.

There is a constant \(c>0\) depending only on \(q,A\), such that, except with probability \(\exp[-\Omega_{q,A}(\sqrt{d\log d})]\) over the design, **simultaneously for all right-hand sides**, the degree-\(\lfloor c\sqrt{d/\log d}\rfloor\) sum-of-squares relaxation has value 1. In fact its pseudoexpectation can satisfy every gate and every terminal pin at the allowed multiplier degrees.

For independent uniform \(B_i\), the actual optimal agreement, conditional on every design, is at most
\[
               \frac1q+\sqrt{\frac{\log q+1}{2k}}
\]
with probability at least \(1-e^{-d}\). For sufficiently large fixed \(k\) this gives a constant gap, and if \(k\to\infty\) the gap tends to \(1-1/q\). The proof only uses the negacyclic permutation rule, so the statement holds in particular at dyadic dimensions and does not require \(q\) to be prime. This is a lower bound for a specified local sum-of-squares formulation. It does not cover other encodings (e.g. shared arithmetic transforms across multiple roots), unrestricted running time, a continuous likelihood objective, or any deployment.

## 2. A short-support cancellation property in the expanded space

Let \(\mathcal V\) be the original coordinates and all auxiliary variables, with \(|\mathcal V|=O(kd^2)\). Write \(\pi:(\mathbb Z/q)^{\mathcal V}\to(\mathbb Z/q)^d\) for the linear map substituting each auxiliary variable by the coefficient vector of its actual partial linear form in \(s\). For the tree of scalar equation \(r\), any variable in the tree projects to \(a_r\) restricted to a fixed leaf subset, its descendants. In particular the root projects to \(a_r\), and every exact local gate relation projects to zero. An original coordinate projects to its standard basis vector. The map \(\pi\) depends on the design but its masks are fixed in advance.

For a positive integer \(L\), fix any nonzero terminal coefficient vector \(c=(c_r)\) supported on at most \(2L\) terminal indices, and any \(v\in(\mathbb Z/q)^{\mathcal V}\) of support at most \(w\le L/2\). Call a selected root *unrepresented* if \(c_r\ne0\) but no auxiliary variable of that root's tree belongs to the support of \(v\). We bound the event
\[
                 \pi(v)=\sum_r c_r a_r                              \tag{1}
\]
whenever there is an unrepresented root. This is not a restriction on how \(v\) might ultimately be chosen from the sampled design: we will union-bound all fixed pairs \((c,v)\).

For coefficient index \(j\), the difference in (1) at that output index is a linear function of the independent uniform input coefficients \(A_{i,u}\). The scalar row vector at shift \(r=(i,h)\) is \(a_r=X^h\overline{A_i}\) under the coefficient pairing, since multiplication by \(X\) is a signed permutation with transpose \(X^{-1}\). Distinct shifts within the same ring row therefore read distinct underlying coefficients at any fixed output coordinate. In particular, the unrepresented root contributes an uncanceled term with nonzero scalar \(\pm c_r\) at every \(j\); another root in the same ring row reads a different input coordinate, its own tree is absent from \(v\), and base variables contribute only deterministic constants. Conditional on all the other input coefficients at this \(j\), the probability for that coordinate of (1) is at most \(1/2\): multiplying a uniform element of \(\mathbb Z/q\) by a nonzero element has uniform image on a group of size at least two. This avoids a field-invertibility assumption.

Across output coordinates, one underlying \(A_{i,u}\) can occur at most \(\mathrm{wt}(c)+\mathrm{wt}(v)\le 2L+w\) times. In each individual shifted row or its masked restriction, it occurs in at most one output coordinate, and original variables add at most deterministic terms. Thus the \(d\) coordinate-equality indicators form a read-\((2L+w)\) family. The generalized Hölder bound for read families (as in [Gavinsky–Lovett–Saks–Srinivasan](https://arxiv.org/abs/1205.1478)) gives
\[
      \Pr[(1)]\le 2^{-d/(2L+w)}.                                  \tag{2}
\]
To see the form used here, iteratively integrate independent input entries, applying Hölder with exponent \(2L+w\) to the factors that read that entry, padding the inequality with factors 1 if needed. After all integrations the joint expectation of the product of indicators is at most the product of their marginal probabilities to the power \(1/(2L+w)\). No independence between output coordinates is assumed.

The number of possible pairs \((c,v)\) in this range is at most
\[
       (qkd+1)^{2L+1}(q|\mathcal V|+1)^{w+1}
                  =\exp(O_{q,A}(L\log d)).
\]
Take \(L=\lfloor\epsilon\sqrt{d/\log d}\rfloor\), \(w=\lfloor L/2\rfloor\), with \(\epsilon>0\) sufficiently small. The union bound in (2) is then \(\exp[-\Omega_{q,A}(\sqrt{d\log d})]\). Hence on one good event, (1) is impossible for all these pairs whenever at least one selected root is unrepresented.

## 3. Terminal provenance rules out a narrow contradiction

Treat the gates and the terminal pins as affine equations over \(\mathbb Z/q\) in the variables \(\mathcal V\). Their coefficient widths are at most three. Consider the width-\(w\) closure \(\mathcal D_w\) generated by them and the identity \(0=0\), with scalar multiplication and addition allowed when the resulting coefficient vector has support at most \(w\). Attach to each derived pair \((v,b)\) the provenance vector \(c\) of just the terminal pins. A terminal pin starts with the corresponding unit coefficient, a gate starts with zero provenance, and the vector scales and adds under derivation. By construction
\[
                   \pi(v)=\sum_r c_r a_r,\qquad b=\sum_r c_r b_r . \tag{3}
\]
There is no need for provenance to be unique: attach one to every derivation, and the good event of §2 rules out the relevant pairs for all choices.

If a contradiction \((0,b\ne0)\) had terminal provenance of support \(\le2L\), then it would have at least one selected root by (3), all roots would be unrepresented in \(v=0\), and §2 would forbid the projected identity. If the contradiction's provenance is larger, some first derivation step has terminal support at least \(L\); it has at most \(2L\) because an addition uses at most twice the larger parent support and multiplication cannot increase support. At that step its coefficient vector still has width at most \(w<L\), so auxiliary variables of \(v\) can represent at most \(w\) distinct trees. Some selected root is unrepresented, again contradicting §2. Thus \(\mathcal D_w\) contains no contradiction, regardless of right-hand sides.

## 4. Character pseudoexpectation in the expanded variables

For completeness, let \(\omega=e^{2\pi i/q}\), and on the character \(\chi_v(z)=\omega^{v\cdot z}\) of support at most \(w\) define expectation to be \(\omega^b\) if \((v,b)\in\mathcal D_w\), and 0 otherwise. The absence of contradictions makes \(b\) unique whenever the equation is derivable, since subtracting two equations with identical \(v\) has width zero. The functional is normalized by \(0=0\), and conjugation agrees with negation. This standard width-to-character construction was also used in [our sparse orbit theorem, §4](https://github.com/mxym/math/blob/05a6d07a3508af481e30330222ec347ec1e2537b/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-random-sparse-orbit-sos.md#4-explicit-prime-field-pseudoexpectation); the novel step here was proving consistency directly on the expanded space.

For characters of support at most \(\lfloor w/2\rfloor\), indices \(u,v\) are equivalent if \(v-u\) is derivable. This is an equivalence relation since the result of adding two relevant equations has width at most \(w\). Between classes the Gram entries vanish, and on a class the entry for \(u,v\) is \(\omega^{b_v-b_u}\) using right-hand sides relative to a representative. Each block is rank-one positive semidefinite. Hence the functional is nonnegative on squares of polynomials of degree at most \(\lfloor w/2\rfloor\) after substituting each one-hot variable by its exact character expansion. A degree-\(w\) polynomial has only characters of support at most \(w\). All one-hot equalities hold under this substitution as identities.

For any gate or terminal equation \((a,b)\) of arity at most three, the equality \(\widetilde E \chi_{v+ca}=\omega^{cb}\widetilde E\chi_v\) holds whenever both sides have width \(\le w\), by closure under adding or subtracting the scaled equation. Averaging over \(c\in\mathbb Z/q\) gives satisfaction of the equation's one-hot indicator against every multiplier allowed by total degree. This argument uses only additive characters and works over composite \(q\), too. Thus the objective attains 1. It cannot exceed 1 since each terminal's satisfaction indicator is a single one-hot bit, whose pseudoexpectation is at most 1 by positivity and the one-hot sum.

In a genuine assignment satisfying the gate constraints, every root is its actual linear form in \(s\), so the objective equals ordinary equation agreement. Conditional on the design and a fixed \(s\), its \(kd\) agreements against independent uniform \(B_i\) are independent Bernoulli \(1/q\), because the coefficient coordinates of uniform \(B_i\) are independent. Hoeffding followed by a union over \(q^d\) choices of \(s\) proves the claimed bound on the true optimum. The simultaneous statement for arbitrary \(b_r\) refers only to the pseudoexpectation, not to the true optimum.

## 5. The encoding restriction is substantive

For contrast, over a prime field and for unit rows, consider a different arithmetic encoding of the **same** exact equations. Represent each invertible coefficient matrix as a sequence of elementary invertible wire updates: add a multiple of one wire to another, rescale one wire nontrivially, or exchange two wires. Retain each stage's wires in the encoding, and identify unchanged wires across a step. Such a factorization exists by ordinary elementary row operations, and each gate relation has arity at most three. If two rows prescribe different original vectors upon inversion, then in this encoding the degree-six relaxation cannot have value 1.

Indeed a degree-six feasible pseudoexpectation gives a genuine local probability distribution on every triple of field variables: each three-variable assignment indicator is nonnegative in expectation by the one-hot idempotence identity and square positivity, and the resulting probabilities sum to one and have the given marginals. Value 1 would force all terminal output pins in these marginals. For a shear update the pinned new wire and the unchanged other wire uniquely determine the old wire in the local gate relation; a scaling or exchange is even simpler. Hence the pins propagate backward all the way to the original coordinates by induction on the stages. If two rows force different original pins, the single-coordinate marginal cannot satisfy both, proving the claim. This is only a statement about refuting exact full agreement, not a quantitative bound at constant degree on the optimal fraction. It illustrates why permitting a different variable encoding or a shared transform is not a free extension of the theorem.

## 6. Prior and scope

[Schoenebeck](https://schoeneb.people.si.umich.edu/papers/LasserreNew.pdf) and subsequent width arguments give local sum-of-squares gaps for random sparse constraints; [the semirandom linear-systems theorem](https://arxiv.org/abs/2609.30052) is a close model for width/provenance reasoning. The earlier sparse ring-orbit proof uses the width of partially combined sparse coefficient rows, then pulls back local gates; this costs a factor proportional to the maximal original row weight. The present terminal-only provenance does not make that substitution at the pseudoexpectation stage. It proves an obstruction for **uniformly dense** independent ring rows in a precise local encoding, despite the dependencies among all their scalar shifts. It gives no implication for other possible circuit encodings or unrestricted algorithms, including ordinary Ring-LWE inference.
