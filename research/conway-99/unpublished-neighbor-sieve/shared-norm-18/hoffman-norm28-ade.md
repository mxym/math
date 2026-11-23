# An ADE classification of the true norm-28 fields in one ternary class

Fix an actual Hoffman coclique C compatible with a maximal original seven-extension H. Count *oriented* neutral graph fields t of squared norm 28, vanishing at every point of C, eligible for H. On the rank-42 two-type face H is the original seven lattice; these are actual original-zero fields. A zero *total evaluation* on C is not the same as vanishing on C, and the bound below concerns only the latter. No symmetry or assumption that t is unit is needed.

Use the unsaturated ternary lattice L from [the rank-22 residual construction](hoffman-residual-theta.md): m_b for b outside C have norm 6, integral Gram Q, and x in L* represents t=( (x,m_b) ) with t²=21x². At seven the compatible summand has a residual anisotropic plane; since x²=4/3 is integral at seven, each x actually lies in its **primal** lattice at that prime. At three keep the original class alpha=x+L_3, not the class after an additional ternary saturation. Write k=dim ker(D^t mod 3).

For any single alpha, the class of fields is either empty, a simplex of at most 20 points, or one of the following entire finite configurations. The number given is the number of fields in the **one** class, not including the opposite class:

* three A1 components: 3 fields;
* D_n and A1, n≥3 (with D3=A3): 2n-1 fields;
* A5: 9 fields; D6: 15 fields; E7: 27 fields.

In the second alternative n≤22-2k, and in fact n≤21-2k if k=1 or 2. Accordingly the numbers of fields vanishing on C, after summing all admissible classes, are at most **0, 222, 2376** for k=0,1,2 respectively. By the [independent ternary kernel theorem](hoffman-ternary-rank-three.md) a true Hoffman design has k≤2. The rank-42 minimum total population of N28 applies to all fields, not just this subpopulation; these upper bounds alone do not contradict it.

## Pairings and completion

Use f=t/sqrt(7) in the ordinary real graph coordinate space, so |f|²=4. Distinct fields in one ternary class have integral pairings in this scaling: at seven both corresponding x lie in the primal lattice, and in graph coordinates the only possible denominator is seven. Their differences x-x' belong to L_3. It follows from |x-x'|²=(8-2(f,f'))/3 that (f,f')≡1 mod3. The class is nonzero at three since x²=4/3. Thus an opposite field is not in the same class; Cauchy and the integrality/congruence give only inner products 1 and -2.

If (f,g)=-2, then -f-g has norm four and is the normalization of an actual field vanishing on C, with the same seven eligibility and ternary class (-2alpha=alpha). If no such pair occurs the Gram is 3I+J and the number m of fields is at most 22 by real dimension. At seven the compatible residual has Gram rank 20 since its determinant is 49 with elementary discriminant. In dimension m=21 or 22 the determinant of (3I+J)/3 is a seven-unit, ruling out either value. Hence m≤20.

Otherwise lift every f to w_f=(f,sqrt(2))/sqrt(3) in one extra real dimension. The w_f have norm two and pairwise inner products 0 or 1. Their integer span is a positive definite integral even root lattice: a finite subset forms a real basis, and the integral Gram pairings place the whole span inside its dual, so it is discrete. Let lambda have only last coordinate sqrt(3/2). Every marked root has height (lambda,w)=1. Conversely **every** root of height one in this root lattice is marked: its expression as an integer sum of w_f has coefficient sum one, so the recovered graph projection is an integral combination of original t of total coefficient one, remains in alpha and H, vanishes on C, and has the required norm. An orthogonal pair w_f,w_g has third member w_(-f-g); their sum is 2lambda. Thus lambda is in the real span and 2lambda in the root lattice. Its norm is 3/2. Every root has integral lambda-pairing of magnitude at most sqrt(3)<2, hence each component of the weight is minuscule after choosing a Weyl chamber. No component can have height identically zero, since the marked roots generate.

For completeness, the standard simply-laced minuscule weights with twice the weight in the root lattice and squared norm ≤3/2 give the full list. In A_l, omega_a has norm a(l+1-a)/(l+1) and twice its class is zero only for 2a=l+1, giving A1, A3, A5 of norms 1/2,1,3/2. In D_l the vector weight has norm one; a permissible spin weight has l even and norm l/4, giving only D4 (triality-equivalent) or D6. In the exceptional types, E6's two minuscule classes have order three, E7's unique one has norm 3/2 and order two, and E8 has none. Norms across components add to 3/2, yielding exactly the listed products. The number of height-one roots is 1 in A1, 2(n-1) for D_n's vector weight, 3·3=9 in A5, binom(6,2)=15 in D6, and (126-72)/2=27 for E7 (perpendicular roots E6).

## The actual vertex evaluations exclude the endpoint D-frame

In D_n plus A1 take the central f corresponding to the A1 root. The other 2(n-1) f's come in m=n-1 pairs g_i,h_i with g_i+h_i=-f. In the standard D_n realization these pairs correspond to the height-one roots e_1+e_j,e_1-e_j for j=2,...,n. Their differences are orthogonal to one another and to f. In original graph coordinates, put d_i=t_(g_i)-t_(h_i); these have squared norm 84 and d_i≡t_f mod2 entrywise. The corresponding rank-22 vectors x_(g_i)-x_(h_i) give an orthogonal frame of norm four inside L_3 because the two lifts have the same ternary class. The original ternary rank of L is 21-2k, hence m≤21-2k. At seven these vectors together with x_f are an orthogonal unit system in the rank-20 nondegenerate part of the compatible residual, giving n≤20 as well.

If k=1 or 2 and m=21-2k, those norm-four vectors form a basis of the nondegenerate ternary quotient. For any outside block site b, the mark m_b of norm six therefore gives

    24 - sum_i d_i(b)^2 = 0 mod 3.

Choose b with t_f(b) odd: otherwise division of the integral field by two would give an integral neutral field with odd squared norm seven, impossible since its coordinate sum is zero. Every d_i(b) is odd. Real orthogonal projection onto x_f of norm 4/3 and the orthogonal norm-four vectors gives

    3t_f(b)^2 + sum_i d_i(b)^2 ≤ 4|m_b|²=24.

For m=19 or 17, this forces |t_f(b)|=1 and |d_i(b)|=1 for every i: a single absolute value three already adds eight. But 24-m=3+2k is not zero modulo three. This excludes the endpoint. In particular the largest possible one-class populations for k=1,2 are 37 and 33, not 43.

Finally q(alpha)=x²/2=2/3. The ternary discriminant is the sum of k hyperbolic planes and a line of q-value 1/3, by the rank-22 construction. There are 3^(2k)-3^k such alpha (add hyperbolic planes to the one-dimensional count, or count the three values of uv explicitly). This gives 0,6,72 classes. Fields and their negatives occur in opposite classes and are counted once each.
