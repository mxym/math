# Which power symmetric moduli induce norms for all symmetric norms?

For a finite real p≥1, a complex n-by-n matrix X, and a unitarily invariant matrix norm N, define S_p(X)=((|X|^p+|X*|^p)/2)^(1/p) and F(X)=N(S_p(X)), where |X|=(X*X)^(1/2). Conjecture 8.7 of Bourin–Zhang [arXiv:2610.30538](https://arxiv.org/html/2610.30538v1#S8) proposes that F is a weakly unitarily invariant norm for every N. Weak invariance means invariance under unitary conjugation, not separate left and right unitaries. Positivity, absolute scalar homogeneity and conjugation invariance are automatic for all these p. The triangle inequality is not.

**Theorem.** For finite p≥1, F is a norm for every dimension and symmetric norm if and only if p=2. The positive case is already Bourin–Zhang, Corollary 6.5. For every p≠2 the operator norm N gives a midpoint convexity failure on real 4-by-4 matrices, and hence on every matrix size n≥4 by adjoining a common zero block. This does not classify every N at a fixed p or all smaller dimensions. Only the universal Conjecture 8.7 is addressed, not the optimal constants in Problem 8.6.

**A small closed counterexample (p=1).** For real symmetric 2-by-2 A,B put X(A,B)=[[0,A],[B,0]] in block notation. The two diagonal blocks of |X|^p+|X*|^p both equal |A|^p+|B|^p, so
     
     F(X(A,B))=2^(−1/p) λ_max(|A|^p+|B|^p)^(1/p)                 (1)

for N the operator norm. Choose B=diag(0,21) and

     A_+ = [[8,4],[4,2]],      A_- = [[-8,4],[4,-2]].

A_+ is positive and A_- negative semidefinite. The matrices |A_±|+B have diagonal (8,23) and off-diagonal ±4, hence trace 31, determinant 168 and eigenvalues 24,7. The midpoint M=(A_++A_-)/2=[[0,4],[4,0]] has |M|=4I. Thus the two F-values are both 12, while F at the midpoint is 25/2. This is a violation of the norm triangle inequality by absolute homogeneity.

**Isolating an entry of the matrix power.** Let e=(0,1)^T and P=ee*. For any fixed 2-by-2 positive semidefinite C, write its entries in this basis as [[u,z],[z*,v]]. For t→∞,
     
     λ_max(tP+C)=t+v+O_C(1/t).

Indeed the larger eigenvalue is (t+u+v+sqrt((t+v−u)^2+4|z|²))/2, and subtracting t+v and rationalizing gives the bound. For fixed p>0 this implies
     
     λ_max(tP+C)^(1/p)=t^(1/p)+(v/p)t^(1/p−1)+O_(C,p)(t^(1/p−2)).

In (1) fix B=t^(1/p)P. For two fixed symmetric matrices A_1,A_2 and their midpoint M, the top comparison as t→∞ therefore tests the scalar midpoint inequality
     
     e*|M|^p e ≤ [e*|A_1|^p e + e*|A_2|^p e]/2.                (2)

More precisely, if (2) fails with a strictly positive gap, then by (1) and the expansion, convexity of F fails for every sufficiently large finite t. Scaling by the positive quantity p·2^(1/p)·t^(1−1/p) makes the difference converge to that gap. No single t is required to work for all p.

**Failure for every 1≤p<2.** Pick 0<s<1 and put c=sqrt(1−s²). Set unit vectors u_+=(c,s)^T, u_-=(c,−s)^T and A_1=u_+u_+*, A_2=−u_-u_-*. Their absolute powers are the respective projections, so the right side of (2) is s². Their midpoint has off-diagonal cs and diagonal zero, hence the left side is (cs)^p. As s decreases to zero the ratio c^p s^(p−2) tends to infinity. Choose any sufficiently small positive s to violate (2).

**Failure for every 2<p<∞.** Take T>1,
     
     A_1 = diag(T−1/T,0),       A_2 = [[0,1],[1,0]].

The right side of (2) is 1/2. The matrix A_1+A_2 has eigenvalue T with unit eigenvector (T,1)^T/sqrt(T²+1). Consequently e*|M|^p e ≥ (T/2)^p/(T²+1), which tends to infinity for p>2. Choose a sufficiently large finite T, then use the isolating argument.

**The known positive exponent.** At p=2, S_2(X) is the ordinary modulus of the rectangular real-linear stack G(X)=[X;X*]/sqrt(2). Applying the same symmetric gauge N to its n singular values defines a rectangular unitarily invariant norm. The stack is additive, giving the triangle inequality. The other norm axioms and conjugation invariance were noted above. Equivalently this is the already proved Corollary 6.5 in the source, not an additional original assertion.
