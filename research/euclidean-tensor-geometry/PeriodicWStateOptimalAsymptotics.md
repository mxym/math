# Optimal asymptotic bond dimension for periodic translation-invariant W states

**Yongxian Zhang.** AI-assisted proof development and internal verification; no external peer review claimed.

Let \(d(n)\) be the least bond dimension of an exact, single-site translation-invariant periodic matrix product representation of the \(n\)-site \(W\) state over \(\mathbb C\). We prove
\[
\sqrt n\le d(n)\le \sqrt n+O(n^{1/4+o(1)}),\qquad
d(n)=(1+o(1))\sqrt n.
\]
The upper bound comes from the [explicit uniform construction](PeriodicWStateSquareRoot.md). The lower bound below is unrestricted: the matrices may be singular, non-diagonalizable, and genuinely complex. We determine the leading asymptotic constant, not the integer value for every \(n\).

[Klimov–Sengupta–Biamonte, §4, Problems 4–5](https://arxiv.org/html/2306.16456v2#S4) ask about the optimality and asymptotics in this trace model. Their \(\lfloor n/2\rfloor+1\) upper bound was already shown nonoptimal at \(n=7\) by [a formalized trureturing example](https://www.trureturing.org/research/klimov-2023-w-state-ti-mps-bond-dimension/), which also records an infinite square-root subsequence. [Cirac–Pérez-García–Schuch–Verstraete, Appendix A.1.3](https://arxiv.org/html/2011.12127#A1.SS1.SSS3) and [the MPS-under-permutations paper, Appendix E](https://arxiv.org/html/2410.19541v2#A5) discuss the previously known lower bound \(\Omega(n^{1/(3+\delta)})\) for every \(\delta>0\). This result concerns exact periodic representations, not border bond dimension, nor representations with a separate boundary tensor.

## Trace lower bound

Let \(A,B\in M_D(\mathbb C)\) and \(1\le k\le n\). Suppose all length-\(n\) words with more than \(k\) copies of \(B\) have zero trace, and all words with exactly \(k\) copies have nonzero trace. Then
\[
n\le kD^2.
\]
For \(k=1\), nonzero trace for all one-excitation words follows from cyclicity as soon as \(\operatorname{tr}(A^{n-1}B)\ne0\). For fixed \(k\), this also gives a square-root lower bound for the exact periodic Dicke state of weight \(k\); it does not give a matching construction for \(k>1\).

### Reachability with a saturated count

Take the Fitting decomposition \(W=P\oplus N\) for \(A\), with \(A_P\) invertible and \(A_N\) nilpotent. Let \(r=\dim P\), let \(s\) be the nilpotence index on \(N\) (zero if \(N=0\)), and let \(\pi:W\to P\) be the projection. If \(r=0\), then the required nonzero trace of \(A^{n-k}B^k\) gives \(n\le D+k-1\le kD^2\). Suppose \(r>0\). We will show \(n\le krD+s\), which is at most \(kD^2\).

Let \(U_t\) be the span, in \(k\) labeled copies of \(\operatorname{Hom}(W,P)\), of
\[
A_P^{-t}\pi M_w\otimes e_{\min(k,\#B(w))}
\]
for all length-\(t\) words \(w\) containing at least one \(B\). Here \(M_w\) is the ordinary matrix product and \(e_1,\ldots,e_k\) are formal labels. On these copies let
\[
T_A(X\otimes e_j)=A_P^{-1}XA\otimes e_j,\qquad
T_B(X\otimes e_j)=A_P^{-1}XB\otimes e_{\min(j+1,k)} .
\]
Prepending \(A\) leaves a normalized word unchanged, so \(U_t\subseteq U_{t+1}\). Appending a letter gives the recurrence
\[
U_{t+1}=T_AU_t+T_BU_t+
  \langle A_P^{-1}\pi B\otimes e_1\rangle.
\]
The last term comes from appending \(B\) to the all-\(A\) word, which is not included in \(U_t\). Any equality in the nested chain persists under the same recurrence. Since \(U_0=0\) and the ambient dimension is \(krD\), the chain has stabilized by \(t_*=krD\). Set \(U=U_{t_*}\).

Suppose for contradiction that \(n\ge krD+s+1\). Append \(B\) on the right of a length-\(t_*\) word from the last slot, then pad on the left with \(A^{n-t_*-1}\). The product has more than \(k\) copies of \(B\), so its trace is zero. The left padding kills the nilpotent block, so for the last slot \(U^{(k)}\) we obtain
\[
\phi(A_P^{-1}XB)=0\quad(X\in U^{(k)}),\qquad
\phi(Y)=\operatorname{tr}_P(A_P^n\, Y|_P).
\]

### Products on the invertible part

The projection \(E(X)=X|_P\circ\pi\), taken separately in each slot, is the Fitting projector for \(T_A\): on the right-\(P\) block \(T_A\) is invertible and on the right-\(N\) block it is nilpotent. Thus \(E\) is a polynomial in \(T_A\) and \(E(U)\subseteq U\). Identify the projected slots with spaces of \(r\)-by-\(r\) matrices. On them \(T_A\) is conjugation \(\sigma(X)=A_P^{-1}XA_P\); by stability and finite dimensionality its inverse preserves the same spaces.

Let \(B_{PP}=\pi B|_P\) and \(C=B_{PP}A_P^{-1}\). The operator \(T_A^{-1}ET_B\) on the projected space right-multiplies by \(C\) and increments the count, saturated at \(k\). The projected source followed by \(T_A^{-1}\) places \(C\) in slot 1. Conjugating these observations by powers of \(T_A\) allows every \(C_j=\sigma^j(C)\), \(j\in\mathbb Z\), as source or right multiplier. It follows that the last slot contains all products of at least \(k\) matrices \(C_j\). Also, for any \(X\) in the projected last slot,
\[
\phi(XC)=\phi(T_A^{-1}ET_B X)=\phi(T_B X)=0 .
\]
The middle equality uses that \(\phi\) depends only on the right-\(P\) block and is invariant under conjugation by \(A_P\). Since that slot is \(\sigma\)-invariant, it follows that \(\phi(XC_j)=0\) for all \(j\). Thus \(\phi\) kills all products of at least \(k+1\) conjugates.

### Radical and contradiction

Let \(\mathcal A\) be the unital finite-dimensional algebra generated by the \(C_j\), \(J\) the ideal spanned by its nonempty words, and \(R\) the Jacobson radical of \(\mathcal A\). The image of \(J\) in the semisimple algebra \(\mathcal A/R\) is an idempotent ideal, so \(J\subseteq J^{k+1}+R\). We just proved \(\phi(J^{k+1})=0\). The radical is invariant under \(\sigma\); for \(x\in R\), a sufficiently large power of \(A_P^n x\) equals a power of \(A_P\) times a product of equally many conjugates of \(x\), hence is zero by nilpotence of \(R\). Thus \(\operatorname{tr}_P(A_P^n x)=0\), and \(\phi(J)=0\).

Finally, \(rD\ge s+1\) implies \(n\ge k(s+1)\). Choose a cyclic word with exactly \(k\) copies of \(B\), each separated from the next by at least \(s\) copies of \(A\). Its trace can be computed entirely on \(P\), because every gap kills \(N\). On \(P\), normalization of a word of length \(t\) by \(A_P^{-t}\) changes it on appending \(A\) by \(X\mapsto\sigma(X)\), and on appending \(B_{PP}\) by \(X\mapsto\sigma(X)C\). Hence the normalized length-\(n\) product lies in \(J\), and the original trace is \(\phi\) of this product, zero. This contradicts the required nonzero trace.

This proves \(n\le krD+s\), and \(s\le D-r\) gives \(n\le kD^2\). In particular \(k=1\) gives the claimed sharp leading constant when combined with the upper construction.
