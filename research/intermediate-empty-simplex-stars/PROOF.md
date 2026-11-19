# Intermediate-dimensional stars of empty simplices

Let \(K\) be a fixed compact convex body with nonempty interior in \(\mathbb R^d\), and let \(X_n\) consist of \(n\) independent uniform points of \(K\). A \(d\)-simplex with vertices in \(X_n\) is empty if no further sample point lies in its interior. For each \(k\)-subset of sample points count the empty simplices containing it among their vertices; let \(D_k(X_n)\) be the **maximum** such count over the \(k\)-subsets. The uniform sample is in general position almost surely.

**Theorem.** For \(2\le k\le d-1\), set \(c=d-k+2\). There is \(C=C(K,d,k)>0\) such that for all sufficiently large \(n\),
\[
 E D_k(X_n)\ \ge\ C n^{d-k+\min(1,k/c)}.
 \tag{1}
\]
In particular the \(O(n^{d-k})\) assertion of Reitzner–Temesvari, [*Stars of Empty Simplices*, Conjecture 1.6 in arXiv:1808.08734v2](https://arxiv.org/pdf/1808.08734v2), fails for **every** intermediate \(k\) and every such body. If \(2k\ge d+2\), the trivial completion bound \(D_k\le {n-k\choose d+1-k}\) shows the order is exactly \(\Theta(n^{d+1-k})\). We assert only the lower bound when \(2k<d+2\); neither endpoint \(k=1\) nor \(k=d\) is a counterexample here.

## A rare well-conditioned flat base

Scale so \(|K|=1\), fix a closed ball \(B\subset\operatorname{int}K\) of positive radius, and let \(B'\) be its concentric half-radius ball. For sufficiently small fixed \(a>0\), call a \(k\)-tuple a candidate at scale \(h>0\) if its points are in \(B'\), its \((k-1)\)-simplex has volume at most \(h\), and **every** one of its \((k-2)\)-faces has \((k-2)\)-volume at least \(a\). A zero-dimensional face has volume one; for \(k=2\) the condition is just a close pair in \(B'\) if \(a\le1\).

There are positive constants \(c_0,C_0,h_0\), independent of \(n\), with the following estimates for \(0<h\le h_0\):

- Given **any** \(k-1\) fixed points, the probability that one additional independent point completes a candidate is at most \(C_0 h^c\). If the fixed face fails the lower bound the chance is zero. Otherwise the new point must lie within distance \((k-1)h/a\) of its \((k-2)\)-dimensional affine hull by the base-height formula. The volume of this tube inside the bounded ball \(B'\) is at most a constant times \(h^{d-k+2}\), by orthogonal coordinates. The conditional bound applies whichever vertex is left free.
- For \(k\) iid points, the probability of a candidate is at least \(c_0 h^c\). Choose \(k-1\) affinely independent model points in a small ball strictly inside \(B'\). Complete them in their own affine span by their barycenter. All \((k-2)\)-faces of this degenerate model tuple have positive \((k-2)\)-volume, as each barycentric coordinate of the added point in the original face is positive. Choose \(a\) below the minimum, and constrain the first \(k-1\) sampled points to sufficiently small fixed balls about the model points, an event of fixed positive probability. In the affine span of these actual points take a fixed-radius \((k-2)\)-ball around their barycenter, and add an orthogonal \(c\)-ball of radius \(b h\). For small enough fixed radii and \(b>0\) the entire product lies in \(B'\), preserves all face lower bounds by continuity, and gives full simplex volume at most \(h\) by base-height and boundedness. Its volume is a positive constant times \(h^c\). For \(k=2\) this is the ordinary \(d\)-ball of radius \(b h\) about the first point. Full-dimensionality within the \((k-1)\)-simplex holds almost surely.

## Marking one base without biasing the remaining points

Split the **labels**, in advance, into pools of sizes \(\lfloor n/2\rfloor\) and \(n-\lfloor n/2\rfloor\). Consider candidate bases only among \(k\)-subsets of the first pool. Set
\[
 h=\delta n^{-k/c},\qquad t=\min(1,(nh)^{-1})
\]
with \(\delta>0\) so small that \(C_0\delta^c\le1/4\). In a configuration with exactly one first-pool candidate, count the empty simplices consisting of it plus \(d+1-k\) second-pool labels. On all other configurations put the count equal to zero. Pointwise it is at most \(D_k(X_n)\): we have counted only completions of one base. We lower-bound its expectation by summing indicators over a designated first-pool \(k\)-subset \(S\) and a designated second-pool \((d+1-k)\)-subset \(Q\).

First expose \(S\); its chance of being a candidate is at least \(c_0h^c\). Order the labels of \(Q\) by their indices and expose all but the last. The resulting \(d\) points span a hyperplane almost surely and the \((d-1)\)-volume of their simplex is at most \(C_1 h\). Indeed start with the candidate face and append \(d-k\) points, multiplying the previous volume at each stage by a height at most \(\operatorname{diam}K\) divided by the new dimension. The hyperplane goes through a vertex of \(S\) in \(B'\). Intersect the ball of radius half the radius of \(B\) about that vertex with a slab of half-width \(b' t\) about the hyperplane. Its \(d\)-volume is at least \(c_1 t\), uniformly in the hyperplane, for sufficiently small fixed \(b'>0\): it contains a product of a fixed \((d-1)\)-ball and an interval of that order. It lies in \(B\). When the last point lands there, the \(d\)-simplex spanned by \(S\cup Q\) has volume at most \(C_1h b't/d\le1/(4n)\), choosing \(b'\) small enough.

Now condition on **all** these \(d+1\) positions, with \(S\) a candidate and the completed simplex of volume at most \(1/(4n)\). Other labels still have the original iid uniform law. The probability that any of them lies inside this simplex is at most \(1/4\) by a union bound. Also the conditional probability of any *different* first-pool candidate is at most \(n^k C_0 h^c\le1/4\): each competing \(S'\ne S\) has a label outside \(S\), necessarily outside \(Q\) as well, since \(Q\) uses the second pool. Expose the other labels of \(S'\), then use the one-free-vertex upper bound on the remaining fresh label. This argument allows arbitrary overlap between \(S'\) and \(S\) and does not presume independence of rival candidates. By another union bound, with conditional probability at least \(1/2\) both the desired emptiness and uniqueness hold.

Consequently each choice of \(S,Q\) contributes at least \(c_2 h^c t\) in expectation. There are \({\lfloor n/2\rfloor\choose k}{n-\lfloor n/2\rfloor\choose d+1-k}=\Theta(n^{d+1})\) choices, and each completion counted for the unique base is a distinct unordered simplex. Their total lower bound has order
\[
 n^{d+1} h^c\min(1,(nh)^{-1})
 =\Theta\big(n^{d-k+\min(1,k/c)}\big),
\]
as claimed.
