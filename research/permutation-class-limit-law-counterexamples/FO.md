# A proper permutation class without a first-order convergence law

**Theorem.** There are an infinite proper permutation class $D$ and a single fixed first-order sentence $\psi$ in the language of two linear orders such that, for $\sigma_n$ uniform in $D_n=D\cap S_n$,
$$\liminf_n\Pr(\sigma_n\models\psi)=0,\qquad \limsup_n\Pr(\sigma_n\models\psi)=1.$$
This answers Braunfeld and Kukla's published Question 5.4 negatively. We do not impose sum closure (their separate Question 5.3), a finite basis, or the existence of a proper exponential growth rate. The essential recently proved ingredient, a permutation class of oscillatory exponential speed, is due to Pantone and Vatter, not constructed anew here.

**Oscillatory input.** In the proof of Theorem 1.1 of Pantone and Vatter, *Permutation classes need not have proper growth rates*, arXiv:2610.30369v1, the family constructed with each permitted integer $w\ge4105$ satisfies
$$\liminf_n |C_n|^{1/n}\le 8(w+513)<9w\le\limsup_n |C_n|^{1/n}.$$
Their integer parameter counts increasing runs in the cell class in §3; take $w=4106$. The left bound is $L=36952$ and the right bound is $U=36954$. Only this strict gap is needed. Set $b=36953$, so $L<b<U$.

**An observable comparison class.** Let $B$ consist of permutations which are concatenations of $b$ consecutive increasing blocks, allowing empty blocks. This is a permutation class because taking a subsequence restricts each block. Equivalently a permutation has at most $b-1$ descents. The position and value orders are denoted by $<_p,<_v$. Put $\operatorname{succ}(x,y):=(x<_p y)\land\neg\exists z\ (x<_p z\land z<_p y)$. Take $\psi$ to be the negation of
$$\exists x_1,y_1,\ldots,x_b,y_b:\quad
x_1<_p\cdots<_p x_b\quad\land\quad
\bigwedge_{i=1}^{b}(\operatorname{succ}(x_i,y_i)\land y_i<_v x_i).$$
Only the left endpoints must be distinct; consecutive descents may share an endpoint. This is a fixed finite sentence, independent of $n$, and it defines exactly $B$.

This bounded-descent comparison family and its growth computation are classical, and are already used (with parameter $w$ instead of $b$) in Pantone–Vatter §§3–4. Color each value $1,\ldots,n$ by one of $b$ colors, list values of color $1$ in increasing order, then those of color $2$, and so on. The resulting map onto $B_n$ has fibers of size at most $\binom{n+b-1}{b-1}$: the vector of block lengths together with the output recovers all colors. Consequently
$$ b^n/\binom{n+b-1}{b-1}\le |B_n|\le b^n,\qquad |B_n|^{1/n}\longrightarrow b.$$

**Union, not disjoint union.** Set $D=C\cup B$. It is hereditary, has members of every length, and is proper: both summands have at most exponential speed (for $C$ this also follows from the Marcus–Tardos theorem), whereas $n!$ is superexponential. For uniform $\sigma_n$ one has
$$\Pr(\sigma_n\models\psi)=\frac{|B_n|}{|C_n\cup B_n|}.$$
Choose constants $L<\ell<b<u<U$. Infinitely many sizes satisfy $|C_n|\le\ell^n$; along them $1-\Pr(\psi)\le |C_n|/|B_n|\to0$ exponentially. Infinitely many sizes satisfy $|C_n|\ge u^n$; along them $\Pr(\psi)\le |B_n|/|C_n|\to0$ exponentially. No disjointness, and no knowledge of how many members lie in both classes, is required. This proves the theorem.

In fact $D$ is not finitely based. In Pantone–Vatter's notation, $Q\subset C$, and their Proposition 6.4 forces every finitely based superclass of $Q$ to have lower growth at least $9w=U$. But the lower growth of $D$ is exactly $b<U$ by the two-sided cardinality bounds above. No conclusion about finitely based classes follows.
