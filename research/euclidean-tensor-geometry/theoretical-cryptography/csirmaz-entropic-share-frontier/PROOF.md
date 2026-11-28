# The exact distinguished-share region with entropic defects

## 1. Model and theorem

For \(k\ge1\), let \(A\) be a set of \(k\) distinguished participants. Enumerate its subsets \(A_0,\ldots,A_{2^k-1}\) so a strict superset always precedes a strict subset. Thus \(A_0=A\) and \(A_{2^k-1}=\varnothing\). Let \(B_i=\{b_1,\ldots,b_i\}\) for \(0\le i\le 2^k-2\); the tail participants are disjoint from \(A\). The Csirmaz access structure \(\Gamma\) is the upward closure of \(A_i\cup B_i\) for \(i=0,\ldots,2^k-2\). All other coalitions are forbidden. For \(k=1\) this is the single qualified participant and there is no tail. For \(k\ge2\), every qualified coalition either includes all of \(A\) or includes \(b_1\), as follows immediately from the generating sets.

Let \(S,(X_i)_i\) be finite jointly distributed variables with \(H(S)>0\); \(X_U\) denotes the joint share of a set. For fixed \(0\le\eta,\delta\le1\) require, respectively,
\[
 I(S;X_U)\le\eta H(S)\quad(U\ {\rm forbidden}),\qquad
 H(S\mid X_Q)\le\delta H(S)\quad(Q\ {\rm qualified}).
 \tag{1}
\]
This is Kaced's normalized entropic model (Definition 2.2). It concerns entropy on the given distribution, not statistical distance or maximal decoding error probability. At \(\delta=0\), qualified reconstruction has zero error on the support.

Write \(a=(1-\eta-\delta)_+\), \(r=1-\delta\), \(t=2^k-1\), and \(x_i=H(X_i)/H(S)\) for \(i\in A\). Abbreviate \(x(D)=\sum_{i\in D}x_i\). The results are as follows.

1. For every \(k\), all schemes obey
   \[
   H(X_J\mid X_{A\setminus J})/H(S)\ge a(2^{|J|}-1),\qquad
   x(A)\ge r,\qquad
   x(A_i)+x(A)\ge r+(t-i)a\quad(0\le i<t).
   \tag{2}
   \]
   At the perfect caps, the first family already gives the full closed projection: it is the convex hull of the permutations of \((1,2,\ldots,2^{k-1})\) plus the nonnegative orthant.
2. If \(k=2\), write \(u\) for the singleton \(A_1\) and \(v\) for \(A_2\). The closed projection at **all** caps is exactly
   \[
   x_u,x_v\ge a,\qquad x_u+x_v\ge\max\{3a,r\},\qquad
   2x_u+x_v\ge r+2a.
   \tag{3}
   \]
   Every rational feasible vector at rational caps is attained by a linear scheme over any prescribed finite field. The last inequality can be essential: at \((\delta,\eta)=(0,2/3)\), \((x_u,x_v)=(1/3,2/3)\) satisfies the symmetric subset and total bounds but is infeasible, even in the closure.
3. For every \(k\ge1\), at the critical caps
   \[
   r>0,\qquad \eta=r(1-1/t)
   \tag{4}
   \]
   the infimum of \(x(A)\) equals \(r\) if and only if the order is a binary-weight order: for some bijection \(\pi:A\to\{0,\ldots,k-1\}\),
   \[
   \iota(D)=\sum_{j\in A\setminus D}2^{\pi(j)} \qquad(D\subseteq A).
   \tag{5}
   \]
   In this case the only projected vector with total \(r\) in the closure is \(x_j=(r/t)2^{\pi(j)}\). For rational caps it is attained linearly over any prescribed finite field after a possible extension. In every other order the infimum total is strictly bigger than \(r\).

These are projections on \(A\); no upper limits are imposed on the tail shares. The theorem does not optimize the full convec region or resolve the reverse-substitution factors.

## 2. Restricting a Csirmaz chain

A coalition with distinguished part \(D\subseteq A\) and some tail participants is qualified exactly when \(D\ne\varnothing\) and it contains the tail prefix \(B_{\iota(D)}\), where \(\iota(D)\) is the index of \(D\) itself. Indeed, among indices \(i\) with \(A_i\subseteq D\), the first is \(\iota(D)\). If \(D=\varnothing\) there is no generating set with such distinguished part.

Fix nonempty \(J\subseteq A\), put \(F=A\setminus J\), and take all nonempty subsets of \(J\) in the order \(D_0,\ldots,D_M\) of their indices \(i_j=\iota(F\cup D_j)\), where \(M=2^{|J|}-2\). Then \(D_0=J,\ i_0=0\), and \(i_M<\iota(F)\) because \(F\cup D_j\) is always a strict superset of \(F\). This also applies when \(F\) is empty, with its formal last index. Use
\[
 P_j=F\cup B_{i_j},\qquad Z_j=P_j\cup J \quad(0\le j\le M).
\]
Each \(P_j\) is forbidden: its distinguished part is \(F\), but its prefix stops too early, or \(F=\varnothing\). Each \(Z_j\) is qualified because it contains \(A\). For \(j<M\), define
\[
 Y_j=P_{j+1}\cup D_{j+1},\qquad E_j=P_j\cup D_{j+1}.
\]
Then \(Y_j\) is qualified at its prefix \(i_{j+1}\), and \(E_j\) is forbidden at the shorter prefix \(i_j\). We also have \(Z_j\cap Y_j=E_j\) and \(Z_j\cup Y_j=Z_{j+1}\).

Equivalently, contract the forbidden set \(F\), group each consecutive block \(B_{i_j}\setminus B_{i_{j-1}}\) into one participant, and discard tail shares beyond \(B_{i_M}\). The resulting access structure on \(J\) and the grouped blocks is exactly the Csirmaz structure of size \(|J|\): a prefix through its \(j\)-th block is available precisely when all the first \(j\) such participants are in the coalition. A single tail omission prevents a longer original prefix. We work with \(Z_j,Y_j,E_j\) directly, so the same proof applies to (1) without any assertion that conditional slices meet the same error caps.

## 3. Converse: the telescoping conditional entropy inequality

For any two coalitions \(Z,Y\) with \(E=Z\cap Y\), the entropy submodularity gap \(\Delta_X=H(X_Z)+H(X_Y)-H(X_E)-H(X_{Z\cup Y})\) is the conditional mutual information between the shares on \(Z\setminus E,Y\setminus E\) given \(X_E\). Applying the same identity while conditioning additionally on \(S\), its conditional counterpart is nonnegative. Subtracting and using the entropy chain rule yields
\[
 \Delta_X\ge
 H(S\mid X_E)-H(S\mid X_Z)-H(S\mid X_Y)+H(S\mid X_{Z\cup Y}).
 \tag{6}
\]
This is the access-function submodularity rule, stated here in raw entropy units.

Let \(g_j=H(X_J\mid X_{P_j})\) and \(e(U)=H(S\mid X_U)\). Submodularity for \(E_j,P_{j+1}\) gives
\(H(X_{E_j})-H(X_{P_j})\ge H(X_{Y_j})-H(X_{P_{j+1}})\). Adding this to (6) for \(Z_j,Y_j\) gives
\[
 g_j-g_{j+1}\ge e(E_j)-e(Y_j)-e(Z_j)+e(Z_{j+1}).
\]
The endpoint satisfies \(g_M\ge I(S;X_J\mid X_{P_M})=e(P_M)-e(Z_M)\). Thus summing telescopes *all* intermediate \(e(Z_j)\), leaving the exact lower bound
\[
 H(X_J\mid X_F)\ge e(P_M)+\sum_{j=0}^{M-1}e(E_j)-e(A)-\sum_{j=0}^{M-1}e(Y_j).
 \tag{7}
\]
There are \(M+1=2^{|J|}-1\) forbidden terms with positive sign and the same number of qualified terms with negative sign. By (1) and nonnegativity of entropy,
\[
 H(X_J\mid X_{A\setminus J})/H(S)\ge a(2^{|J|}-1). \tag{8}
\]
This also covers \(|J|=1\) with an empty sum in (7). Normalized subadditivity yields the first inequalities in (2), and \(A\) is qualified, so \(H(X_A)\ge I(S;X_A)\ge rH(S)\). This proves the first two constraints of (2). In the perfect case and \(J=A\), the lower argument is Csirmaz's original chain proof.

For the asymmetric constraints, take \(J=A\). Then \(F=\varnothing,\ i_j=j,\ P_j=B_j,\ Z_j=A\cup B_j,\ M=t-1\). Start the same sum at any \(i\) instead of at 0. Writing \(H_0=H(S)\), when \(r\ge\eta\) this gives
\[
 H(X_A\mid X_{B_i})
 \ge (1-\eta)H_0+(t-1-i)(1-\eta-\delta)H_0
      -e(A\cup B_i)
 = \bigl((t-i)a+\delta\bigr)H_0-e(A\cup B_i).
\]
By the entropy chain rule the left side equals \(H(X_A\mid S,X_{B_i})+e(B_i)-e(A\cup B_i)\). The last term cancels. Since \(A\) is qualified,
\[
 H(X_A\mid S,X_{B_i})\le H(X_A\mid S)
   =H(X_A)-I(S;X_A)\le \bigl(x(A)-r\bigr)H_0.
\]
Moreover \(A_i\cup B_i\) is qualified, so
\[
 x(A_i)H_0\ge H(X_{A_i}\mid X_{B_i})
 \ge e(B_i)-e(A_i\cup B_i)\ge e(B_i)-\delta H_0.
\]
Combining these displays gives \(x(A_i)+x(A)\ge r+(t-i)a\). If \(r<\eta\), then \(a=0\), and the constraint is implied by nonnegativity and \(x(A)\ge r\). This establishes all of (2), with no conditional error-cap assumption.

## 4. The perfect projection

At perfect caps \(a=r=1\) the subset inequalities alone describe the convex hull of the permutations of \((1,2,\ldots,2^{k-1})\) plus the nonnegative orthant. Every permutation satisfies all constraints. Conversely, for any nonnegative \(w\), sort indices by decreasing weight and write \(w\cdot x\) as a combination of prefix sums with coefficients \(w_{(i)}-w_{(i+1)}\), where \(w_{(k+1)}=0\). The subset inequalities give \(w\cdot x\ge\sum_i2^{i-1}w_{(i)}\), attained by assigning the smallest value to the largest weight and so on. These inequalities suffice because the convex hull plus orthant is closed, and any separating functional bounded below on it must have nonnegative coefficients.

Attaining every permutation uses an existing construction, which we recall for completeness.

For any finite field \(\mathbb F\), any access structure, and any chosen ordering of the \(k\) distinguished participants, Khazaei's Proposition A.1 constructs a perfect scalar-secret linear scheme assigning their dimensions \(2^{k-1},\ldots,1\) in that order. We recall why. For \(k=0\), an arbitrary monotone structure is realized by independently splitting the same scalar secret additively inside each minimal qualified set (no shares for the empty family). No forbidden set gathers a whole split, and partial views of different splits are independent given the secret and have distributions independent of its value.

Inductively remove the participant \(p\) meant to have dimension 1. If \(p\) itself qualifies, give \(p\) the secret, recursively share it for the restricted structure on the others, and independently pad the remaining distinguished shares to double their dimensions. Otherwise define \(\Gamma_0\) by qualifications of sets not containing \(p\), and \(\Gamma_1\) by qualifications after adding \(p\) to those sets. Both exclude the empty coalition and \(\Gamma_0\subseteq\Gamma_1\). Use independent recursive schemes for independent scalars \(T_0,T_1\) in these two structures; let the true secret be \(T_0\), give \(p\) the form \(T_0-T_1\), and combine each other participant's two shares. Qualified sets without \(p\) know \(T_0\); those with \(p\) and a qualified \(\Gamma_1\)-part can use \(T_1\) and \(p\). Forbidden sets without \(p\) see no information of \(T_0\), and those with \(p\) have a remaining part forbidden in both structures. The paired view is then independent of \((T_0,T_1)\), and observing \(T_0-T_1\) still leaves \(T_0\) uniform. These facts give correctness and privacy. Entropy adds for the paired shares, producing the desired doubled dimensions. This is the standard unit-share construction, not a new sharing primitive.

Independent copies realize rational convex combinations, and independent uniform padding in each selected share realizes nonnegative rational increases. Taking limits gives the full closed projection. The same construction for any access structure on a specified set of \(k\) participants realizes all these projected points, so the Csirmaz structures are simultaneous worst cases for all such coordinate budgets in the perfect model. This is a projected statement only; it does not constrain the tail, as Khazaei's full capacity does.

## 5. The exact two-participant projection

Assume \(k=2\), with distinguished \(u\) early and \(v\) late, and tail \(b=b_1,c=b_2\). The minimal qualified coalitions are \(uv,ub,vbc\); the maximal forbidden coalitions are \(vb,uc,bc,vc\). Here juxtaposition denotes a coalition. These lists follow from the three nonempty distinguished subsets, and testing just those extremal coalitions suffices by monotonicity of available secret information. The singleton and total subset bounds in (2) give \(x_u,x_v\ge a\) and \(x_u+x_v\ge\max(3a,r)\), while the \(i=1\) inequality is \(2x_u+x_v\ge r+2a\). This proves necessity of (3).

If \(r=0\), share no information of \(S\) and use independent padding. If \(r>0\), it suffices to construct exactly reconstructing schemes at parameters \(r'=1\), \(a'=a/r\), \(\eta'=1-a'\). Indeed, let the shared/recoverable secret be a fraction \(r\) of the final uniform vector secret, and append an independent fraction \(\delta=1-r\) that is absent from every share. The residual entropy is then \(\delta H(S)\) at each qualified set. The leakage relative to the final secret is at most \(r\eta'=r-a\le\eta\), and all projected dimensions are multiplied by \(r\).

In the rest of this section set \(r=1\), and use \(a\) for the resulting normalized gap. Subtract \(a\) from each of the two coordinates. The remaining constraints are two nonnegative coordinates \(x,y\) with
\[
 x+y\ge \max\{a,1-2a\},\qquad 2x+y\ge1-a .
\]
Intersecting these lines with each other and with the axes gives the following Pareto vertices in the original coordinates, suppressing duplicated endpoints if desired:

| Range | Pareto vertices \((x_u,x_v)\) |
| --- | --- |
| \(0\le a\le1/3\) | \((a,1),\ (2a,1-2a),\ (1-a,a)\) |
| \(1/3\le a\le1/2\) | \((a,1),\ (1-a,4a-1),\ (2a,a)\) |
| \(1/2\le a\le1\) | \((a,2a),\ (2a,a)\) |

The region is the convex hull of the listed vertices plus the nonnegative orthant: its lower boundary is the polygonal graph given by the active nonnegative, sum and weighted-sum constraints. Each displayed vertex varies affinely on its parameter interval. Therefore it suffices to construct the vertices at the breakpoints \(a=0,1/3,1/2,1\). Independent block concatenation gives any rational interpolation, including its leakage cap \(1-a\); independent padding yields the orthant.

All ingredients below are independent uniform field coordinates unless a share is written as their linear form.

- **\(a=0\).** For \((1,0)\) put the entire secret at \(u\) and \(c\); for \((0,1)\) put it at \(v\) and \(b\). All three minimal qualified coalitions recover, and the leakage cap is 1.
- **Left vertices at \(a=1/3,1/2\).** More generally let \(S=(L,M)\) have fractions \(a,1-a\), and choose independent pads \(R,K\) with the dimension of \(L\). Give
  \[
  X_u=L,\quad X_v=(M,R),\quad X_b=(M,K),\quad X_c=L+R+K .
  \]
  The three qualified coalitions learn all of \(S\): the first two receive both \(L,M\), and \(vbc\) subtracts its two pads. The forbidden pair \(vb\) sees \(M\) and independent pads. The forbidden pair \(bc\) sees \(M,K\) and a form of \(L\) masked by the unknown uniform \(R\); \(vc\) is analogous with the other pad. The forbidden pair \(uc\) sees \(L\) and an independently masked observation, not \(M\). Thus leakage is at most \(\max(a,1-a)=1-a\) for \(a\le1/2\), and the distinguished costs are \((a,1)\).
- **Right vertex at \(a=1/3\).** Take three scalar secret coordinates \(S=(P,Q,T)\) and give \(u:(Q,T),\ v:P,\ b:P+Q,\ c:T\). The three qualified coalitions recover the secret. Each forbidden pair has rank two on \(S\): \(vb\) obtains \(P,Q\); \(uc\) obtains \(Q,T\); \(bc\) obtains \(P+Q,T\); \(vc\) obtains \(P,T\).
- **Right vertex at \(a=1/2\).** Take secret \(S=(P,Q)\), independent pad \(R\), and give \(u:(P,R),\ v:Q,\ b:Q+R,\ c:P+R\). Both \(uv\) and \(ub\) recover \(P,Q\); \(vbc\) first recovers \(R\) and then \(P\). The forbidden \(vb,uc,vc\) reveal respectively \(Q,P,Q\) and no other secret information. The forbidden \(bc\) reveals only the difference \(P-Q\) because the remaining form is masked by \(R\). This gives \((1,1/2)\).
- **\(a=1\).** The perfect vertices \((1,2),(2,1)\) follow from §4. Here are small explicit schemes for the checkers. For \((1,2)\), with secret \(S\) and pads \(R_1,R_2,T\), give \(u:S-T,\ v:(R_1,T),\ b:(R_2,T),\ c:S-R_1-R_2\). For \((2,1)\), with pads \(R,T,Q\), give \(u:(R,T),\ v:S-T,\ b:(S-R,Q),\ c:T-Q\). In the first scheme, \(uv,ub\) know \(T\) and \(vbc\) knows both additive masks. In the second, \(uv\) knows \(T\), \(ub\) knows \(R\), and \(vbc\) obtains \(T\) from \(Q,T-Q\). In each case the rows of every forbidden pair have no nonzero linear combination that cancels all pads and retains \(S\). Equivalently their span has zero intersection with the one-dimensional secret row space, proving perfect privacy. For example, in the second scheme the \(bc\)-rows have the unique masks \(R,Q,T\) after eliminating \(Q\) from the last form; \(v+c\) has the unmatched mask \(Q\); \(vb\) has the unmatched masks \(T,R\); and \(uc\) has no secret row component. In the first scheme \(vb\) has no secret component, \(uc\) has independent nonoverlapping pad directions, and each of \(bc,vc\) is missing one of the two additive masks.

All calculations work over any finite field, including characteristic two. Since rational concatenation uses independent uniform copies, both leakage and entropies add. For a real parameter use rational parameters from the stricter side: at \(r=1\) use \(a_j\ge a\) tending to \(a\), and the continuous vertex descriptions show that feasible points converge. For arbitrary real caps, equivalently choose rational stricter caps \(\delta_j\le\delta,\eta_j\le\eta\) tending to them, scale the above continuous shapes by \(r_j\), and add rational padding converging to the desired padding. At \(r=0\) this argument is unnecessary as independent padding alone suffices. The converse constraints are closed. Thus (3) is the stated closed projection.

## 6. Critical caps and the ordering of the subsets

At (4), \(a=r/t>0\). For any tuple with total \(x(A)=r\), even if it is only in the closed projection, (2) implies
\[
 x(A_i)\ge(t-i)a \quad(0\le i<t).
 \tag{9}
\]
Every distinguished participant is in exactly \(2^{k-1}\) of the nonempty \(A_i\)'s. The sum of the left sides of (9) is therefore \(2^{k-1}r\), and the right sides sum to \(\sum_{i=0}^{t-1}(t-i)a=2^{k-1}r\), since \(t+1=2^k\). Thus every inequality has equality. In particular the index of a nonempty \(D\) satisfies
\[
 \iota(D)=\frac{r-x(D)}{a}=\sum_{j\notin D}\frac{x_j}{a}.
\]
It holds also at \(D=\varnothing\), with both sides \(t\). For each \(j\), \(w_j=x_j/a=\iota(A\setminus\{j\})\) is a positive integer. The \(2^k\) subset sums of the \(w_j\)'s are distinct and form exactly \(0,\ldots,t\), because \(\iota\) enumerates all subsets. Sorting the weights increasingly forces the first to be 1. If the weights already used give all sums in \(0,\ldots,L\), the next cannot be \(\le L\) by uniqueness, and cannot be \(>L+1\) since then \(L+1\) is never represented by any sum. Thus it is \(L+1\), giving the powers of two successively. This forces (5) and the asserted unique vector. If (5) fails, the infimum cannot be \(r\): a sequence of feasible vectors with totals tending to \(r\) is bounded in the nonnegative orthant, and a limit subsequence would satisfy the finite closed inequalities (2) with total \(r\), an impossibility.

For sufficiency first take \(r=1\), so \(\eta=1-1/t\). Over a field \(E\) with at least \(t\) elements, choose secret \(S=(S_1,\ldots,S_t)\) uniform and independent, and partition its coordinates among \(A\), giving the block of size \(2^{\pi(j)}\) as the entire share of \(j\). Choose distinct \(\alpha_1,\ldots,\alpha_t\in E\). For each \(1\le j<t\) define the parity row
\[
 P_j(S)=\sum_{v=1}^t \alpha_v^{j-1} S_v .
\]
Create an independent additive split of row \(j\) among \(b_1,\ldots,b_j\): use independent uniform masks \(R_{j,1},\ldots,R_{j,j-1}\) at positions \(1,\ldots,j-1\), and the final form \(P_j(S)-\sum_{\ell<j}R_{j,\ell}\) at \(b_j\). The masks are independent across rows. Thus a tail coalition whose longest complete prefix is \(B_i\) obtains exactly rows \(1,\ldots,i\). More precisely, conditioned on the secret, the view of each incomplete split has a uniform law independent of the secret, and complete splits yield their parity plus independent masks. Hence, even when including the distinguished blocks in the coalition, its mutual information is exactly that of the known blocks and the \(i\) parities. If it lacks \(z\) secret coordinates after reading its distinguished blocks, the matrix for the remaining coordinates is the first \(i\) Vandermonde rows restricted to \(z\) distinct columns. It has rank \(\min(i,z)\) by its square initial minor of that size. Thus residual entropy is \((z-i)_+\log|E|\). The ordering hypothesis says \(z=\iota(D)\) where \(D\) is the distinguished subset held. Qualified means \(z\le i\), exactly; if \(D=\varnothing\) then \(z=t>i\). Every forbidden set leaves at least one symbol unknown, so its normalized leakage is at most \(1-1/t\). Each distinguished share has the claimed rank and their total cost is exactly 1.

For any prescribed base field \(\mathbb F\), expand \(E\) as a vector space over \(\mathbb F\) to express all operations as \(\mathbb F\)-linear maps. Dimensions and \(H(S)\) scale by the same extension degree in \(\mathbb F\)-units, hence the normalized entropy values do not change. For rational \(r\), concatenate copies of this scheme and append an independent unshared block of relative dimension \(1-r\); this achieves (4) and total \(r\). For real \(r\) use rational strict caps tending to the pair: approximate \(r\) by rationals \(r_j\ge r\), and the target critical leakage \(\eta\) by \(\eta_j\le\eta\). To ensure the latter, at each \(r_j\) one may share a small additional protected part using any perfect scheme; the remaining shared part uses the critical construction, and the omitted part is independent. More explicitly, take a rational \(L_j\le r_j\) tending to \(r\) with \(L_j(1-1/t)\le\eta\), use critical schemes for a fraction \(L_j\) of the final secret, and perfect schemes for the remaining \(r_j-L_j\) recoverable fraction. This has residual at most \(\delta\), leakage at most \(\eta\), and projected vectors tending to the required one. For \(t=1\) simply share a recoverable fraction \(r_j\) at the sole participant; there is no tail or leakage.

## 7. Scope

The exact non-perfect region is proved for \(k=2\). At general \(k\), the asymmetric converse and the critical-total classification apply to every valid order of the distinguished subsets, but (2) is not claimed sufficient away from the specified cases. The entropic caps concern the conditional entropy of the whole secret and may allow an independent portion to be absent from all views; they are not guarantees about its decoding error probability. No conclusion is drawn about arbitrary access structures or actual cryptographic implementations beyond the stated finite-variable models.
