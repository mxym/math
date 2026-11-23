# Hoffman cocliques force empty norm-eighteen seeds

This is an actual graph count, not an extension average. Work in a hypothetical SRG(99,14,1,2) and assume \(N_{16}=U_{1,27}=0\), so the [rank-independent seed theorem](norm18-seven-mark-seed.md) permits at most six norm-eighteen markings at any seed. Let \(\mathcal C\) be a family of \(M\) distinct actual Hoffman 22-cocliques satisfying:
1. every actual norm-eighteen field is orthogonal to every \(1_C\) with \(C\in\mathcal C\);
2. distinct family members meet in one or eight sites.

Then at least
\[
 E(M)=\left\lceil\frac{2233^2 M}{2233+234(M-1)}\right\rceil
\]
distinct seeds have no norm-eighteen marking, for \(M\ge1\). Consequently
\[
 9N_{18}\le6(55,440-E(M)).
\]
For \(M\ge23\), \(E(M)\ge15,538\), giving the even-oriented cap **\(N_{18}\le26,600\)**. This is a necessary condition with precise hypotheses, not a native lower on \(M\) or \(N_{18}\).

## Literal empty seeds from a single coclique

Use an actual nonzero neutral norm-eighteen field \(t=1_P-1_N\). Its signed-unit support has nine sites of each sign with exactly four neighbours of the opposite sign at each support site, by the [classical short-support classification](../../short-support-packing/README.md). For \(C\in\mathcal C\), orthogonality gives \(k=|P\cap C|=|N\cap C|\). If \(k\ge4\), two negative sites in \(C\) both need four positive neighbours in \(P\setminus C\), since \(C\) is independent. That set has at most five sites; their neighbour sets would share at least three, contrary to \(\mu=2\). Thus \(k\le3\).

At \(k=3\), the three negative sites in \(C\) have three four-element positive-neighbour sets within the six-site set \(P\setminus C\). Any two of those four-sets intersect in at most two. Their two-element complements must therefore be pairwise disjoint and partition the six sites. In particular every positive site outside \(C\) has **exactly two** negative neighbours in \(C\), not three.

An actual seed consists of a root \(o\) with a chosen independent four-subset \(Q\) of its neighbours, interpreted as the four negative neighbours of a positive \(o\) in a marking. For any \(o\notin C\) with \(|Q\cap C|\ge3\), this seed has no such marking: it would require \(k=3\), but the root would have at least three negative neighbours in \(C\).

The Hoffman property gives four neighbours in \(C\) for each of the 77 choices \(o\notin C\). They lie in distinct mate pairs of the seven-edge matching on \(N(o)\). There is one seed selecting all four. Otherwise choose three of these four, then choose one of the ten neighbours of \(o\) outside \(C\), excluding the three mates of the selected sites, leaving seven choices. Thus \(C\) supplies exactly \(77(1+4\cdot7)=2233\) distinct empty seeds of the stated kind.

## Count coincidences between two coclique decks

Two different \(C,D\) with intersection one cannot supply the same seed: two subsets of a four-set each of size at least three must share at least two sites. Now suppose \(|C\cap D|=8\), write \(I=C\cap D\), and take the 63 sites in \(O=V\setminus(C\cup D)\). A common seed must have its root in \(O\). At \(o\in O\), the two four-element contact sets \(S_C=N(o)\cap C\) and \(S_D=N(o)\cap D\) intersect in \(d(o)=|N(o)\cap I|\). The number of coincident seeds there is at most \(0,0,4,11,29\) for \(d=0,1,2,3,4\), respectively:
* if \(d=2\), select both common sites and one of two exclusive sites from each list;
* if \(d=3\), select all three common sites and one of eight possible independent fillers, or select two common sites and both exclusive sites, giving at most \(8+3=11\);
* if \(d=4\), the contact lists coincide, with 29 seeds as just counted.

All neighbours of \(I\) lie in \(O\), since both \(C,D\) are independent. Counting degree incidences and common-neighbour pairs of the eight independent sites gives
\[
 \sum_{o\in O} d(o)=8\cdot14=112,\qquad
 \sum_{o\in O}\binom{d(o)}2=2\binom82=56.
\]
If \(n_i=\#\{o\in O:d(o)=i\}\), it follows that \(n_0+n_3+3n_4=63-112+56=7\), so \(n_4\le2\). The discrepancy of the bound at \(d=4\) from \(4\binom42\) is five (at \(d=3\) the bound is already below \(4\binom32\)). Hence for any such pair at most \(4\cdot56+5\cdot2=234\) empty seeds are duplicated.

Let \(w_s\) be the number of cocliques supplying seed \(s\). Summing over the actual seeds gives \(\sum_s w_s=2233M\) and \(\sum_s w_s^2\le2233M+234M(M-1)\). Cauchy–Schwarz on the nonzero multiplicities gives the displayed lower bound on distinct vacant seeds, without assuming uniform overlaps. The expression before rounding is increasing in \(M\), and at \(M=23\) its numerator and denominator are \(114684647/7381\), whose ceiling is \(15538\). There are 55,440 actual seeds and each oriented norm-eighteen marking is counted once at each of its nine positives. The six-mark cap on the nonempty seeds now proves the theorem.

## Verification of hypotheses for the rank-36 palette application

Take \(\mathcal C\) to be the actual **original zero-seven-class** Hoffman cocliques, i.e. \(c=-1_C\) at charge two and cost 22 in the original marked class, not a count averaged over determinant-49 extensions. By the [charge and seven-class pairing dictionary](../affine-witness.md), the raw pairing \(t\cdot 1_C\) of a neutral actual \(t\) with each such \(C\) is divisible by seven. In charge coordinates, neutral \(t\) is already centered and the seven-primary pairing is unchanged by centering \(c\). For \(t\) of norm 18, \(|t\cdot1_C|\le9\); if nonzero it is seven in absolute value. Choose the orientation of \(t\) accordingly. The affine translate \(t-1_C\) then has charge two and squared norm \(18+22-14=26\). The [short-shell classification](../short-shell-moments.md#when-the-nonzero-labels-must-all-be-signed-units) makes this an actual unit \(U_{2,26}\). Thus if that shell is absent, all the asserted orthogonalities hold in the whole graph.

For two original cocliques their difference \(c_C-c_D\) is in the original seven-zero class at charge zero, so its cost \(44-2|C\cap D|\) is divisible by seven (equivalently by fourteen, since it is even). This permits overlaps \(1,8,15\) for distinct members and no other values. Overlap 15 gives an actual Fano norm-14 field, absent at rank 36 by [the rank-36 Fano theorem](../rank36-no-fano.md). Consequently conditions 1 and 2 apply to any rank-36 palette omitting \(U_{2,26}\), once \(N_{16}\) and \(U_{1,27}\) are also absent. The numerical threshold \(M\ge23\), if used, must be certified for its separate native palette and must concern the original rather than folded/averaged compatible counts.
 
## Without the two shell absences

The lower bound on empty seeds concerns the orthogonality and intersection assumptions on the Hoffman family and does not use N16=U127=0. Without those shell absences, apply the [soft seed deletion bound](norm18-soft-seed-loss.md) to the actual markings. Empty seeds remain empty after deletions, and all other seeds have at most six surviving rows. Adding back the bounded deletions therefore gives
```
9 N18 ≤ 6(55440−E(M)) + 385 N16 + 544 U127.
```
The two geometric assumptions on the Hoffman family still apply; they are not being inferred merely from this inequality.
