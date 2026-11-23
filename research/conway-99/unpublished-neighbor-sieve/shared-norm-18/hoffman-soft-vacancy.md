# Soft original-Hoffman seed vacancies

For a hypothetical Conway graph, let \(M\) count its actual original zero-seven-class Hoffman 22-cocliques (not a residue-normalized or extension-averaged population). For \(M\ge1\), put
\[
 E(M)=\left\lceil\frac{2233^2 M}{2233+234(M-1)}\right\rceil,
\]
with \(E(0)=0\). The one exception is when \(M=2\) and the two cocliques meet in fifteen sites; put \(E(2)=3780\) in that case. Then the actual graph populations obey
\[
 9N_{18}\le6(55,440-E(M))+385N_{16}+544U_{1,27}+36U_{2,26}.
\]
Neutral fields are counted in both orientations, and each \(U\) counts actual unit fields of the displayed positive charge. No absence of any of these four indicated short shells is required.

## Original coclique vacancies, and the only exceptions

For each \(C\), the [original-Hoffman vacancy proof](hoffman-vacant-n18-seeds.md) counts 2,233 seeds \((o,Q)\) with \(o\notin C\) and \(Q\) an independent four-subset of \(N(o)\) meeting \(C\) in at least three sites. Call these nominal holes of \(C\), without yet assuming orthogonality. Distinct original cocliques meet in one, eight, or fifteen sites by the original seven pairing. For families with fifteen-overlap pairs, the [Fano endpoint seed count](many-hoffman-fano-seeds.md) gives the same union lower bound, with the stated exception when \(M=2\). This part of the counting is independent of how many fields are present at a nominal hole.

Any actual norm-18 field at a nominal hole fails to be orthogonal to the corresponding \(C\), since the vacancy proof showed that equality of the two sign hits makes this seed empty. The original class modulus gives \(t\cdot1_C=\pm7\), because it is a multiple of seven of absolute value at most nine. Orient \(t\) positively on \(C\)'s sum and write \(b=t-1_C\). This is true charge two and cost \(18+22-14=26\), hence a unit \(U_{2,26}\) by the short-shell classification. Conversely the source of a fixed pair \(b,C\) is uniquely \(t=b+1_C\) with that orientation.

The positive sites of \(b\) avoid \(C\), since otherwise \(b+1_C\) would have an exceptional \(+2\). The negative shore of \(b\) has 24 sites, and \(t\) has nine negatives, so \(C\) contains precisely fifteen of the 24 negatives of \(b\). It follows also that \(t\) has seven positives in \(C\) and **no** negatives there. Among the two orientations of \(t\), therefore only \(-t\) can occur at a nominal hole of \(C\). It can do so at no more than its nine positive roots, since the four negative neighbours at each such root determine its unique seed. Given a marking at a seed in the union of nominal holes, choose any one coclique witnessing the nominal hole. This assigns the flag to an actual pair \(b,C\) and one of those at most nine seeds.

For a fixed \(b\) at most four original cocliques are possible. If five existed, their intersections with the negative shore of \(b\) are five 15-subsets of a 24-set. Their 75 incidences have at least \(21\binom32+3\binom42=81\) pair coincidences by integer convexity. Any two candidate cocliques share at least six sites on the negative shore of \(b\), since \(15+15-24=6\). If two overlap in fifteen, every other original coclique meets them in just one site by the Fano endpoint intersection table, so there can be no third candidate. Thus in a putative family of five every pair meets in eight, giving at most \(8\binom52=80\). Contradiction. The union of nominal holes thus contains at most \(36U_{2,26}\) oriented field–seed flags in all. This upper does not require the hole sets to be disjoint, and uses no assumption on marking–coclique pairs outside the actual chosen family.

## Add the two soft deletion losses off the nominal holes

Apply the [rank-independent seed deletion argument](norm18-soft-seed-loss.md) to the seeds **outside** the union of nominal holes. It deletes at most \(385N_{16}+544U_{1,27}\) total flags, since its bounds were on recovery in the whole graph and only decrease on restricting the seeds. At the remaining seeds \(m+j+k\le6\); in particular \(m\le6\). There are at most \(55,440-E(M)\) such seeds. Adding back the soft deletions and then the flags in nominal holes gives the stated inequality, because each actual oriented norm-18 field contributes nine seed flags. No claim of an entire rank or support exclusion follows from this inequality without independent native population constraints.
