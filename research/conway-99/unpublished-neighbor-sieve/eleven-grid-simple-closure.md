# No simple four-cubic core at eleven grids

This is an additive conclusion to the [previous eleven-grid screen](eleven-grid-odd-doubled-exclusion.md). Under its hypotheses the simple \(K_4\) case is impossible. Only the two necessary axis shapes of the opposite-doubled even core remain when there are exactly four cubic groups. Six-cubic roots are not covered.

The prior proof leaves one simple-core axis shape: \(AB=a-x-b,\ CD=c-x-d,\ AC=a-y-z-c\), and \(AD,BC,BD\) direct. The four cubic original axes are \(a,b,c,d\); \(x,y,z\) are distinct peripheral axes. Write \(p,t,u\) for the three path-start fields, so the direct columns are \(-p-u,-t-u,p+t+u\). The only Gram menus after the \(AC\) contact test have \(p\perp t\), \(p\cdot u=t\cdot u=-14\), \(u^2=28\), and \((\alpha,\beta)=(p^2/7,t^2/7)\) equal to \((4,4),(4,6),(6,4)\).

The [additive exact certificate](eleven_grid_simple_closure.py) determines which local four-row decks can participate in at least one full moment solution in each of these three menus. For a deck of a given cell, subtract its six quadratic moments from the actual Gram target and enumerate the moment lists in the other twenty cells, with exact integer interval pruning only. If the remaining target is not representable, the deck cannot appear. This is the same necessary row model as the earlier checker, not an assumption that any of the retained decks is a real graph. The certified clean support is: \(u\) vanishes on all clean cells, \(p\) vanishes there except on \(CY\), and \(t\) vanishes there except on \(AZ\). Each of those two active squares has only unit or zero values, centered by the clean projector. At \(\alpha=4\) the squared support in \(CY\) is 2 or 4, while at \(\alpha=6\) it is 4; similarly for \(AZ,\beta\). The three replay lines are
\[
 (4,4):\{2,4\},\{2,4\};\qquad
 (4,6):\{2,4\},\{4\};\qquad
 (6,4):\{4\},\{2,4\}.
\]

## The clean square cannot be fully signed

Suppose \(p\) fills \(CY\) with balanced unit signs. At a positive \(p\)-site of \(CY\), the only possible \(p\)-marked neighbours outside that square are in \(AX\) and \(BD\), both disjoint in axes. Indeed, \(u=t=0\) here, so the two columns \(-p,-p-u\) give no contacts into \(BX,AD\); all other possibly marked dirty cells share \(c\) or \(y\) with the clean square. The \(AX,BD\) columns are \(p,p+t+u\), both taking value \(1\) at the positive sites. At the negative sites both columns equal \(-1\), so all the contacts from \(AX,BD\) into this full clean square go to its two positive sites. Every \(AX\) or \(BD\) vertex has exactly one such contact by cleanness of \(CY\). The total signed external contribution to \(Ap\) at the two positive \(CY\) sites is therefore
\[
 \sum_{AX}p+\sum_{BD}p
 =-\alpha+(2-\alpha)=2-2\alpha,
\]
by the cell-sum formula. Since \(Ap=-4p\), the contribution from the two internal square rows is \(2\alpha-10\), which is \(-2\) or \(+2\). But with a balanced full signed square this internal sum is either zero (the positives adjacent) or \(-4\) (the positives opposite). This contradiction excludes full \(CY\), and the mirror argument excludes full \(AZ\). Thus the mixed norm menus are impossible, and in the remaining \((4,4)\) menu each active clean square has just one \(+1\) and one \(-1\).

## The far short-path center is impossible

Now count the squared entries of \(p\), which has total squared norm 28. The clean contribution is exactly two, all on \(CY\). Each of the own cells \(AX,BX\) has two edges, so contributes four squares of entries if a matching and six if a two-edge path with isolate. The three direct cells \(AD,BC,BD\) each contribute exactly two squared entries of \(p\): their cell sums are \(2,-2,-2\), their \(p\)-signs are forced by the shared \(a\) or \(b\) axis, and both \(p,-p\) are off-cell columns, giving absolute bound one. The long start \(AY\) likewise gives two positive units; the long middle \(YZ\) gives two negative units, since its \(u\)-value is \(+1\) and the disjoint column \(-p-u\ge-1\). The long end \(CZ\) has \(p\)-sum two and \(|p|\le1\), so contributes either two or four squares of entries. The two \(t\)-cells have zero \(p\) by the other split group on \(x\). The baseline dirty contribution is therefore 20, with exactly three possible increments of two, at \(AX,BX,CZ\). Reaching the necessary dirty norm 26 forces all increments, so in particular \(BX\) is a two-edge path and isolate.

On its center \(v\) the \(p\)-value is zero, and \(t=0\) on the entire cell. The field \(u\le0\) on \(BX\) from \(BC\)'s shared column \(-t-u\), and \(p+t+u\ge0\) from the shared \(BD\) column, so \(u(v)=0\). The isolate of \(BX\) has \(p=2\); the disjoint \(AD\) column \(-p-u\ge-1\) forces \(u=-1\) there. The two negative \(u\)-sites in \(BX\) were proved in the preceding \(AC\) contact test. The other one is thus an arm of the path, so the two own neighbours of \(v\) give a total \(-1\) to \(Au(v)\).

There is no contact from \(v\) into \(AX,BC,BD\), whose shared columns are zero there, or into \(CX,DX\), the other split group at \(x\). Because all fields vanish at \(v\), there is exactly one disjoint-axis neighbour in each of \(AY,CZ,YZ,AD\). The respective contributions of the first three are \(-1,-1,+1\), and \(AD\) contributes at most \(+1\). These exhaust the support of \(u\), since it vanishes on all clean cells and the first layer. Consequently
\[
 Au(v)\le -1-1-1+1+1=-1,
\]
contradicting \(Au(v)=-4u(v)=0\).

This excludes the simple core without imposing any arbitrary labeling of the clean squares or exact adjacency completion. It does not remove the doubled-even profiles or establish nonexistence of the graph.
