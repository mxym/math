# Sharp internal sunflower extraction for large pair fibers

**Yongxian Zhang.** AI-assisted proof development and internal checks; no external peer review claimed.

Let \(m\ge2\) and \(1\le L\le m\) be integers. Let \(H\) be a finite tripartite 3-uniform family on \(A,B,C\). Suppose its \(AB,AC\) projections are injective, its maximum \(A\)-vertex degree is at most \(L\), and every occupied \(BC\) fiber has size at least \(\max(2m,mL)\). There are no upper bounds on the pair-fiber sizes and no comparability assumption.

**Theorem.** The sharp worst-case proportion retained while providing an internal \(m\)-petal sunflower for every **nonempty** pairwise intersection is \(\Theta(1/m)\). The lower-bound method also gives \(\Omega(1/(m+L))\) for arbitrary \(L\ge1\) with the same fiber hypothesis. This is a special case of the [internal sunflower question](https://link.springer.com/article/10.1007/s00493-026-00222-1#Sec6), complementary to the [capped-multiplicity regime](TwoInjectiveInternalSunflowers.md); the full-kernel case is treated below. It does not address arbitrary mixtures of small and large fibers.

## A sufficient structure

It suffices to choose a simple subgraph \(G'\) of the \(BC\) projection with each positive vertex degree either 1 or at least \(m\), and retain at least \(m\) original triples in each chosen \(BC\) fiber, with \(A\) labels unique across the entire output. A repeated \(BC\) pair supplies its own sunflower. If a shared vertex \(B\) or \(C\) occurs with different projected neighbors, it has at least \(m\) such neighbors, which supply petals with disjoint labels in both other parts. No two output triples share an \(A\) label.

## Dense projection

Peel vertices of projected degree less than \(m\), recording an edge at the first endpoint peeled. In the remaining core the simple projected minimum degree is at least \(m\). For each occupied fiber \(e\) of size \(f_e\), allocate \(\lfloor f_e/L\rfloor\) distinct \(A\) labels, with no label allocated to another fiber. This follows from Hall's theorem with quotas: any fiber set \(S\) is incident to at least \(\sum_{e\in S} f_e/L\) different \(A\) labels, since each \(A\) has degree at most \(L\); replace fibers by their prescribed numbers of identical copies to apply Hall. Each allocation has size at least \(m\) and at least \(f_e/(2L)\), so the core retains \(\Omega(1/L)\) of its triples.

## Peeled orientation

In each of the two orientations of the peeled graph, tails have simple degree less than \(m\). Split each orientation into heads with original indegree less than \(8m\) in that orientation and with indegree at least \(8m\). Each split keeps or discards all edges at a head, so a high head retains its original indegree. We may work in whichever of these four pieces or the core has the most original triples, keeping every fiber whole until sampling.

For the low-head piece, sample projected pairs independently with probability \(p=1/(128(m+L))\). Keep only isolated sampled pairs, and for each such pair keep only triples whose \(A\) label did not occur at any other sampled pair. Conditioned on the given pair being sampled, the chance any given triple is lost at this step is at most \((9m+L)p\) by the union bound, since the pair has fewer than \(9m\) adjacent pairs and the label has fewer than \(L\) other incidences. Delete fibers now containing fewer than \(m\) triples. In a conditional fiber of size \(f\ge 2m\), such a deletion requires losing more than half its triples, so its conditional probability is at most \(2(9m+L)p\) by Markov's inequality. The two loss bounds show that a fixed original triple is finally retained with probability at least \(p(1-3(9m+L)p)>p/2\). The output projection is a matching.

For the high-head piece, sample heads independently at the same probability \(p\). A tail allows its projected pair only if the head is sampled and no other sampled head touches that tail. At every allowed pair discard triples whose \(A\) label is used by another sampled head. The projection incident to \(A\) and the head part is injective, so an \(A\) never repeats at the same head. Thus every original triple, conditional on its own head being sampled, has initial loss probability at most \(\delta=(m+L)p\). As before, the conditional probability that its fiber becomes too short is at most \(2\delta\). Remove too-short fibers, then remove heads with fewer than \(m\) surviving neighbors. Conditional on a head of original indegree \(s\ge8m\) being sampled, the expected number of too-short fibers is at most \(2\delta s\); the conditional probability that fewer than \(m\) survive is at most \(2\delta s/(s-m)\le16\delta/7\). For a fixed triple these failures, together with its individual loss, have total conditional probability less than \(6\delta\). Hence its final retention probability exceeds \(p/2\). The remaining projection is a vertex-disjoint union of stars with at least \(m\) leaves each, and all \(A\) labels are globally unique.

Summing the expected retentions within a largest piece proves the lower order.

## Sharpness for \(L\le m\)

Let the \(BC\) projection be \(K_{m-1,m-1}\), and give each projected edge a private set of \(w\) different \(A\) labels, with \(w\ge\max(2m,mL)\). Both injectivity conditions hold, and the \(A\) degrees are one. A valid extraction must use a projected matching: two retained edges at a common \(B\) with different \(C\) labels (or vice versa) need a singleton-kernel sunflower with \(m\) distinct projected neighbors, whereas only \(m-1\) exist. At most \((m-1)w\) of the \((m-1)^2w\) triples can be retained, and selecting full fibers on a projected matching attains this. The upper fraction is \(1/(m-1)\).

## Including the empty kernel

Under the same hypotheses with \(L\le m\), the sharp retention order for **all** pairwise intersections is \(\Theta(1/m^2)\). Use first the nonempty extraction above, of size \(\Omega(|H|/m)\) with the sufficient structure specified there. If its projected graph has an \(m\)-matching, choose one triple over each of those pairs. The \(A\) labels are globally unique, so those triples witness the empty kernel and the whole extraction is fully valid.

Otherwise the endpoints of a maximal projected matching cover all selected projected pairs and number fewer than \(2m\). One of these vertices carries at least \(1/(2m)\) of the extracted triples. Retain all extracted triples at that vertex and discard the rest. Its number of projected neighbors was 1 or at least \(m\). The selected star therefore retains all required nonempty witnesses (fibers remain whole, and at least \(m\) distinct neighbors supply a singleton kernel if one occurs); it has no empty intersections. This gives \(\Omega(|H|/m^2)\).

For the upper bound use the same \(K_{m-1,m-1}\) example with private \(A\) labels. Its original projection has no \(m\)-matching, so an empty-kernel witness is impossible. Every nonempty-valid projected subgraph must be a matching, hence in the full-kernel case it can use at most one pair. A single full fiber is valid, retaining exactly \(w\) of \((m-1)^2w\) triples.
