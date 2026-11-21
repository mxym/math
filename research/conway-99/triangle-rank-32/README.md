# A Conway 99-graph would have Seidel rank at least 34 over the field of seven elements

Let $A$ be the adjacency matrix of a strongly regular graph with parameters $(99,14,1,2)$ and put $S=2A-J+I$. **The rank of $S$ over the field of seven elements cannot be 32.** The [earlier triangle argument](../triangle-rank/README.md) excludes ranks at most 30. The known parity and upper bound leave **34, 36, 38, 40 and 42**. These are necessary possibilities. The existence problem remains open. [Rank parity and its source](../../conway-99-involution/rational-eigenspaces/Theorem.md).

## The finite search

Assume the full rank is 32. Fix any triangle and take the induced graph on it and its 36 neighbors, called the shell. The three wings of twelve each carry a mate matching. Each pair of wings is linked by a perfect matching. Label the first two transfers as identities and write the last as a permutation of twelve sites. The earlier triangle argument proves that 3,580 triples of named mate matchings cover all simultaneous relabelings. Each exterior vertex chooses two nonmated sites per wing. Every nonmate pair in each wing must occur exactly once among the sixty exterior vertices. These facts require no symmetry of the full graph.

For each triple the census fixes the parents and first two wings, then inserts the last twelve sites one by one. The site being inserted and its image under the transfer determine the new column against all previously assigned sites. Bordering a symmetric matrix raises its rank by two if the new column pairs nontrivially with its kernel. Otherwise the increase is one for a nonzero residual diagonal and zero for a zero residual diagonal. These statements follow by splitting off a nonsingular principal minor and taking its Schur complement. A prefix over the cap can therefore be discarded. To quotient a partial assignment, fix pointwise all components of the three named matchings touched by any assigned source, target, or the next source. On the untouched components, retain one target per orbit of rooted, color-preserving component isomorphisms. Such a bijection extends to a permutation of the full label set by swapping isomorphic components if necessary. Every descendant of a skipped choice has a simultaneously relabeled counterpart under a retained choice.

Let $s$ be the shell rank, $Z$ a matrix whose rows span the shell kernel and $V$ the matrix of exterior columns restricted to the shell. Splitting off the nonsingular minor gives the lower bound $s+2\operatorname{rank}(ZV)$ for the full rank. For an exterior candidate $v$, its entries are $+1$ on six sites and $-1$ elsewhere.

* At $s=31,32$ the exterior columns must all satisfy $Zv=0$. The first pass tests that every nonmate pair of the first wing can occur with this property. It retains every lower-rank shell.
* The second pass tests pair prescriptions on all three wings, disallowing any choice of six sites in which two already have their full quota of common neighbors. At $s=32$ each added column must also give a bordered matrix of rank 32. At $s=29,30$ all nonzero $Zv$ must lie on a single common line. A pair admitting $Zv=0$ puts no restriction on that line. The pass sends shells of rank at most 28 directly to the final check.

The first pass returns 33,124 records. The second leaves 72, or eight representatives after simultaneous conjugation within each matching triple. Six representatives already contain a pair with too many common neighbors. The remaining two are addressed below.

## Two final obstructions

For a connected component $D$ of the graph on the 36 wing sites, each far vertex must see exactly $|D|/6$ of its sites. Indeed, each component meets the three wings equally often, by the two identity transfers. The vector equal to its indicator minus $|D|/36$ on the wings, and zero elsewhere, is perpendicular to the all-ones vector. The wing graph is cubic. On the shell this vector satisfies the eigenvalue-three equation, including at the parents. Its Rayleigh quotient in the whole graph is therefore three. The only eigenvalues on the all-ones perpendicular space are three and minus four, so the vector is a full eigenvector for three. At each far vertex its eigenvalue equation gives the claimed balance. This real argument is valid regardless of the modular rank.

In addition to this balance and the pair quotas, a candidate with six chosen sites must have at most $2-a$ common shell neighbors with each shell vertex, where $a=1$ if the vertex is among the six and zero otherwise.

* **Shell rank 28.** At most two dimensions are available for the span of $Zv$. Enumerate every locally admissible word, retaining 23,904. For each required wing pair form the set of directions of its candidate vectors. A required pair with no zero vector forces at least one of its directions into the putative plane. Choose such a pair with the fewest directions, giving 213 possibilities. For each direction take the quotient by its span. Every required pair must now allow zero or admit the same quotient line. All 213 intersections fail.
* **Shell rank 31.** There are 5,760 admissible words in this representative. For every word orthogonal to the shell kernel, ordinary elimination gives $v_I^t S_I^{-1}v_I=0$, where $I$ indexes a nonsingular principal minor of rank 31. After splitting off this minor, the shell radical vanishes against every remaining column. The far block has zero diagonal because its original diagonal and every displayed correction are zero. For the full rank to be 32 this symmetric block would have to have rank one. A symmetric rank-one matrix over the field is a nonzero scalar times $ww^t$ and has a nonzero diagonal entry. This rules out the last representative.

## Replay

Use Python 3 with NumPy and a C++17 compiler. From this directory run

```sh
c++ -O3 -std=c++17 census.cpp -o /tmp/conway-census32
c++ -O3 -std=c++17 extend.cpp -o /tmp/conway-extend32
python3 verify.py /tmp/conway-census32 /tmp/conway-extend32 --jobs 5
```

The two passes reproduce the following SHA-256 digests over lexicographically sorted ASCII output lines, each with a trailing newline. The final Python pass reconstructs the adjacency matrices from the surviving permutations.

| Stage | Records | SHA-256 |
| --- | ---: | --- |
| Rank census and first-wing test | 33,124 | f7b00acd43bf716b485f148e641457bee48923e936f2b6eeaeb182d8410b190e |
| Three-wing extension test | 72 | d8df755af3c521d71fa51fd7506de4f036da7cee17b6dcbbad0bfadf2dcf7cb4 |

An instrumented run visited 16,475,511,643 prefixes and reached 1,721,394 leaves across all matching triples. A separate run of the packaged census reproduced the first-pass digest. Both runs use the same mathematical enumeration.
