# Genuine high-factor chains: scale cap and exclusion above \(N/7\)

A true high-factor path consists of distinct odd unit primes \(x_0,\dots,x_{k-1}>\sqrt N\) with \(x_i+m_i x_{i+1}=N\) and odd integer cofactor \(m_i\ge3\). A true cycle includes the edge back to \(x_0\). The next prime is the unique factor above \(\sqrt N\), including multiplicity. No ambient finite closure is needed.

## 1. Limited side support below a cap

Assume all \(x_i\le U<N\) and that all cofactor primes belong to a set \(S\) of size \(t\). Define
\[
 \lambda=\max\{3,(N-U)/U\},\qquad
 A=\max\left(1,\prod_{q\in S}\left(1+\left\lfloor
                  \frac{\log N}{2\log q}\right\rfloor\right)-1\right),\qquad
 w=1+\left\lfloor\frac{\log U}{\log\lambda}\right\rfloor.
\]
Each \(m_i<\sqrt N\) and \(m_i\ge\lambda\), so \(A\) bounds the quotient alphabet. If two positions \(j,j'\ge w\) share the preceding word of \(w\) quotients, the same composition of affine maps \(x\mapsto(N-x)/m\) sends their respective starting labels in \((0,U]\) to their end labels. The absolute slope is at most \(\lambda^{-w}<1/U\); the end labels differ by less than 1 and so coincide. Hence
\[
 k\le w+A^w.                                                   \tag{1}
\]
The argument applies to any contiguous subpath and can use its actual number of quotients.

For a single side prime \(p\), if all labels lie in \([V,U]\), with \(U/V\le2\) and \(U\le N/3\), the ratio between maximum and minimum possible quotient is at most \(\frac{N-V}{N-U}\frac UV<3\). Distinct powers of \(p\ge3\) are separated by factor at least 3, so the quotient is fixed throughout. Substituting \(A=1\) gives \(O(\log N)\) labels even at a linear-scale band, and \(O_\eta(1)\) at \(U\le N^{1-\eta}\) with fixed \(\eta>0\).

For a possibly moving alphabet, write \(L=\log N\). At \(U=N\exp(-L^\gamma)\), \(0<\gamma<1\) fixed, we have \(\log\lambda\ge (1-o(1))L^\gamma\), \(\log A=O(t\log L)\), and (1) yields \(\log k=O(L^{1-\gamma}(t+1)\log L)\). If a rank constraint forces a true high chain of length \(\exp(\Omega(L^\theta/s))\) with \(s=O(\log L/\log\log L)\), and its cofactors use \(t=O(\log L)\) primes, then for any fixed \(1-\theta<\gamma<1\), every contiguous block longer than the bound in (1) includes a label above \(U\). Entering such a label also entails \(m_i<N/U=\exp(L^\gamma)\) if the preceding edge is in the chain. This does not constrain chains with many side primes and the moving cap \(U\) is not a fixed positive fraction of \(N\).

## 2. Uniform linear-scale cap and cycle exclusion

**Proposition.** If \(N>49\) is even and \(7\nmid N\), every true factor path with all labels \(>N/7\) has at most \(46+\log_3 N\) vertices. No true factor cycle can have all labels \(>N/7\) in this regime. There is no small-radical or cofactor-support hypothesis.

Since \(N/7>\sqrt N\) and \(N/7>7\), each quotient is odd and in \([3,7)\), hence is 3 or 5. If \(3\mid N\), quotient 3 is forbidden since it would force \(3\mid x_i\), inconsistent with the true label being a unit. The same applies to quotient 5 if \(5\mid N\). If neither quotient is available the path is trivial; if just one is available it is a fixed-quotient run. In any fixed-quotient run \(m\ge3\) with \(a\ge1\) edges,
\[
 1\le |x_a-x_{a-1}|=m^{-(a-1)}|x_1-x_0|< N m^{-(a-1)}
\]
by distinctness. Thus it has at most \(2+\log_3 N\) labels. A fixed-quotient true cycle is impossible because the affine map \(x\mapsto(N-x)/m\) and its iterates all have the same unique real fixed point, forcing all labels to coincide. A single-label unit self-loop is impossible as well (\(x\mid N-x\) would imply \(x\mid N\)).

When \(N\) is a unit mod 105, normalize \(r=x/N\bmod105\). The labels exceed 7 and are prime, so states are the 48 unit residues mod 105. A quotient-\(m\) arc obeys \(r+ms=1\bmod105\). This is only a necessary modular condition; no modular walk is assumed to lift. List the arcs by selecting each target unit \(s\) and \(m\in\{3,5\}\) and retaining \(r=1-ms\bmod105\) only when it is a unit. Repeatedly delete all states with zero indegree or zero outdegree at the start of the round. The exact deletions are:
~~~
1: 1 2 8 16 17 22 23 26 29 31 32 38 43 44 46 47 52 53
   59 61 62 64 68 71 74 76 83 89 92 104
2: 19 37 82 101 103
3: 11 13 58
4: 67 73 86
5: 88 97
6: 41
~~~
The survivor graph is \(4\to34\to94\to4\) and \(79\to79\), all arcs labeled 3. A repeated residue in a walk lies on a nonempty closed directed walk, whose states each retain an in- and out-neighbor from the walk in every pruning round. Thus every outside state occurs at most once. Likewise a path joining two core states cannot leave the core: its union with the core cycles has positive indegree and outdegree throughout, so every state on the path would survive. All visits to the core therefore form at most one contiguous block, with each internal edge of quotient 3. At most 44 outside positions and at most \(2+\log_3 N\) core positions prove the bound. For any real cycle all modular states and arcs lie in the core, so the quotient is fixed and the cycle is impossible.

If \(7\mid N\) but \(3\mid N\) or \(5\mid N\) as well, the separate fixed-quotient case still applies. If \(7\mid N\) and both \(3,5\) are units, the mod-105 normalization is invalid and no such conclusion is claimed. Separately, true paths with quotients in \(\{3,7\}\) have at most one 3-run followed by one 7-run, hence \(O(\log N)\) labels, for every even \(N\) and labels above 7. If \(3\mid N\) then quotient 3 is forbidden, and if \(7\mid N\) quotient 7 is forbidden. If neither divides \(N\), normalize mod 3: a quotient-7 edge has both endpoints equal to 2 modulo 3 in normalized coordinates (both units and \(7\equiv1\)); a quotient-3 edge starts at normalized residue 1. Thus 3 cannot occur immediately after 7. The same reasoning excludes cycles supported on \(\{3,7\}\), since a cyclic mixed word would necessarily contain a \(7,3\) transition and a fixed word cannot cycle.

## 3. Exact 48-state replay

The following JavaScript certifies the deletion rounds and survivor arcs, with integer residues only.
~~~js
const Q=105, ms=[3,5];
const good=x=>x%3!==0 && x%5!==0 && x%7!==0;
let V=new Set(Array.from({length:Q-1},(_,i)=>i+1).filter(good));
const arcs=new Map([...V].map(x=>[x,[]]));
for(const y of V) for(const m of ms){
  const x=((1-m*y)%Q+Q)%Q;
  if(arcs.has(x)) arcs.get(x).push([y,m]);
}
const rounds=[];
for(;;){
  const inSet=new Set();
  for(const x of V) for(const [y] of arcs.get(x))
    if(V.has(y)) inSet.add(y);
  const gone=[...V].filter(x=>!inSet.has(x)||!arcs.get(x).some(([y])=>V.has(y)));
  if(!gone.length)break;
  rounds.push(gone);
  for(const x of gone)V.delete(x);
}
const core=[...V].flatMap(x=>arcs.get(x).filter(([y])=>V.has(y)).map(([y,m])=>[x,y,m]));
const expectedRounds=[
 [1,2,8,16,17,22,23,26,29,31,32,38,43,44,46,47,52,53,59,61,62,64,68,71,74,76,83,89,92,104],
 [19,37,82,101,103], [11,13,58], [67,73,86], [88,97], [41]
];
const expectedCore=[[4,34,3],[34,94,3],[79,79,3],[94,4,3]];
if(JSON.stringify(rounds)!==JSON.stringify(expectedRounds)||
   JSON.stringify(core)!==JSON.stringify(expectedCore))throw Error('certificate mismatch');
console.log({rounds,core});
~~~

**Scope.** These constraints can be imposed on the genuine all-composite closure of selected seeds at a hypothetical Goldbach failure. In particular, long high chains under \(7\nmid N\) must have visits \(\le N/7\) in every sufficiently long block. This is compatible with the conditional required visits above \(N\exp(-L^\gamma)\) from section 1, since that threshold is asymptotically below \(N/7\). Neither bound implies or refutes a Goldbach prime pair.
