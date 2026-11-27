# A transversal obstruction for tripled Steiner triple systems of order 27

## Scope and prior work

Akiyama, Suetake and Tanaka, [JCD DOI 10.1002/jcd.21869](https://onlinelibrary.wiley.com/doi/full/10.1002/jcd.21869), show every collineation group of an order-12 plane has order 1, 2 or 3. This note makes no new claim about those groups.

Tomar, [Hexagon 2611.00389v1](https://hexagonmath.org/pdf/2611.00389v1), §5 and §8, proves that the STS(27) of any degree-3 maximal arc in such a plane has a class cover, rules out an affine STS(27) cover in Theorem 5.3, and conjectures there is no cover for any STS(27) (Conjecture 8.4). §8 defines (DP), records tripled (DP) examples and says several hundred non-affine systems of several types were tested. The following uniform counting restriction and explicitly reproducible (DP) example do not assert a solution to that conjecture. Literature comparison does not establish novelty against unpublished examples or computations.

## Counting theorem

Partition 27 points into three 9-point groups. On each group take the 12 lines of AG(2,3), with arbitrary labeling; between the groups take the 81 triples (r,c,Q(r,c)) of a Latin square Q of order 9. These triples form an STS since same-group pairs lie in exactly one affine line and cross-group pairs determine their third coordinate via the Latin property.

A parallel class partitions 27 points into nine triples. Write k for the number of internal lines it has in any one group: if there are t crossing triples, then 3k+t=9 in each of the three groups, so k is common and ranges from 0 to 3. In a class cover each disjoint pair occurs once. Each triple is disjoint from 80 others (there are 117 triples, and separately for each of its three points there are 12 other triples meeting it there), hence appears in 80/8=10 classes. There are 117*10/9=130 classes. Let n[k] count type k. Count occurrences of internal lines in one group to get sum(k*n[k])=120. Count pairs of internal lines from two fixed different groups, always disjoint, to get sum(k^2*n[k])=144. Consequently n[2]=12−3n[3], n[1]=96+3n[3], n[0]=22−n[3].

For a fixed crossing triple b, among the 10 classes containing it let m[k] have type k. Each of the 8 internal lines of a fixed group avoiding the point of b in that group pairs with b once. Thus m[1]+2m[2]=8 and m[0]=2+m[2]. Type-zero classes correspond to full transversals of Q. Any two cover classes share at most one triple, because if they shared two, that disjoint pair would be covered twice. In particular each cell of Q lies in at least two full transversals meeting exactly at that cell. Globally the cover selects 18 to 22 transversals, pairwise meeting in at most one cell.

Further direction restriction (root): In each group a type-3 class uses a complete affine direction. Distinct type-3 classes cannot reuse a direction, and no type-2 class can use a direction used by type 3 in that group, since otherwise the classes would share two or more triples. Fix one of the u=4−n[3] unused directions in group A. Its three pairs of parallel lines must occur in three distinct type-2 classes. The corresponding B directions must all differ: their A pairs necessarily share one line, and if their B directions agreed then their B pairs would also necessarily share one line. Thus either u=0 or u≥3, so n[3] is 0, 1 or 4, and n[0] is 22, 21 or 18. The type-2 direction projection to any two groups is a 3-regular bipartite simple graph on u+u vertices; for u=3 it is complete and for u=4 it is K(4,4) minus a perfect matching.

## Explicit (DP) but not class-cover example

Use the first square from [Wanless's confirmed bachelor data](https://users.monash.edu.au/~iwanless/data/transversals/LS9confbach), displayed as row strings in the code below. On each group represent affine points by x+3y, x,y in F3. Permutation p maps each affine point to its Latin row/column/symbol label. The example uses the three specific arrays in the code. A finite exact enumeration gives 156, 1369, 68, and 64 parallel classes by type, with every one of the 4680 disjoint pairs occurring. The zero-based cell (4,8), its b-index 80, lies in no full transversal, so the counting theorem proves exact nonexistence of a cover. In this same example cell indices 51, 100, 104 *do* each lie in one or more transversals but do not lie in a pair of transversals intersecting only there, so the two-transversal condition is useful beyond the zero-transversal test on individual cells. The exact enumeration computes ordinary (DP) and is not a SAT nonexistence claim. It examines each partition once by choosing the first uncovered point and trying every contained triple incident with it; the 27-bit arithmetic is safely below the signed bit limit.

Reproduction: run the following in any current JavaScript runtime. The result also contains the failed cells as [triple-index, number of full transversals through it]. Crossing triple indices are 36+9*r+c.
```js

function analyze(s,perms=[[0,1,2,3,4,5,6,7,8],[0,1,2,3,4,5,6,7,8],[0,1,2,3,4,5,6,7,8]]) {
const lines=[];for(let i=0;i<9;i++)for(let j=i+1;j<9;j++){let k=(6-(i%3+j%3))%3+3*((6-(i/3|0)-(j/3|0))%3);if(j<k)lines.push([i,j,k]);}
const b=[];for(let g=0;g<3;g++)for(const l of lines)b.push(l.map(x=>9*g+perms[g][x]));
for(let x=0;x<9;x++)for(let y=0;y<9;y++)b.push([x,y+9,s[x].charCodeAt(y)-97+18]);
const masks=b.map(l=>l.reduce((m,x)=>m|(1<<x),0)), ats=Array.from({length:27},(_,x)=>masks.map((m,i)=>[m,i]).filter(([m,i])=>m&(1<<x)));
const p=[],counts=[0,0,0,0], n=masks.length,seen=new Uint16Array(n*n), fulls=Array.from({length:n},()=>[]);
function rec(m){
 if(m===0){let k=p.filter(i=>i<36).length/3;counts[k]++;for(let u of p)for(let v of p)seen[u*n+v]++;if(k===0)for(let u of p)fulls[u].push(p.slice());return;}
 let a=ats[31-Math.clz32(m&-m)];
 for(const [q,i] of a)if((q&m)===q){p.push(i);rec(m^q);p.pop();}
}
rec((1<<27)-1);
let missing=0;for(let i=0;i<n;i++)for(let j=i+1;j<n;j++)if((masks[i]&masks[j])===0&&!seen[i*n+j])missing++;
const bad=[];for(let i=36;i<n;i++)if(!fulls[i].some((u,j)=>fulls[i].slice(j+1).some(v=>u.filter(x=>v.includes(x)).length===1)))bad.push([i,fulls[i].length]);
return {missing,counts,bad};
}
const s = ["abcdefghi","bcdefghia","cabfdeigh","deabhicfg","edghicabf","fieaghbcd","ghicabfde","hgfibadec","ifhgcdeab"];
const perms = [[7,6,4,8,5,1,0,3,2],[2,1,8,6,3,7,4,5,0],[7,6,5,3,2,8,0,1,4]];
const a = analyze(s, perms);
if (a.missing !== 0 || String(a.counts) !== '156,1369,68,64' ||
    JSON.stringify(a.bad) !== '[[51,5],[80,0],[100,5],[104,11]]')
  throw new Error(JSON.stringify(a));
console.log(a);
```

## Stronger witness: all cells lie in at least five full transversals

Take the third Latin square in [Wanless's order-nine minimum disjoint-transversal data](https://users.monash.edu.au/~iwanless/data/transversals/LS9mu), with the same affine relabelings. This example satisfies (DP) and the naive requirement of two transversals per cell, but not the stronger pairwise-intersection condition. In the exact enumeration, counts for k=0,1,2,3 are 168, 1345, 71, 64 respectively and all 4680 disjoint pairs occur. Every cell lies in at least five full transversals. Nonetheless all five through zero-based cell (0,3) contain (2,0) as well, so a class cover is impossible. The following is a standalone augmentation to the preceding enumerator. Change its final return to:

```js
return {missing,counts,bad,full39:fulls[39],min:Math.min(...fulls.slice(36).map(q=>q.length))};
```

Then run:

```js
const strong = analyze(["cbaefdhig","bachigefd","acbighfde","fihdaegbc","dgifeachb","ehgadfbci","ifegbcdah","gdfchbiea","hedbciagf"], [[7,6,4,8,5,1,0,3,2],[2,1,8,6,3,7,4,5,0],[7,6,5,3,2,8,0,1,4]]);
const expected = [[39,47,54,64,80,86,96,103,115],[39,49,54,65,73,88,96,104,116],[39,50,54,70,78,89,91,103,110],[39,52,54,65,73,89,96,104,112],[39,53,54,70,78,83,91,103,113]];
if (strong.missing !== 0 || String(strong.counts) !== '168,1345,71,64' ||
    strong.min !== 5 || JSON.stringify(strong.full39) !== JSON.stringify(expected) ||
    !strong.full39.every(q=>q.includes(54))) throw new Error(JSON.stringify(strong));
```

The five rows of expected are the full transversals through index 39 (cell (0,3)), listed as block indices. Index 54 is cell (2,0). This proof does not use the catalog's assertion about mutually disjoint transversals.