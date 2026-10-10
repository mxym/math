# W(2,7): baseline reconstruction, not a new bound

Date: 2026-10-10

This research checkpoint reproduces the known bound W(2,7)>3703. It does not claim a new bound, an exact value, a proof of optimality, Lean certification, or external review. ES(7) is paused by user direction.

## Explicit coloring

Use zero-based positions i=0,...,3702; ordinary positions are i+1. Put c(0)=1, c(i)=0 at all positive multiples of 617, and c(i)=1 at nonzero quadratic residues modulo 617, otherwise 0.

An exhaustive integer check of all 1140833 seven-term arithmetic progressions found 0 monochromatic progressions. A separate partial-coloring pass leaves the seven multiples of 617 blank: every progression involving any fixed positions already has both colors. The only residual condition is that the seven blank colors are not all equal. Consequently there are 126 valid completions with these nonzero residue colors fixed.

## Scoped extension obstruction

None of these 126 completions can be extended by one position while keeping all earlier nonzero residues fixed. Appending color 1 always gives the monochromatic progression at one-based positions 2+617j (j=0,...,6). Appending color 0 always gives, among others, the progression at one-based positions 3422+47j (j=0,...,6). Both avoid the seven blank positions. This excludes only this fixed template, not arbitrary length-3704 colorings.

For the particular c(0)=1, c(617)=...=c(3702)=0 completion followed by color 1, flipping one element of its unique bad progression gives respectively 6,36,57,58,51,38,6 new bad progressions at positions 2,619,1236,1853,2470,3087,3704. Thus this particular extension has no repair by one bit flip. No larger-neighborhood exclusion has been established.

## Standalone replay (JavaScript)

```js
const p=617, n=3703;
const sq=new Set(Array.from({length:p-1},(_,i)=>(i+1)**2%p));
const c=Array.from({length:n},(_,i)=>i%p===0?Number(i===0):Number(sq.has(i%p)));
let total=0,bad=0;
for(let d=1;6*d<n;d++)for(let a=0;a+6*d<n;a++){
  total++;
  if([0,1,2,3,4,5,6].every(j=>c[a+j*d]===c[a]))bad++;
}
if(total!==1140833||bad!==0)throw Error("baseline failed");
console.log({total,bad});
```

## Sources and interpretation

The established lower bound is recorded in Herwig, Heule, van Lambalgen and van Maaren, A New Method to Construct Lower Bounds for Van der Waerden Numbers, Table 1; Section 4.2 explains the power-residue method and attributes it to Rabung. Source: https://www.cs.utexas.edu/~marijn/publications/waerden.pdf . The reconstruction here is not claimed as a new construction.

Next mathematical bottleneck: modifications must leave this fixed residue template, while controlling newly created progressions. Symmetric or periodic restricted UNSAT alone cannot prove an unrestricted upper bound.
