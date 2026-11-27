'use strict';

// Exhaust the degree-six and degree-seven Radon identities for 34 points.
// The centered univariate lists are justified by the coefficient scan in the checkpoint.
const results = (() => {
const p = 17;
const mod = n => (n % p + p) % p;
const range = Array.from({length:p}, (_,i) => i);
const inverse = range.map(x => range.find(y => mod(x*y) === 1) ?? 0);
function power(x, exponent) {
  let result = 1;
  while (exponent-- > 0) result = mod(result*x);
  return result;
}
const square = new Set(range.map(x => mod(x*x)));
const powers = Array.from({length:8}, (_,degree) => range.map(x => power(x,degree)));
const sexticSquare = [2,0,1,0,2,0,1];
const sexticNonsquare = [6,0,13,0,12,0,3];
const septic = [[6,16,0,8,14,6,0,1],[2,1,0,7,0,7,0,1],
  [1,13,0,10,0,11,0,1],[3,0,9,3,8,12,0,1],[0,6,4,15,13,12,0,1]];

function mask(directions) {
  return directions.reduce((bits, s) => bits | (1<<s), 0);
}
const permutations = [];
for (let a=0; a<p; a++) for (let b=0; b<p; b++)
for (let c=0; c<p; c++) for (let d=0; d<p; d++) {
  if (mod(a*d-b*c) === 0 || ([a,b,c,d].find(x => x !== 0) !== 1)) continue;
  permutations.push(Array.from({length:p+1}, (_,s) => {
    const x = s === p ? a : mod(a*s+b);
    const y = s === p ? c : mod(c*s+d);
    return y === 0 ? p : mod(x*inverse[y]);
  }));
}
function getRepresentatives(size) {
  const seen = new Set(), out = [];
  function extend(slopes, next) {
    if (slopes.length === size) {
      if (seen.has(mask(slopes))) return;
      out.push(slopes);
      for (const permutation of permutations) seen.add(mask(slopes.map(s => permutation[s])));
      return;
    }
    for (let s=next; s<=p-size+slopes.length; s++) extend([...slopes,s],s+1);
  }
  extend([0,1],2);
  return out;
}
function barycentric(slopes) {
  return slopes.map(s => inverse[slopes.reduce((prod,t)=>s===t?prod:mod(prod*(s-t)),1)]);
}
function profileValues(coefficients, shift = 0) {
  return range.map(t => coefficients.reduceRight((v,c)=>mod(v*mod(t-shift)+c),0));
}
function integerCheck(slopes, profiles) {
  const base = 2*(slopes.length-1);
  const values = [];
  for (let x=0; x<p; x++) for (let y=0; y<p; y++) {
    const sum = slopes.reduce((total,s,i)=>total+profiles[i][mod(x+s*y)],0);
    if (sum!==base && sum!==base+p && sum!==base+2*p) return null;
    values.push((sum-base)/p);
  }
  return values;
}
function signature(coefficients,s,maxDegree) {
  return Array.from({length:maxDegree+1},(_,d)=>powers.slice(0,d+1)
    .map(values => mod(values[s]*coefficients[d]))).flat();
}
function sexticCoefficients(leading, shift) {
  const base = square.has(leading) ? sexticSquare : sexticNonsquare;
  const u2 = power(mod(leading*inverse[base[6]]),3);
  const scaled = base.map((v,j)=>j%2 ? 0 : mod(v*power(u2,j/2)));
  const choose = [[1],[1,1],[1,2,1],[1,3,3,1],[1,4,6,4,1],
                  [1,5,10,10,5,1],[1,6,15,20,15,6,1]];
  return range.slice(0,7).map(j=>scaled.reduce((r,v,i)=>i<j?r:mod(r+v*choose[i][j]*power(mod(-shift),i-j)),0));
}
function censusSeptic(slopes) {
  const weights = barycentric(slopes);
  const allowed = slopes.map((s,i)=>septic.map(base=>{
    const coefficients = base.map((v,j)=>mod(v*power(power(weights[i],7),j)));
    return {coefficients, signature:signature(coefficients,s,5)};
  }));
  const partial = new Map(), target = [16,...Array(20).fill(0)];
  const report = {congruences:0, integer:0, doubles:{}};
  function visit(start,end,acc,chosen,cb) {
    if(start===end){cb(acc,chosen);return;}
    for(const obj of allowed[start])visit(start+1,end,acc.map((x,i)=>mod(x+obj.signature[i])),[...chosen,obj],cb);
  }
  visit(0,4,Array(21).fill(0),[],(acc,chosen)=>{
    const key=acc.join(",");
    if(!partial.has(key))partial.set(key,[]);
    partial.get(key).push(chosen);
  });
  visit(4,9,Array(21).fill(0),[],(acc,chosen)=>{
    const key=acc.map((x,i)=>mod(target[i]-x)).join(",");
    for(const left of partial.get(key)??[]){
      report.congruences++;
      const f=integerCheck(slopes,[...left,...chosen].map(obj=>profileValues(obj.coefficients)));
      if(f){report.integer++;const t=f.filter(x=>x===2).length;report.doubles[t]=(report.doubles[t]??0)+1;report.peaks=[...left,...chosen].map(obj=>Math.max(...profileValues(obj.coefficients)));}
    }
  });
  return report;
}
function censusSextic(slopes) {
  const weights = barycentric(slopes), n=slopes.length;
  const report = {leading:0, centered:0, congruences:0, integer:0, doubles:{}};
  for (let a=0; a<p; a++) for (let b=0; b<(n===8?1:p); b++) {
    const leading = slopes.map((s,i)=>mod(weights[i]*(a+b*s)));
    if (leading.includes(0)) continue;
    if (n===8 && leading.some(x=>square.has(x))) continue;
    report.leading++;
    for (let lambda=0; lambda<(n===8?1:p); lambda++) {
      report.centered++;
      const cs=slopes.map((s,i)=>{
        const h=mod(lambda*weights[i]*(s-slopes[0])*(s-slopes[1])*inverse[mod(-6*leading[i])]);
        return sexticCoefficients(leading[i],h);
      });
      const sig=cs.map((c,i)=>signature(c,slopes[i],4));
      if (sig[0].some((_,j)=>mod(sig.reduce((v,s)=>v+s[j],0))!==(j===0?2*(n-1):0))) continue;
      report.congruences++;
      const f=integerCheck(slopes,cs.map(c=>profileValues(c)));
      if(f){report.integer++;const t=f.filter(x=>x===2).length;report.doubles[t]=(report.doubles[t]??0)+1;}
    }
  }
  return report;
}
const targetMask=[3,5,6,8,12,13,14,15,16];
const out = [];
for(const n of [8,9])for(const s of getRepresentatives(n)){
  const inTargetOrbit=n===9&&permutations.some(permutation=>mask(s.map(x=>permutation[x]))===mask(targetMask));
  out.push({s,inTargetOrbit,sextic:censusSextic(s),septic:n===9?censusSeptic(s):null});
}
return out;
})();
const survivors = results.filter(row => row.sextic.integer || row.septic?.integer);
if (results.length !== 34 || results.some(row => row.sextic.congruences) ||
    survivors.length !== 1 || survivors[0].inTargetOrbit ||
    survivors[0].septic.congruences !== 1 || survivors[0].septic.doubles[0] !== 1 || String(survivors[0].septic.peaks) !== '10,4,4,4,4,4,4,10,4') {
  throw new Error(JSON.stringify(results));
}
console.log({masks:results.length,survivors});
