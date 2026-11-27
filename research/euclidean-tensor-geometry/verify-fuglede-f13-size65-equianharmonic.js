'use strict';
// Equianharmonic four-bad-profile Radon pencil at size 65 in F_13^3.
// After projective normalization the bad forms are x,y,x+y,x+4y.
const p=13, m=5, mod=x=>(x%p+p)%p;
const patterns=Array.from({length:p},()=>[]);
for(let a=1;a<p;a++)for(let c=0;c<p;c++){
  const residues=Array.from({length:p},(_,t)=>mod(c+a*t*t));
  const lift=(m*p-residues.reduce((s,x)=>s+x,0))/p;
  const roots=residues.flatMap((x,i)=>x===0?[i]:[]);
  if(!Number.isInteger(lift)||lift<0||lift>roots.length)continue;
  if(lift>1)throw Error("unexpected lift count");
  for(const root of lift===1?roots:[-1])
    patterns[a].push({c,root,profile:residues.map((x,i)=>i===root?p:x)});
}
let profiles=0, liftAssignments=0, survives=0;
const verified=new Set();
for(let b=1;b<p;b++){
  const a=[mod(3*b),b,mod(9*b),b];
  for(const f0 of patterns[a[0]])for(const f1 of patterns[a[1]])
  for(const f2 of patterns[a[2]])for(const f3 of patterns[a[3]]){
    const F=[f0,f1,f2,f3];
    if(mod(F.reduce((s,f)=>s+f.c,0)-3*m)!==0)continue;
    verified.add([b,...F.map(f=>f.c)].join(","));
    liftAssignments++;
    let feasible=true;
    for(let x=0;x<p&&feasible;x++)for(let y=0;y<p;y++){
      const t=[x,y,mod(x+y),mod(x+4*y)];
      const n=F.reduce((s,f,j)=>s+f.profile[t[j]],0)-3*m;
      if(n%p!==0)throw Error("Radon identity residue error");
      if(n<0){feasible=false;break;}
    }
    if(feasible)survives++;
  }
}
profiles=verified.size;
if(profiles!==198||liftAssignments!==534||survives!==0)
  throw Error(JSON.stringify({profiles,liftAssignments,survives}));
console.log({profiles,liftAssignments,survives});
