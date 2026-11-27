"use strict";

// Tiny fixed examples, testing counts and character identities only.
const pools=[
  [2,3,5,7],
  [3,5,7,11,13,17,19,23,29],
  [37,41,43,47,53,59,61,67,71,73]
];
function gcd(a,b) { while(b)[a,b]=[b,a%b]; return a; }
function abs(b){ return b<0n?-b:b; }
let checks=0, profiles=0, conductors=0, sparse=0;
function ok(x,msg){checks++; if(!x)throw Error(msg);}
for(const P of pools) for(let m=2;m<=239;m++) {
  const units=Array.from({length:m-1},(_,i)=>i+1).filter(i=>gcd(i,m)===1);
  const phi=BigInt(units.length), active=P.filter(p=>gcd(p,m)===1);
  for(const ordered of [false,true]){
    const bins=Array(m).fill(0n), a=new Map();
    for(let i=0;i<P.length;i++)for(let j=ordered?0:i+1;j<P.length;j++) {
      const n=P[i]*P[j]; a.set(n,(a.get(n)||0n)+1n);
      if(gcd(n,m)===1)bins[n%m]++;
    }
    let K=units.reduce((s,z)=>s+bins[z],0n);
    const L=BigInt(active.length), M=BigInt(P.length);
    ok(K===(ordered ? L*L : L*(L-1n)/2n),"correct unit mass");
    ok([...a.values()].every(w=>w===1n||w===2n),"bounded coefficient weights");
    if(K===0n)continue;
    const N=ordered?M*M:M*(M-1n)/2n;
    const eq=units.reduce((s,z)=>s+(phi*bins[z]-K)**2n,0n);
    const absSum=units.reduce((s,z)=>s+abs(phi*bins[z]-K),0n);
    const aboutOld=units.reduce((s,z)=>s+(phi*bins[z]-N)**2n,0n);
    ok(aboutOld===eq+phi*(K-N)**2n,"center shift cross term vanishes");
    const energy=units.reduce((s,z)=>s+bins[z]**2n,0n);
    ok(eq===phi*(phi*energy-K*K),"centered quadratic identity");
    ok(absSum*absSum<=phi*eq,"TV-chi-square Cauchy-Schwarz");
    const support=BigInt(units.filter(z=>bins[z]>0n).length);
    ok(absSum>=2n*K*(phi-support),"uniform mass off support");
    if(phi>BigInt(a.size)) {
      ok(absSum>=2n*K*(phi-BigInt(a.size)),"support-size bound nonvacuous");
      sparse++;
    }
    profiles++;
  }
}
function char(f,n) {
  const a=n%f;
  if(gcd(a,f)!==1)return 0n;
  if(f===3||f===4)return a===1?1n:-1n;
  if(f===5)return a===1||a===4?1n:-1n;
  if(f===8)return a===1||a===7?1n:-1n;
  throw Error("not a toy conductor");
}
const summ=(A)=>A.reduce((s,t)=>s+t,0n);
for(const P of pools)for(const f of [3,4,5,8])for(let e=1;e<=110;e++){
  const m=f*e, removed=P.filter(p=>e%p===0);
  const d=BigInt(removed.length);
  const S=summ(P.map(p=>char(f,p)));
  const T=summ(removed.map(p=>char(f,p)));
  const induced=p=>gcd(p,m)===1?char(f,p):0n;
  ok(summ(P.map(induced))===S-T,"single-prime deletion identity");
  for(const ordered of [false,true]){
    let A=0n,B=0n;
    for(let i=0;i<P.length;i++)for(let j=ordered?0:i+1;j<P.length;j++){
      A+=char(f,P[i]*P[j]); B+=induced(P[i]*P[j]);
    }
    const diag=summ(P.map(p=>char(f,p)**2n));
    const gone=summ(removed.map(p=>char(f,p)**2n));
    ok(A===(ordered?S*S:(S*S-diag)/2n),"primitive character pair sum");
    const expected=ordered?(S-T)**2n:((S-T)**2n-diag+gone)/2n;
    ok(B===expected,"induced character pair sum");
    ok((A-B)**2n<=16n*(d*d*S*S+d**4n),"squared deletion bound");
    if(d===0n)ok(A===B,"no removed prime, no error");
    conductors++;
  }
}
ok(sparse>0,"some small supports");
console.log("OK: "+checks+" exact checks; "+profiles+" residue profiles, "+
            conductors+" conductor/pair-family cases, "+sparse+" sparse-support cases.");
