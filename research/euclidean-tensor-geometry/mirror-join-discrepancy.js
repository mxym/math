'use strict';
// Spherical-cap discrepancy of all finite real mirror configurations.
// Usage: node mirror-join-discrepancy.js E6 E8 I2:5
const assert=require('node:assert/strict');
const gcd=(a,b)=>b?gcd(b,a%b):a<0n?-a:a;
const rat=(n,d=1n)=>{n=BigInt(n);d=BigInt(d);if(!d)return [1n,0n];const k=gcd(n,d);return [n/k,d/k];};
const add=(a,b)=>!a[1]||!b[1]?rat(1,0):rat(a[0]*b[1]+b[0]*a[1],a[1]*b[1]);
const cmp=(a,b)=>a[0]*b[1]-b[0]*a[1];const str=a=>!a[1]?'inf':a[1]===1n?String(a[0]):a.join('/');
function components(t){
 let p=t.match(/^([ABCD])([1-9][0-9]*)$/),d=p?BigInt(p[2]):0n;
 const out=(rank,N,M,rays)=>({t,rank:BigInt(rank),N:BigInt(N),M:BigInt(M),rays:BigInt(rays)});
 const polygon=m=>out(2,2n*m,m-1n,m);
 if(p){switch(p[1]){
 case'A':if(d===1n)return out(d,2,1,1);if(d===2n)return polygon(3n);return out(d,d*(d+1n),d,d+1n);
 case'B':case'C':if(d===1n)return out(d,2,1,1);if(d===2n)return polygon(4n);return out(d,2n*d*d,2n*d-1n,d);
 case'D':if(d===3n)return out(d,12,3,4);if(d<4n)break;return out(d,2n*d*(d-1n),2n*(d-1n),d===4n?12n:d);
 }}
 const a={E6:[6,72,16,27],E7:[7,126,27,28],E8:[8,240,57,120],F4:[4,48,15,24],H3:[3,30,10,6],H4:[4,120,45,60],G2:[2,12,5,6]}[t];if(a)return out(...a);
 const q=t.match(/^I2:([1-9][0-9]*)$/);if(q&&BigInt(q[1])>=3n)return polygon(BigInt(q[1]));
 throw Error('unknown irreducible factor: '+t);
}
function classify(types){if(!types.length)throw Error('no factors');const f=types.map(components),N=f.reduce((s,r)=>s+r.N,0n),m=f.reduce((s,r)=>r.M<s?r.M:s,f[0].M),rank=f.reduce((s,r)=>s+r.rank,0n),axes=f.filter(r=>r.M===m).reduce((s,r)=>s+r.rays,0n);
 return {rank:String(rank),points:String(N),minOpenHemisphere:String(m),discrepancy:str(rat(N-2n*m,2n*N)),maximizingEquators:String(axes),hemispheresOnly:rank>=3n};
}
// Positive threshold convention: roots of each component have the same length.
// Each A[k] and B[k] is a nonnegative rational, infinity encoded [1n,0n].
function joinEnvelope(P,Q){const merge=(X,Y,low)=>Array.from({length:X.length+Y.length-1},(_,k)=>{
 let z;for(let i=Math.max(0,k-Y.length+1);i<Math.min(X.length,k+1);i++){const u=add(X[i],Y[k-i]);if(!z||(low?cmp(u,z)<0n:cmp(u,z)>0n))z=u;}return z;});return {A:merge(P.A,Q.A,true),B:merge(P.B,Q.B,false)};}
function selfTest(){
 const expected=[['A1','0',1],['I2:5','1/10',5],['D4','1/4',12],['B6','25/72',6],['E6 E8','35/78',27],['E8 E8','61/160',240],['I2:5 I2:7','1/3',5],['A1 E8','60/121',1],['A1 A1','1/4',2],['A1 A1 A1','1/3',3],['D4 E7','23/50',12]];
 for(const [t,d,e]of expected){const r=classify(t.split(' '));assert.equal(r.discrepancy,d);assert.equal(r.maximizingEquators,String(e));}
 const a1={A:[rat(0),rat(1)],B:[rat(1),rat(1,0)]};let h=a1;
 for(let d=1;d<=32;d++){assert.equal(h.A.map(str).join(),Array.from({length:d+1},(_,i)=>String(i)).join());assert.deepEqual(h.B.map(str),[String(d),...Array(d).fill('inf')]);h=joinEnvelope(h,a1);}
 const hex={A:[rat(0),rat(1),rat(4,3),rat(4)],B:[rat(4,3),rat(4),rat(1,0),rat(1,0)]},j=joinEnvelope(hex,hex);
 assert.deepEqual(j.A.map(str),['0','1','4/3','7/3','8/3','16/3','8']);assert.deepEqual(j.B.map(str),['8/3','16/3','inf','inf','inf','inf','inf']);
 console.log('PASS classification arithmetic, 32 cross-polytope spectra, orthogonal hexagons');
}
if(require.main===module){selfTest();if(process.argv.length>2)console.log(JSON.stringify(classify(process.argv.slice(2)),null,2));}
module.exports={classify,joinEnvelope,rat};
