'use strict';
// Exact continuum certificate; no optimization library or floating-point decisions.
// See KissingAntipodalTradeoffSixSeven.md for notation and why row bounds suffice.
const assert=require('node:assert/strict'), Q=1n<<26n,Q2=Q*Q,Q3=Q2*Q,Q5=Q3*Q2,cut=725n*Q/1024n;
// Each item: degree, cap numerator, intervals [low, high, B, D, J].
const rows=[
  [2,11258,[[21845,29841,0,23475,0],[29841,33839,29595,9607,0],[33839,35838,57604,-2517,0],[35838,37838,64679,-3182,0]]],
  [3,11898,[[24576,32354,0,23475,0],[32354,36243,36334,8856,0],[36243,40133,69664,-1261,0]]],
  [4,12538,[[26214,33831,19918,14589,0],[33831,37640,60788,-549,0],[37640,41449,73447,1770,0]]],
  [5,13178,[[27306,34805,17258,16928,0],[34805,38554,61104,1578,0],[38554,42304,76235,4228,0]]],
  [6,13818,[[28086,35495,19134,16789,0],[35495,39199,60832,3301,0],[39199,42904,78765,6239,0]]],
  [7,14458,[[28672,36010,21029,16493,0],[36010,43348,60827,11223,0]]],
  [8,15098,[[29127,36409,22791,16157,0],[36409,43691,62353,12279,7]]],
  [9,15738,[[29491,43963,56948,14050,0]]],
  [10,16378,[[29789,44185,62442,13204,7]]],
  [11,17018,[[30037,44369,69946,12355,25]]],
  [12,17658,[[30247,44523,75773,11780,39]]],
  [13,18298,[[30427,37541,32601,13277,0],[37541,44656,119919,5417,145]]],
  [14,18938,[[30583,37676,34190,12780,0],[37676,44770,131009,4591,149]]],
  [15,19578,[[30720,37795,36325,12036,0],[37795,41332,57838,9160,0],[41332,43101,59171,11918,0],[43101,43985,59780,13362,0],[43985,44427,60417,14016,1],[44427,44648,136561,4570,111],[44648,44870,6400000,-839375,10442]]],
  [16,21736,[[30840,44958,103181,8897,105]]],
  [17,23489,[[30947,45036,110311,8148,122]]]
];
function bin(n,k){if(k<0||k>n)return 0n;let z=1n;for(let j=0;j<k;j++)z=z*BigInt(n-j)/BigInt(j+1);return z;}
// Univariate Bernstein coefficients of F on a rational interval, scaled by 10000 Q^5.
function poly(lo,hi,co){const dx=hi-lo,r=[];for(let j=0;j<=5;j++){let z=0n;for(let l=0;l<=5;l++)for(let k=0;k<=Math.min(l,j);k++)z+=co[l]*bin(l,k)*lo**BigInt(l-k)*dx**BigInt(k)*Q**BigInt(5-l)*(10n*bin(j,k)/bin(5,k));r.push(z);}return r;}
const pos=[0n,-81n,-250n,260n,1000n,460n],neg=[0n,81n,-250n,-260n,1000n,-460n];let checks=0;
function non(lo,hi){if(poly(lo,hi,pos).every(z=>z<=64n*Q5))return;++checks;const m=(lo+hi)>>1n;if(m===lo)throw Error('nonedge');non(lo,m);non(m,hi);}
non(-Q/2n,Q/2n);
// On a rectangle evaluate each bidegree (5,2) Bernstein coefficient.
// u2,u1,u0 are coefficients of the three auxiliary polynomials, scaled by 20 Q^2.
function certify(d,cap,l,h,b,c,j){d=BigInt(d);cap=BigInt(cap);b=BigInt(b);c=BigInt(c);j=BigInt(j);const n=d<7n?d:7n;let visits=0;
 function box(A,Z,M,N,hi){visits++;const dx=Z-A,dm=N-M,fx=poly(A,Z,neg);let good=true;
 for(const active of (Z<=M?[false]:A>=N?[true]:[true,false]))for(let i=0;i<=5&&good;i++){const v=BigInt(i),a1=5n*A+v*dx,a2=20n*A*A+8n*v*A*dx+v*(v-1n)*dx*dx;for(let k=0n;k<3n;k++){const m1=2n*M+k*dm,m2=2n*M*M+2n*k*M*dm+k*(k-1n)*dm*dm;
 const u2=10n*(Q2-m2)-(active?d*(a2-4n*a1*m1+10n*m2):0n),u1=10n*m1*Q-(active?d*(4n*a1-10n*m1)*Q:0n),u0=20n*Q2*(n-(hi?d:0n));
 if(d*200n*fx[i]+(b*u2+c*u1+j*u0)*Q3>=20n*cap*Q5){good=false;break;}
 }}if(good)return;
 if(dx<=1n&&dm<=1n)throw Error('uncertified '+[d,cap,A,Z,M,N,hi]);
 if(dx>=dm){const m=(A+Z)>>1n;box(A,m,M,N,hi);box(m,Z,M,N,hi);}else{const m=(M+N)>>1n;box(A,Z,M,m,hi);box(A,Z,m,N,hi);}
 }
 const ml=BigInt(l)*Q/65536n,mh=BigInt(h)*Q/65536n;box(Q/2n,cut,ml,mh,false);box(cut,Q,ml,mh,true);return visits;
}
// Prove exact coverage in m, then prove every piece of the dual majorant.
const caps=new Map();for(let [d,cap,t]of rows){const D=BigInt(d),Q0=65536n,lo=BigInt(t[0][0]),hi=BigInt(t.at(-1)[1]);assert(2n*lo*(D+1n)<=Q0*D);assert(2n*hi*hi*(D+1n)>=D*Q0*Q0);let cells=0;
 for(const [i,r]of t.entries()){if(i)assert.equal(t[i-1][1],r[0]);assert(r[2]>=0&&r[4]>=0);cells+=certify(d,cap,...r);}
 console.log('degree',d,'upper',cap+'/100000','boxes',cells);caps.set(d,cap);
}
for(const [r,S]of [[1,8],[2,11],[3,13],[4,15],[5,16],[6,17]])for(let s=1;s<=S;s++)for(let d=2;d<=s;d++){
 const q=2*s+r,n=138900+caps.get(d)+(q-1-d)*640;
 assert(4*s*n<3*q*100000,'row contradiction');
}
console.log('PASS all off-diagonal and continuum row inequalities');
