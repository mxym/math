'use strict';
const assert=require('node:assert/strict');
let checks=0;
const gcd=(a,b)=>b?gcd(b,a%b):a<0n?-a:a;
const Q=(a,b=1n)=>{a=BigInt(a);b=BigInt(b);if(b<0n)[a,b]=[-a,-b];assert(b>0n);const g=gcd(a,b);return [a/g,b/g];};
const Z=Q(0),I=Q(1),C=(a,b)=>a[0]*b[1]-b[0]*a[1];
const N=([a,b])=>Q(-a,b),A=([a,b],[c,d])=>Q(a*d+b*c,b*d),M=([a,b],[c,d])=>Q(a*c,b*d);
const S=(a,b)=>A(a,N(b)),D=(a,[c,d])=>M(a,Q(d,c));
const abs=a=>a[0]<0n?N(a):a,floor=([a,b])=>a/b,ceil=([a,b])=>(a+b-1n)/b;
const pow=(a,n)=>n<0?D(I,pow(a,-n)):n?M(a,pow(a,n-1)):I;
const max=a=>a.reduce((x,y)=>C(x,y)>=0n?x:y),sum=a=>a.reduce(A,Z);
const pos=a=>{assert(a[0]>0n, String(a));checks++;};
const nonpos=a=>{assert(a[0]<=0n,String(a));checks++;};
const gte=(a,b)=>{assert(a>=b);checks++;};
function rat(v){
  const [a,b='']=String(v).split('.');
  return Q(a+b,10n**BigInt(b.length));
}
function ch(n,k){
  if(k<0||k>n)return 0n;let v=1n;
  for(let i=1;i<=k;i++)v=v*BigInt(n-i+1)/BigInt(i);
  return v;
}
function qgen(n,x,j){
  const R=[I,x];
  for(let k=1;k<j;k++)R.push(D(S(M(Q(2*k+n-2),M(x,R[k])),M(Q(k),R[k-1])),Q(k+n-2)));
  return R;
}
function pol(n,coef,x){
  const u=qgen(n,x,Math.max(...coef.map(([j])=>j)));
  return A(I,sum(coef.map(([j,c])=>M(c,u[j]))));
}
function angles(a,ant){
  const B=Number(floor(S(M(Q(2),a),ant?I:Q(3,2))));
  return Array.from({length:B},(_,i)=>{
    const w=S(a,Q(i+1));return ant?D(abs(w),a):D(w,a);
  });
}
function shell(n,a,coef,h,ant,groups){
  const ex=D(S(a,I),a);
  for(const t of angles(a,ant))if(C(t,ex)!==0n)nonpos(pol(n,coef,t));
  const b=A(pol(n,coef,I),M(M(Q(h),a),max([Z,pol(n,coef,ex)])));
  return ceil(M(Q(groups),b));
}
// Exact polynomial interpolation bound on a sphere of squared radius a,
// when pair differences have even squared length >=2.
function residual(d,a){
  if(d===0||C(a,Q(1,2))<0n)return 1n;
  if(C(a,I)<=0n){
    if(C(a,I)===0n)return BigInt(2*d);
    const z=floor(D(I,S(I,a)));return z<BigInt(2*d)?z:BigInt(2*d);
  }
  const j=Number(floor(M(Q(2),a)));
  return ch(d+j,j)-ch(d+j-2,j-2);
}
function proj(n,r,a,shadow){
  const m=r+1,d=n-r,K=Number(floor(M(Q(2),a)));
  const maxM=Number(floor(A(a,Q(K*K,m))));
  const kstr=(k,b)=>k+','+b;
  let p=new Map([['0,0',1n]]);
  for(let i=0;i<m;i++){
    const out=new Map();
    for(const [tag,N] of p){
      const [k,b]=tag.split(',').map(Number);
      let R=0;while((R+1)*(R+1)+b<=maxM)R++;
      for(let v=-R;v<=R;v++){
        const key=kstr(k+v,b+v*v);out.set(key,(out.get(key)||0n)+N);
      }
    }
    p=out;
  }
  let total=0n;
  for(let k=0;k<=Math.min(K,Math.floor(m/2));k++)for(let b=k;b<=maxM;b+=2){
    const L=S(A(a,Q(k*k,m)),Q(b));
    if(L[0]<0n)continue;
    const v=(p.get(kstr(k,b))||0n)*BigInt(k?2:1);
    // Only split the two shadow cosets if the residual radius exceeds 1.
    // At smaller radii a bound using separation alone applies to their union.
    let U=residual(d,L);
    if(shadow&&C(L,I)>0n)U*=2n;
    if(!shadow&&!k&&!b&&C(L,I)>0n){
      const j=2*(Number(floor(L))-1); // here L is the original integer a=4 or 6
      const antipodal=2n*ch(d+j-1,j);
      if(d&&antipodal<U)U=antipodal;
    }
    total+=v*U;
  }
  return total;
}
// Odd ranks: fixed rational coefficients, in order of nonzero degree.
const tbl4={"42":[[4,410]],"43":[[1,2.1],[5,1500]],"44":[[2,13.6],[6,4250]],"45":[[1,0.14],[3,69],[7,11800]],"46":[[4,290],[8,30500]],"47":[[1,0.21],[3,6.5],[5,1060],[9,81000]],"48":[[4,15.6],[6,3800],[10,200000]],"49":[[1,0.04],[3,9.99],[5,132],[7,11450],[11,510000]],"50":[[6,550],[8,35620],[12,1198000]],"51":[[1,0.0134],[3,1.95],[5,204.08],[7,1706.8],[9,96610],[13,2945840]],"52":[[6,661.3],[8,5884],[10,272911],[14,6971645]],"53":[[1,0.00371],[3,0.9183],[5,47.45],[7,2723.23],[9,17279.1],[11,719203],[15,16570221]],"54":[[8,8071.43],[10,56221.3],[12,1921954],[16,38488265]],"55":[[8,66.5034],[9,17633.21],[10,1041.59],[11,73866.61],[12,3277.2],[13,4580469],[17,90995200]]},tbl5={"50":[[4,505]],"51":[[1,2.8646],[5,1982.64]],"52":[[2,19.614],[6,6099.53]],"53":[[2,4.00732],[3,83.7481],[7,17743.27]],"54":[[4,385.45],[8,47562.55]],"55":[[1,0.022464],[2,5.87852],[5,1374.54],[9,136811.52]]};
const small5=[2,2,88,92,4324,2352,9024,44200],small6=[2,2,104,108,5940,3192];
function cert(T,s){return T.map(([j,c])=>[j,M(rat(c),s)]);}
function coeff2(n,j){return Q((n-24*j)**2-(n+24*j),2);}
function U5(n){
  const d=120-n;return max([Z,A(A(coeff2(n,5),Q(d*(n-96))),Q(d*d,4))]);
}
function U6(n){
  const p=n-48,b=48;
  const t=ch(p,3)+BigInt(p)-2n*BigInt(b)*ch(p,2)+4n*ch(b,2)*BigInt(p)-8n*ch(b,3);
  const R=S(Q((120-n)*(144-n)),coeff2(n,6));
  const c0=A(A(M(Q(n-96),R),M(Q(144-n),coeff2(n,5))),Q(t));
  const c1=M(Q(64),R),c2=Q(-(144-n)*4096),c3=Q(262144);
  return max([Z,c0,A(c0,D(c1,Q(3))),A(c0,D(A(M(Q(2),c1),c2),Q(3))),sum([c0,c1,c2,c3])]);
}
function odd(n,root,h,B4,B5,B6){
  const T=M(pow(Q(2),24-n),sum([Q(B4*BigInt(n-32)),M(Q(B5),U5(n)),B6?M(Q(B6),U6(n)):Z]));
  const slack=S(S(Q(2*n),Q(root+BigInt(2*n*n-46*n),64)),T);
  pos(slack);return Number(slack[0])/Number(slack[1]);
}
const oddRows=[];
for(let n=42;n<=55;n++){
  const even=n%2===0,groups=even?4:2,h=n===54?48:n===55?52:n+1;
  const c4=cert(tbl4[n],n===49?Q(103,100):n===50?Q(21,20):n>=51?Q(203,200):I);
  const B4=shell(n,Q(n-32,4),c4,h,even,groups);
  const B5=n<50?BigInt(small5[n-42]):shell(n,Q(n-40,4),cert(tbl5[n],Q(203,200)),n+1,even,groups);
  const B6=n<50?0n:BigInt(small6[n-50]);
  const row=[n,String(B4),String(B5),String(B6),odd(n,BigInt(n*h),h,B4,B5,B6)];
  oddRows.push(row);
  if(n===54){
    for(let r=48;r<=54;r++){
      const d=n-r, root=BigInt(r*(r+1)+d*Math.max(30,d+1,2*(d-1)));
      const h=r+1,B=r===48?shell(n,Q(n-32,4),c4,h,true,4):proj(n,r,Q(n-32,4),true);
      oddRows.push(['A'+r,String(B),String(B5),String(B6),odd(n,root,h,B,B5,B6)]);
    }
  }
  if(n===55){
    for(let r=52;r<=54;r++){
      const d=n-r,root=BigInt(r*(r+1)+d*(d+1));
      const H=r+1,B=r<=53?shell(n,Q(n-32,4),c4,H,false,2):proj(n,r,Q(n-32,4),true);
      oddRows.push(['A'+r+' (55)',String(B),String(B5),String(B6),odd(n,root,H,B,B5,B6)]);
    }
  }
}
console.log('odd bounds and certified positive margins',JSON.stringify(oddRows));
// Rank 72. Solve the small linear systems giving the exact spherical
// certificates, rather than depending on rounded LP output.
function solve(a,b){
  const n=b.length,m=a.map((r,i)=>r.concat([b[i]]));
  for(let i=0;i<n;i++){
    const j=m.findIndex((r,j)=>j>=i&&r[i][0]);assert(j>=i);
    [m[i],m[j]]=[m[j],m[i]];
    for(let j=0;j<n;j++)if(i!==j){
      const f=D(m[j][i],m[i][i]);
      for(let k=i;k<=n;k++)m[j][k]=S(m[j][k],M(f,m[i][k]));
    }
  }
  return m.map((r,i)=>D(r[n],r[i]));
}
function interpolate(deg,n,X){
  const a=X.map(x=>{const q=qgen(n,x,Math.max(...deg));return deg.map(j=>q[j]);});
  const w=solve(a,X.map(()=>Q(-1)));w.forEach(pos);return deg.map((k,i)=>[k,w[i]]);
}
const E4=interpolate([2,6,10],72,[Z,Q(1,4),Q(1,2)]);
const E6=interpolate([2,4,10,18],72,[Z,Q(1,6),Q(1,3),Q(2,3)]);
// Positivity of the linear coefficients of N2,N4,N6.
pos(S(Q(27,64),Q(1416,4096)));pos(S(Q(27,64),Q(672,4096)));
gte(672*1416,842652);
const Padd=(a,b)=>Array.from({length:Math.max(a.length,b.length)},(_,i)=>A(a[i]||Z,b[i]||Z));
const Pmul=(a,b)=>{
  const r=Array(a.length+b.length-1).fill(Z);
  for(let i=0;i<a.length;i++)for(let j=0;j<b.length;j++)r[i+j]=A(r[i+j],M(a[i],b[j]));
  return r;
};
const Ppow=(a,n)=>n?Pmul(a,Ppow(a,n-1)):[I];
const scale=(a,s)=>a.map(c=>M(c,s));
function hpoly(r2,r4,r6){
  const c1=r2-2160n,c2=r4-2093040n-1416n*c1,
    c3=r6-1198601280n-842652n*c1-672n*c2;
  const e=[Q(3,4),Q(1,4)],v=[Q(1,4),Q(-1,4)];
  let p=[Z];
  for(let j=0;j<=8;j++)p=Padd(p,Ppow(e,j));
  p=Padd(p,scale(Pmul(Ppow(e,6),v),Q(-c1,256)));
  p=Padd(p,scale(Pmul(Ppow(e,3),Ppow(v,3)),Q(-c2,65536)));
  p=Padd(p,scale(Ppow(v,5),Q(-c3,16777216)));
  return p;
}
const evenRows=[];
for(let r=49;r<=72;r++){
  // r=49 represents the whole h<=50 case, not an assumed A49 component.
  const d=72-r,h=r+1,r2=r===49?3600n:BigInt(r*(r+1)+d*Math.max(30,d+1,2*(d-1)));
  let r4=shell(72,Q(4),E4,h,true,2),r6=shell(72,Q(6),E6,h,true,2);
  if(r>=50){const B4=proj(72,r,Q(4),false),B6=proj(72,r,Q(6),false);
    if(B4<r4)r4=B4;if(B6<r6)r6=B6;}
  const p=hpoly(r2,r4,r6);
  const bern=Array.from({length:9},(_,i)=>sum(p.slice(0,i+1).map((v,j)=>M(v,Q(ch(i,j),ch(8,j))))));
  bern.forEach(pos);
  const min=bern.reduce((x,y)=>C(x,y)<0n?x:y);
  evenRows.push([r,String(r2),String(r4),String(r6),Number(min[0])/Number(min[1])]);
}
console.log('even rank 72: case, N2, N4, N6, minimum Bernstein coefficient',JSON.stringify(evenRows));
console.log('PASS',checks,'exact spherical/positivity assertions');
