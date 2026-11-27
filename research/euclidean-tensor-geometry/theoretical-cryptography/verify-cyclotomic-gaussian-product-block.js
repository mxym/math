"use strict";
// Deterministic standalone algebra and normalizations. No cryptographic data.
let exact=0,numeric=0;
function chk(a,msg) { if(!a) throw new Error(msg); ++exact; }
function near(a,b,r,msg) {
  if (!Number.isFinite(a) || !Number.isFinite(b) ||
      Math.abs(a-b)>r*Math.max(1,Math.abs(a),Math.abs(b))) {
    throw new Error(msg+": "+a+" vs "+b);
  }
  ++numeric;
}
const dot=(a,b)=>a.reduce((s,x,j)=>s+x*b[j],0);
const matrix=(d,f)=>Array.from({length:d},(_,i)=>
                     Array.from({length:d},(_,j)=>f(i,j)));
const transpose=A=>matrix(A.length,(i,j)=>A[j][i]);
const mm=(A,B)=>{const C=transpose(B); return matrix(A.length,(i,j)=>dot(A[i],C[j]));};
const plus=(A,B)=>matrix(A.length,(i,j)=>A[i][j]+B[i][j]);
const minus=(A,B)=>matrix(A.length,(i,j)=>A[i][j]-B[i][j]);
const ident=d=>matrix(d,(i,j)=>+(i===j));
const pi=Math.PI, sin=Math.sin, cos=Math.cos;
function rects(k) {
  const R=[];
  for(let i=0;i<k;i++) for(let j=i+1;j<k;j++) for(let h=j+1;h<k;h++) {
    const l=j+h-i;
    if(l<k) R.push([i,j,h,l]);
  }
  return R;
}
function gaps(k) {
  const R=[];
  for(let u=1;2*u+1<k;u++) for(let v=1;2*u+v<k;v++)
    R.push([u,v,k-2*u-v]);
  return R;
}
for(let k=1;k<=43;k++) {
  const N=rects(k).length;
  chk(gaps(k).reduce((x,i)=>x+i[2],0)===N,"exact rectangle formula");
  chk(Math.abs(k**3-12*N)<=20*k*k,"rectangle asymptotic error");
  let distinct=0, repeated=0, trABABNum=0;
  for(let i=0;i<k;i++) for(let j=0;j<k;j++)
  for(let h=0;h<k;h++) for(let l=0;l<k;l++) {
    const path=(Math.abs(i-j)===Math.abs(h-l) && Math.abs(j-h)===Math.abs(l-i));
    const dis=i!==j && i!==h && i!==l && j!==h && j!==l && h!==l;
    if(dis) {
      if(path) ++distinct;
      if((i+h===j+l)!==path) throw new Error("closed path condition");
    } else if(path) ++repeated;
    if(path) trABABNum+=(i===j?2:1)*(j===h?2:1); // multiply expectation by 4m^2
  }
  chk(distinct===8*N,"eight oriented overlaps per rectangle");
  chk(repeated<=6*k*k,"repeated vertices");
  chk(trABABNum>=8*N&&trABABNum-8*N<=24*k*k,"trace ABAB constant");
  const trABVarNum=k*k+(k-1)*k*(2*k-1)/6;
  chk(Math.abs(trABVarNum-4*N)<=12*k*k,"trace AB variance constant");
  // Matrix H of equation (10), multiplied by 2 to make entries integral.
  const H=matrix(k,()=>0);
  for(const [u,v,fac] of gaps(k)) {
    H[u][u]+=2*fac; H[u+v][u+v]+=2*fac;
    H[v][2*u+v]+=fac; H[2*u+v][v]+=fac;
  }
  for(let i=0;i<k;i++) for(let j=0;j<k;j++)
    chk(i===j?H[i][j]<=4*k*k:H[i][j]<=k,"conditional mean quadratic form");
  chk(H.reduce((s,r)=>s+dot(r,r),0)<=17*k**5,"conditional mean Frobenius");
}
function perms(a) {
 if(a.length<=1) return [a];
 return a.flatMap((x,j)=>perms(a.filter((_,i)=>i!==j)).map(v=>[x,...v]));
}
for(let k=4;k<=24;k++) {
  const Rp=rects(k).flatMap(v=>perms(v));
  for(let r=1;r<=3;r++) {
    const rows=new Map(),cols=new Map();
    for(const v of Rp) {
      const a=v.slice(0,r).join(), b=v.slice(r).join();
      rows.set(a,(rows.get(a)||0)+1); cols.set(b,(cols.get(b)||0)+1);
    }
    const max=(map)=>Math.max(...map.values());
    chk(max(rows)<=2*3*k**(3-r),"row sum bound");
    chk(max(cols)<=2*3*k**(r-1),"column sum bound");
  }
}
function prod(a,b) {
 const d=a.length,out=new Array(d).fill(0);
 for(let i=0;i<d;i++)for(let j=0;j<d;j++)
   out[(i+j)%d]+=(i+j<d?1:-1)*a[i]*b[j];
 return out;
}
function slots(a) {
 const m=a.length/2;
 return Array.from({length:m},(_,j)=>{
  const th=(2*j+1)*pi/(2*m);
  return [a.reduce((x,v,i)=>x+v*cos(i*th),0)/Math.sqrt(m),
          a.reduce((x,v,i)=>x+v*sin(i*th),0)/Math.sqrt(m)];
 });
}
for(const m of [4,8,16,32]) {
 const d=2*m,theta=Array.from({length:m},(_,j)=>(2*j+1)*pi/d);
 for(let k=1;k<=m;k++) for(let h=0;h<k;h++)for(let l=0;l<k;l++)
   near(theta.reduce((x,t)=>x+cos(h*t)*cos(l*t),0),
         h===l?(h===0?m:m/2):0,2e-11,"cosine orthogonality");
 for(let j=0;j<11;j++) {
   const a=Array.from({length:d},(_,i)=>sin(2.1*(j+1)*(i+2))-0.6*cos(0.2*i*i));
   const b=Array.from({length:d},(_,i)=>cos(1.1*(j+2)*(i+1))+0.2*sin(0.3*i*i));
   const x=slots(a),y=slots(b),z=slots(prod(a,b).map(t=>t/Math.sqrt(d)));
   const ww=x.map(t=>dot(t,t)/2);
   for(let h=0;h<m;h++) {
     near(z[h][0],(x[h][0]*y[h][0]-x[h][1]*y[h][1])/Math.sqrt(2),8e-12,
                 "real slot product");
     near(z[h][1],(x[h][0]*y[h][1]+x[h][1]*y[h][0])/Math.sqrt(2),8e-12,
                 "imaginary slot product");
   }
   const rows=Array.from({length:m},()=>new Array(d).fill(0));
   for(let z=0;z<d;z++) {
     const e=new Array(d).fill(0); e[z]=1;
     const eprod=prod(a,e);
     for(let i=0;i<m;i++) rows[i][z]=eprod[i]/Math.sqrt(d);
   }
   const vals=theta.map((_,h)=>theta.reduce((s,t,z)=>s+ww[z]*cos(h*t),0)/m);
   for(let i=0;i<m;i++) for(let l=0;l<m;l++)
     near(dot(rows[i],rows[l]),vals[Math.abs(i-l)],5e-12,"conditional covariance");
   const R=rects(m), gapsSum=gaps(m).reduce((t,[u,v,n])=>
     t+n*(vals[u]**2+vals[u+v]**2+vals[2*u+v]*vals[v]),0);
   const direct=R.reduce((t,[i,j,h,l])=>t+vals[j-i]*vals[l-h]+vals[h-i]*vals[l-j]+
       vals[l-i]*vals[h-j],0);
   near(gapsSum,direct,1e-11,"three Wick pairings");
 }
}
function sweep(A) {
 const d=A.length;
 const M=A.map((x,i)=>x.concat(ident(d)[i])); let det=1;
 for(let i=0;i<d;i++) {
   let piv=i;
   for(let j=i+1;j<d;j++) if(Math.abs(M[j][i])>Math.abs(M[piv][i]))piv=j;
   if(piv!==i) { const x=M[piv]; M[piv]=M[i]; M[i]=x; det=-det; }
   const a=M[i][i]; det*=a;
   for(let j=i;j<2*d;j++) M[i][j]/=a;
   for(let j=0;j<d;j++) if(j!==i) {
     const b=M[j][i];
     for(let h=i;h<2*d;h++) M[j][h]-=b*M[i][h];
   }
 }
 return {det,inv:M.map(x=>x.slice(d))};
}
for(let k=1;k<=9;k++)for(let p=1;p<=40;p++) {
 const I=ident(k), A=matrix(k,(i,j)=>0.3*sin((Math.abs(i-j)+1)*p)/k),
       B=matrix(k,(i,j)=>0.3*cos((Math.abs(i-j)+1)*(p+1))/k);
 const U=plus(I,A),V=plus(I,B), invU=sweep(U),invV=sweep(V),
       precision=minus(plus(invU.inv,invV.inv),I),D=minus(I,mm(A,B)),
       Puv=mm(mm(U,precision),V);
 for(let i=0;i<k;i++)for(let j=0;j<k;j++)
   near(Puv[i][j],D[i][j],5e-13,"Gaussian overlap precision");
 near(invU.det*invV.det*sweep(precision).det,sweep(D).det,5e-13,
      "Gaussian overlap determinant");
}
console.log(exact+" exact combinatorial checks; "+numeric+
            " deterministic numerical checks: PASS");
