'use strict';
// Verification on abstract Gaussian probability laws only.
function assert(p,m){if(!p)throw Error(m);}
function range(n){return [...Array(2*n+1)].map((_,i)=>i-n);}
function qterm(x,y,r){return (x*x+y*y-2*r*x*y)/(2*(1-r*r));}
function lse(xs){let m=Math.max(...xs);return m+Math.log(xs.reduce((a,x)=>a+Math.exp(x-m),0));}
function eig(a){
  let n=a.length;
  for(let sw=0;sw<100;sw++){
    let m=0;
    for(let i=0;i<n;i++)for(let j=i+1;j<n;j++){
      let v=a[i][j];m=Math.max(m,Math.abs(v));
      if(Math.abs(v)<2e-16)continue;
      let d=(a[j][j]-a[i][i])/(2*v),t=(d<0?-1:1)/(Math.abs(d)+Math.hypot(d,1));
      let c=1/Math.hypot(1,t),s=t*c;
      a[i][i]-=t*v;a[j][j]+=t*v;a[i][j]=a[j][i]=0;
      for(let k=0;k<n;k++)if(k!==i&&k!==j){
        let x=a[i][k],y=a[j][k];a[i][k]=a[k][i]=c*x-s*y;a[j][k]=a[k][j]=s*x+c*y;
      }
    }
    if(m<5e-15) return a.map((row,i)=>row[i]).sort((x,y)=>y-x);
  }
  throw Error("Jacobi convergence");
}
function prob(r,h,k,x0=0,y0=0){
 let X=range(Math.max(3,Math.ceil(14/h))).map(i=>h*i+x0);
 let Y=range(Math.max(3,Math.ceil(14/k))).map(i=>k*i+y0);
 let W=X.map(x=>Y.map(y=>-qterm(x,y,r)));
 let mx=W.map(lse),my=Y.map((_,j)=>lse(W.map(row=>row[j])));
 let A=W.map((row,i)=>row.map((a,j)=>Math.exp(a-(mx[i]+my[j])/2)));
 return {X,Y,W,A,mx,my};
}
function squared(A){let l=A[0].length;return eig(Array.from({length:l},(_,i)=>Array.from({length:l},(_,j)=>A.reduce((z,row)=>z+row[i]*row[j],0))));}
function theta(a){let z=0;for(let j=1;j<1000;j++){let t=Math.exp(-a*j*j);z+=2*t;if(t<1e-30)break;}return z;}
let exact=0,num=0,maxDev=0,maxAsym=0,maxLow=0;
for(let b=3;b<=29;b++)for(let a=1;a<b;a++){
 let threshold=Math.min(b,2*(b-a));
 let got=[];
 for(let m=-12;m<=12;m++)for(let n=-12;n<=12;n++){
   if(!m&&!n)continue;
   let q=b*(m*m+n*n)+2*a*m*n;
   assert(q>=threshold,'shortest shell');exact++;
   if(q===threshold)got.push([m,n]);
 }
 assert(got.length===(2*a===b?6:2*a<b?4:2),'multiplicity');exact++;
 let mat=got.reduce(([u,v,w],[m,n])=>[u+m*m,v+m*n,w+n*n],[0,0,0]);
 let [u,v,w]=mat;
 let left=b*(b*b*v+a*b*(u+w)+a*a*v)-a*(b*b*u+2*a*b*v+a*a*w);
 let expected=(2*a<b?2*a*(b*b-a*a):2*a>b?-2*(b+a)*(b-a)**2:0);
 assert(left===expected,'leading coefficient');exact++;
}
for(let rn of [0,.15,.35,.5,.7,.85,.95]) for(let hu of [.8,1.1,1.6,2.0]) for(let kv of [.9,1.4,1.8]){
 let u=Math.sqrt(rn),v=rn===0?0:rn/u;
 for(let [x0,y0] of [[0,0],[.31*hu,-.19*kv]]){
   let {A}=prob(rn,hu,kv,x0,y0),l=squared(A);
   let ex=theta(2*Math.PI**2*(1-u*u)/(1+u*u)/hu**2),ey=theta(2*Math.PI**2*(1-v*v)/(1+v*v)/kv**2);
   let bx=theta(2*Math.PI**2*(1-rn**2)/hu**2),by=theta(2*Math.PI**2*(1-rn**2)/kv**2);
   let D=ex+ey+ex*ey;
   for(let j=0;j<Math.min(10,l.length);j++){
      let e=rn**(2*j),lower=Math.max(0,e-D)/((1+bx)*(1+by)),upper=(bx<1&&by<1)?(e+D)/((1-bx)*(1-by)):Infinity;
      assert(l[j]>=lower-3e-13&&l[j]<=upper+3e-13,'finite-width bound');
      if(j>0)maxDev=Math.max(maxDev,Math.abs(l[j]-e)/(D+bx+by));
      num++;
   }
 }
}
for(let r of [.09,.19,.31,.42,.58,.67,.79,.91]) {
 let d=Math.min(1,2*(1-r));
 let b=(r<.5?-2*r*(1-r*r):2*(1+r)*(1-r)**2);
 for(let z of [14,17,20]){
   let h=Math.sqrt(2*Math.PI**2*d/z),{A,W,X,mx}=prob(r,h,h);
   let eigen=eig(A.map(row=>[...row]))[1];
   let [c,v]=W.reduce(([c,v],row,i)=>[c+row.reduce((z,l,j)=>z+X[i]*X[j]*Math.exp(l),0),v+X[i]**2*Math.exp(mx[i])],[0,0]);
   let pear=c/v,t=2*Math.PI/h,lead=t*t*b*Math.exp(-z),rel=(eigen-r)/lead;
   assert(Math.sign(eigen-r)===Math.sign(lead),'leading sign');
   assert(Math.abs(rel-1)<.27,'leading coefficient at finite scale');
   assert(eigen>=pear-1e-13,'variance principle');
   maxAsym=Math.max(maxAsym,Math.abs(rel-1));num+=3;
 }
}
for(let h of [.7,1.3,2,3,4,8,16,28]){
 let {A}=prob(.5,h,h),l=eig(A);
 assert(Math.abs(l[1]-.5)<2e-13,'exact critical rate');num++;
}
for(let r of [.11,.22,.34,.43,.48,.52,.57,.65,.8,.92]){
 let d=(1-2*r)/(2*(1-r*r));
 let h=Math.sqrt(12/Math.abs(d)),{A}=prob(r,h,h),l=eig(A);
 if(r<.5){let e=Math.exp(-12);maxLow=Math.max(maxLow,Math.abs(l[1]/e-1));assert(Math.abs(l[1]/e-1)<.08,'low-temp coefficient');}
 if(r>.5)assert(l[1]>1-3e-5,'low-temp locking');
 num++;
}
console.log(JSON.stringify({exact,num,maxDev,maxAsym,maxLow}));
