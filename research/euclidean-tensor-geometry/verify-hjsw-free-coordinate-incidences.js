'use strict';
// Small-field exact physical/free-coordinate incidence check, no packages.
const gcd=(a,b)=>b?gcd(b,a%b):a;
let boards=0,weightInstances=0,goodRoots=0,nonzeroGood=0,boundedLoads=0;
function insist(x,m){if(!x)throw Error(m);}
for (const p of [23,31,41,53,67,79]) {
 const m=x=>((x%p)+p)%p, h=(p-1)/2;
 const inv=[0];for(let x=1;x<p;x++)for(let y=1;y<p;y++)if(m(x*y)===1){inv[x]=y;break;}
 for(const gamma of [1,7]){
  boards++;
  const n=2*p,J=(x)=>x>=h+1&&x<=h+p, contains=(x,y)=>x>=0&&x<n&&y>=0&&y<n&&!(J(x)&&J(y))&&m((x-h)*y)===m(gamma);
  const points=[];for(let x=0;x<n;x++)for(let y=0;y<n;y++)if(contains(x,y))points.push([x,y]);
  insist(points.length===3*(p-1),'frame size');
  for(let b=1;b<=3;b++)for(let a=-10*b;a<=-5*b;a++){
   if(gcd(-a,b)!==1||!m(a)||!m(b-a))continue;
   const t=m(a*inv[b]), q=m(1-t), al=m((1-2*t)**2);
   if(!al||al===1)continue;
   weightInstances++;
   const brute=new Uint8Array(n*n), free=new Uint8Array(n*n);
   for(const A of points)for(const B of points){
     if(A===B)continue;
     const x=((b-a)*A[0]+a*B[0])/b,y=((b-a)*A[1]+a*B[1])/b;
     if(Number.isInteger(x)&&Number.isInteger(y)&&x>=0&&y>=0&&x<n&&y<n)brute[x*n+y]++;
   }
   let maxv=Math.floor((n-1)/(-a));
   for(let x=0;x<n;x++)for(let y=0;y<n;y++){
    if(!m(x-h)||!m(y))continue;
    const u=m(x-h),c=m(u*y*inv[m(gamma)]);
    if(c===1||c===al)continue;
    goodRoots++;
    let count=0;
    for(let r=1;r<p;r++)if(m(q*c*r*r-(c+1-2*t)*r+q)===0){
     const ax=m(u*r),ay=m(gamma*inv[ax]), v0=m((ax-u)*inv[m(a)]), v1=m((ay-y)*inv[m(a)]);
     let vx=v0,vy=v1;
     if(vx>maxv)vx-=p;if(vy>maxv)vy-=p;
     if(vx< -maxv||vy< -maxv)continue;
     if(contains(x+a*vx,y+a*vy)&&contains(x-(b-a)*vx,y-(b-a)*vy))count++;
    }
    free[x*n+y]=count;
    insist(count===brute[x*n+y]&&count<=2,'incidence disagreement');
    if(count)nonzeroGood++;
   }
   boundedLoads+=brute.reduce((v,w)=>v+w,0);
  }
 }
}
console.log(JSON.stringify({boards,weightInstances,goodRoots,nonzeroGood,boundedLoads}));
