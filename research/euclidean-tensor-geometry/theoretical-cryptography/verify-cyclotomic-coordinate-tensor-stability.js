/* Node 18+. Exact arithmetic on synthetic projected tensor configurations. */
'use strict';
let exact=0;
function ck(t,msg){++exact;if(!t)throw Error(msg);}
function inner(v,w,p=3,q=5) {
  return v.reduce((s,[i,j,a])=>s+w.reduce((t,[l,k,b])=>
    t+a*b*(p*Number(i===l)-1)*(q*Number(j===k)-1),0),0);
}
const all=[];
for(let i=0;i<3;++i)for(let j=0;j<5;++j)all.push([[i,j,1]]);
for(let i=0;i<3;++i)for(let j=0;j<5;++j)for(let k=j+1;k<5;++k)
  all.push([[i,j,1],[i,k,1]]);
for(let i=0;i<3;++i)for(let l=i+1;l<3;++l)
for(let j=0;j<5;++j)for(let k=0;k<5;++k)if(j!==k)
  all.push([[i,j,1],[l,k,-1]]);
ck(all.length===105,'total sign classes in 3-by-5 shell');
for(let i=0;i<all.length;++i)for(let j=0;j<=i;++j) {
  if(i===j) ck(inner(all[i],all[i])===(i<15?8:i<45?12:14),'shell norm');
  else ck(Math.abs(inner(all[i],all[j]))!==inner(all[i],all[i])||
          inner(all[i],all[i])!==inner(all[j],all[j]),'distinct sign classes');
}
function psd(a) {
  while(a.length) {
    const p=a[0][0];
    if(p<0n) return false;
    if(p===0n) {
      if(a[0].some(t=>t!==0n))return false;
      a=a.slice(1).map(row=>row.slice(1));
    } else {
      a=a.slice(1).map((row,i)=>row.slice(1).map((x,j)=>p*x-a[i+1][0]*a[0][j+1]));
    }
  }
  return true;
}
const d=all.map((v,i)=>all.map((w,j)=>BigInt((i===j?15:0)-inner(v,w))));
function contracted(indices) {return psd(indices.map(i=>indices.map(j=>d[i][j])));}
function search(start,allowed) {
  const c=allowed.filter(i=>i!==start&&contracted([start,i]));
  let tested=0;
  function visit(chosen,next) {
    if(chosen.length===8)return true;
    for(let j=next;j<c.length;++j) {
      const t=[...chosen,c[j]];
      ++tested;
      if(contracted(t)&&visit(t,j+1))return true;
    }
    return false;
  }
  const found=visit([start],0);
  ck(!found,'no contracted 8-column prefix extension with a nonshort vector');
  return [c.length,tested];
}
const medium=search(15,Array.from({length:45},(_,i)=>i));
const long=search(45,Array.from({length:105},(_,i)=>i));
ck(medium[0]===31&&long[0]===21,'exact compatibility counts');
console.log('3-by-5 search extensions:',medium[1],long[1]);
const med7=[[0,0,1],[0,1,1]];
let eligible=0;
for(let i=0;i<3;++i)for(let j=0;j<7;++j) {
  const u=inner(med7,[[i,j,1]],3,7);
  const ok=u*u<=9;
  ck(ok===(i!==0&&j>=2),'3-by-7 mixed compatibility exact');
  eligible+=Number(ok);
  for(let k=j+1;k<7;++k) {
    const z=inner(med7,[[i,j,1],[i,k,1]],3,7);
    ck(Math.abs(z)>=3,'3-by-7 contracted mediums cannot coexist');
  }
}
ck(eligible===10,'3-by-7 exact admissible short count');
function grid(dim) {
  let a=[[]];
  for(const d of dim)a=a.flatMap(x=>Array.from({length:d},(_,j)=>[...x,j]));
  return a;
}
function idx(x,dim){return x.reduce((s,v,i)=>s*dim[i]+v,0);}
let seed=1905770801;
function rnd(n){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>6)%n;}
for(const dim of [[2,3],[3,5],[2,3,4],[3,5,7],[2,3,4,5],[2,2,2,2,2]]) {
  const x=grid(dim),k=dim.length,M=x.length;
  const grams=x.map(a=>x.map(b=>a.reduce((s,e,i)=>s*(dim[i]*Number(e===b[i])-1),1)));
  for(let trial=0;trial<18;++trial) {
    const a=x.map(()=>rnd(15)-7);
    const gn=a.reduce((s,u,i)=>s+a.reduce((t,v,j)=>t+u*v*grams[i][j],0),0);
    let normSum=0,min=Infinity;
    for(const base of x) {
      let norm=0;
      for(const y of x) {
        let w=0;
        for(let mask=0;mask<(1<<k);++mask) {
          let parity=0;
          const z=y.map((v,i)=>{if(mask>>i&1){parity^=1;return base[i];}return v;});
          w+=(parity?-1:1)*a[idx(z,dim)];
        }
        norm+=w*w;
      }
      normSum+=norm;min=Math.min(min,norm);
    }
    ck(normSum===(1<<k)*gn,'simultaneous anchor mean exact');
    ck(min*M<=(1<<k)*gn,'small representative exists');
  }
}
for(let k=2n;k<=64n;++k) {
  const n=1n<<k,p=n+2n;
  ck(3n*k<=p,'uniform factor diagonal lower bound');
  for(const h of [2n,n]) ck(5n*h*(p-h)>=8n*(p-1n),'concave endpoint lower bound');
}
const fixtures=[[3,11,13],[5,11,13],[5,7,37],[3,5,37],[3,7,29]];
for(const [p,q,r] of fixtures) {
  ck(2*(r-2)*(p-1)*(q-1)>r*p*q,'one-slice threshold exact');
  ck(2*(p-1)*(q-1)*(r-1)>p*q*r,'orthogonal block cannot mix');
}
ck(36*36>35*37&&12*12>11*13,'next pair degree inequalities');
ck(3**3*10**3>11**3*4**2,'higher tensor rank bound');
ck(4*3*100>7*121,'rank-two bound, p>=5');
console.log('cyclotomic tensor coordinate stability:',exact,'exact checks');
