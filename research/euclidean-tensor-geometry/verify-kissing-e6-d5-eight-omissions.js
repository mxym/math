function dot(a, b) {
  return a.reduce((sum,v,i)=>sum+v*b[i],0n);
}

// Fraction-free determinant with exact row pivoting.
function det(rows) {
  const a=rows.map(row=>row.slice());
  let sign=1n, prev=1n;
  for(let j=0;j<a.length-1;j++){
    const pivot=a.findIndex((row,i)=>i>=j&&row[j]!==0n);
    if(pivot<0)return 0n;
    if(pivot!==j){[a[j],a[pivot]]=[a[pivot],a[j]];sign=-sign;}
    for(let i=j+1;i<a.length;i++)for(let k=j+1;k<a.length;k++){
      const num=a[i][k]*a[j][j]-a[i][j]*a[j][k];
      if(num%prev!==0n)throw Error('division');
      a[i][k]=num/prev;
    }
    for(let i=j+1;i<a.length;i++)a[i][j]=0n;
    prev=a[j][j];
  }
  return sign*a.at(-1).at(-1);
}

const R=Array.from({length:5},(_,i)=>Array.from({length:5-i-1},(_,n)=>[1,-1].map(sign=>Array.from({length:5},(_,k)=>k===i?1:k===i+1+n?sign:0)))).flat(2);
const roots=R.concat(R.map(v=>v.map(x=>-x)));const I=[0,1,2,3,4,5],basis=I.map(i=>I.map(j=>i===j?1n:0n));
const B=R.map(r=>I.map(i=>i===5?0n:BigInt(r.slice(0,i+1).reduce((x,y)=>x+y,0))));
const ids=R.map((_,i)=>i),maximal=C=>C.filter(i=>!C.some(j=>i!==j&&B[j].every((x,k)=>x>=B[i][k]))),minimal=C=>C.filter(i=>!C.some(j=>i!==j&&B[j].every((x,k)=>x<=B[i][k])));
function vertices(C,cap=false){
 const N=maximal(ids.filter(i=>!C.includes(i))),P=minimal(C);const rows=basis.map(v=>v.map(x=>-x)).concat(N.map(i=>B[i]),P.map(i=>B[i].map(x=>-x)),[[1n,2n,3n,4n,3n,1n]]),rhs=basis.map(()=>0n).concat(N.map(()=>1n),P.map(()=>-1n),[2n]),map=new Map();if(cap){rows.push([1n,1n,1n,1n,1n,0n]);rhs.push(1n);}
 const walk=(A,from)=>{if(A.length!==6){for(let i=from;i<=rows.length-6+A.length;i++)walk(A.concat([i]),i+1);return;}
 const M=A.map(i=>rows[i]),v=A.map(i=>rhs[i]);let D=det(M);if(!D)return;let nums=I.map(k=>det(M.map((r,i)=>r.map((x,j)=>j===k?v[i]:x))));if(D<0n){D=-D;nums=nums.map(x=>-x);}if(rows.some((r,i)=>dot(r,nums)>rhs[i]*D))return;
 const gcd=(a,b)=>b?gcd(b,a%b):a;const g=nums.reduce((g,x)=>gcd(g,x),D);nums=nums.map(x=>x/g);D/=g;const a=I.map(i=>i===5?nums[5]:nums.slice(i,5).reduce((v,w)=>v+w,0n));map.set(String(a)+'/'+D,{a,D});
 };walk([],0);return [...map.values()];
}
const q=v=>3n*v.a.slice(0,5).reduce((s,x)=>s+x*x,0n)+v.a[5]**2n,rootPt=v=>v.a[5]===0n&&v.a.slice(0,5).filter(z=>z===v.D).length===2&&v.a.slice(0,5).every(z=>z===v.D||z===0n);
const exact=(v,C)=>R.every((r,i)=>(r.reduce((s,x,k)=>s+BigInt(x)*v.a[k],0n)>v.D)===C.includes(i));

function census(cap){
 let cur=[[]];const result=[];for(let k=0;k<=8;k++){let out=[];for(const C of cur){const V=vertices(C,cap),high=V.filter(v=>q(v)>6n*v.D**2n),eq=V.filter(v=>q(v)===6n*v.D**2n&&!rootPt(v)&&exact(v,C));if(high.length||eq.length)out.push({C,high:high.length,eq:eq.map(v=>v.a.join(',')+'/'+v.D)});}
 result.push({k,ideals:cur.length,out});const n=new Map();for(const C of cur)for(const i of maximal(ids.filter(i=>!C.includes(i)))){const T=C.concat(i).sort((a,b)=>a-b);n.set(T.join(),T);}cur=[...n.values()];}
 return result;
}
const all=census(false),low=census(true),want=[[],[],[],[],[0,2,4,6],[0,2,4,6,7],[0,2,4,5,6,7],[0,2,3,4,5,6,7],[0,1,2,3,4,5,6,7]];
if(all.map(x=>x.ideals).join()!=='1,1,1,2,2,3,4,5,6')throw Error('ideal counts');
for(let k=0;k<=8;k++){
 const t=all[k],l=low[k];if(t.out.length!==(k>=4?1:0)||t.out.length&&t.out[0].C.join()!==want[k].join())throw Error('star classification');
 if(l.out.length!==(k===4?1:0)||k===4&&(l.out[0].high||l.out[0].eq.join()!=='2,1,1,1,1,0/2'))throw Error('low center classification');
}
console.log(JSON.stringify({all,low}));
const bits=m=>Array.from({length:5},(_,i)=>(m>>i&1)?-1:1);
const parity=s=>s.filter(v=>v<0).length%2,layer=[];for(let m=0;m<32;m++){const s=bits(m);if(!parity(s))for(const t of [-6,6])layer.push(s.map(v=>v*2).concat(t));}
const D5=roots.map(v=>v.map(x=>4*x).concat(0)),removed=D5.filter(r=>r[0]===4),kept=D5.filter(r=>r[0]!==4);
const exceptional=[];for(let m=0;m<16;m++){const s=bits(m).slice(0,4);if(parity(s))exceptional.push([4,...s.map(x=>2*x),0]);}
const points=[...layer,...kept,...exceptional],ip=(a,b)=>3*a.slice(0,5).reduce((s,x,i)=>s+x*b[i],0)+a[5]*b[5];
if(removed.length!==8||points.length!==72||points.some((a,i)=>ip(a,a)!==96||points.some((b,j)=>i!==j&&ip(a,b)>48)))throw Error('sharp example');
const x=[5,2,1,1,-1,0];if(ip(x,x)!==96||layer.some(b=>ip(x,b)>48)||D5.filter(b=>ip(x,b)>48).length!==4)throw Error('four-omission witness');
console.log({sharpConfiguration:points.length,omittedRoots:removed.length,fourOmissionWitness:true});
