'use strict';
// Independent characteristic-zero assertion of the 29 remaining triples.
const out=console.log;


const Ts=[];
function T(p,n,h,dim){Ts.push({p,n,h,dim,size:((p&1)>0)+((p&2)>0)+((p&4)>0)+((n&1)>0)+((n&2)>0)+((n&4)>0)+dim});}
for(let p of [0,2,3,6,7])T(p,0,'none',0);
T(3,0,'K12',1);T(6,0,'K01',1);T(7,0,'free',1);
T(7,1,'H01',1);T(7,4,'H12',1);
for(let n of [0,1,4,5,7])T(7,n,'full',2);
const grid=[];for(let i=0;i<3;i++)for(let k=2;k>=0;k--)grid.push([i,k]);
function stacks(N){
 let out=[];function go(j,ts,left,param){
  if(j===9){if(left===0)out.push({ts,param});return;}
  const [i,k]=grid[j];const parents=[];
  if(i>0)parents.push(ts[j-3]);if(k<2)parents.push(ts[j-1]);
  for(let t of Ts){if(t.size>left)continue;
   let z=param,ok=true;
   for(let f of parents){
    if((t.p&~f.p)!==0||(t.n&~f.n)!==0||t.dim>f.dim){ok=false;break;}
    if(t.dim===1&&f.dim===1&&t.h!==f.h){
      if(t.h!=='free'&&f.h!=='free'){ok=false;break;}
      let c=t.h==='free'?f.h:t.h;if(z&&z!==c){ok=false;break;}z=c;
    }
   }
   if(ok)go(j+1,[...ts,t],left-t.size,z);
  }
 }
 go(0,[],N,null);return out;
}
const st=stacks(8);
const hv=(h,t)=>({K12:[-2,1,1],K01:[1,1,-2],H01:[1,-1,0],H12:[0,1,-1],free:t===null?[0,1,-1]:[1,t,-1-t]})[h];
const roots=[[0,1],[0,2],[1,2]];
function dat(o,t){
 const E=[],F=[];
 for(let k0=0;k0<9;k0++){
  const [i,k]=grid[k0],a=o.ts[k0];
  let ds=Array.from({length:3},(_,j)=>[3*i+j,3*j+k,1]);E.push(ds);
  if(a.dim===0){F.push([ds[0],[...ds[1].slice(0,2),-1]],[ds[0],[...ds[2].slice(0,2),-1]]);}
  if(a.dim===1){let h=hv(a.h==='free'?(o.param??'free'):a.h,t);
   E.push(ds.map(([x,y],j)=>[x,y,h[j]]));
   F.push(ds.map(([x,y],j)=>[x,y,h[(j+1)%3]-h[(j+2)%3]]));
  }
  if(a.dim===2){E.push([ds[0],[...ds[1].slice(0,2),-1]],[ds[1],[...ds[2].slice(0,2),-1]]);}
  for(let j=0;j<3;j++)for(let l=0;l<3;l++)if(j!==l){
   let r=roots.findIndex(([x,y])=>x===Math.min(l,j)&&y===Math.max(l,j));
   let dest=((1<<r)&(l<j?a.p:a.n))?E:F;dest.push([[i*3+j,l*3+k,1]]);
  }
 }
 return {E,F};
}

const sx=(a,b)=>a>b?sx(b,a):b*(b+1)/2+a;
const wx=(a,b)=>a>b?wx(b,a):b*(b-1)/2+a;
function cols(o,t,kind){
 const {E,F}=dat(o,t);const out=[];
 if(kind<2){
  for(let s of F)for(let j=0;j<9;j++)out.push(s.map(([a,b,w])=>[kind===0?sx(a,j)*9+b:a*45+sx(b,j),w]));
 }else{
  for(let s of E)for(let a=0;a<9;a++)for(let b=0;b<9;b++)out.push(s.flatMap(([i,j,w])=>i===a||j===b?[]:[[36*wx(i,a)+wx(j,b),(i<a)===(j<b)?w:-w]]));
 }
 return out;
}
const abs=x=>x<0n?-x:x;
function gcd(a,b){a=abs(a);b=abs(b);while(b){[a,b]=[b,a%b]}return a;}

function rankQ(cols,n){
 const piv=Array(n);
 let rank=0;
 function prim(v) {
  let g=0n;
  for(let x of v.values()){g=gcd(g,x);if(g===1n)return;}
  if(g>1n)for(let [k,x] of v)v.set(k,x/g);
 }
 for(let col of cols){
  const v=new Map;
  function add(k,u){const s=(v.get(k)||0n)+u;if(s)v.set(k,s);else v.delete(k);}
  for(let [k,x] of col)add(k,BigInt(x));
  while(v.size){
   const p=Math.min(...v.keys()),f=v.get(p);
   if(!piv[p]){prim(v);piv[p]=v;rank++;break;}
   const q=piv[p],h=q.get(p);
   if(h!==1n)for(let [k,w] of v)v.set(k,w*h);
   for(let [k,x] of q)add(k,-f*x);
   prim(v);
  }
 }
 return rank;
}
const candidates=[195,196,197,198,200,201,202,203,205,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226];
function cf111(fs){
 const cs=[];
 for(let k=0;k<3;k++)for(let c=0;c<9;c++)for(let col of fs[k])cs.push(col.map(([a,b,w])=>[k===0?81*a+9*b+c:k===1?81*c+9*a+b:81*b+9*c+a,w]));
 return cs;
}

const dims=[405,405,1296],limits=[388,388,952];
const zA=[1,2,4,5],zB=[1,2],zC=[2,5];
const monomials=zA.flatMap(a=>zB.flatMap(b=>zC.map(c=>81*a+9*b+c)));
const D=new Set(monomials), M=new Set();
for(let i=0;i<3;i++)for(let j=0;j<3;j++)for(let k=0;k<3;k++)M.add(81*(3*i+j)+9*(3*j+k)+3*k+i);
function assert(ok,msg){if(!ok)throw Error(msg);}
assert(D.size===16&&M.size===27&&monomials.every(z=>!M.has(z)),'claimed cubic basis independent');
const pairRanks=[11,...candidates,29].map(i=>{
 const R=dims.map((n,k)=>rankQ(cols(st[i],0,k),n));
 assert(R.every((r,k)=>r<=limits[k]),'pair '+i);
 return [i,R];
});
for(let i of candidates){
 const F=cf111([11,i,29].map(t=>dat(st[t],0).F));
 assert(F.every(v=>v.every(([j,w])=>!D.has(j)||!w)&&v.filter(([j])=>M.has(j)).reduce((a,[,w])=>a+w,0)===0),'cubic basis '+i);
 assert(rankQ(F,729)===712,'cubic rank '+i);
}
out(JSON.stringify({pairRanks,cubicRank:712,numberOfTriples:candidates.length,uniqueCubicSpace:true,cartanFreeSideRanks:[pairRanks[0][1],pairRanks.at(-1)[1]]},null,2));
