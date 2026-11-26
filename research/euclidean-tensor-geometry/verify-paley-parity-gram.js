// Exact finite checks of the uncentered torus Gram and centered parity identities.
'use strict';
function verify(p) {
 const mod=x=>(x%p+p)%p, n=(p-5)/4;
 const inv=Array(p).fill(0);inv[1]=1;for(let x=2;x<p;x++)inv[x]=mod(-(p/x|0)*inv[p%x]);
 const chi=Array(p).fill(-1);chi[0]=0; for(let x=1;x<p;x++)chi[mod(x*x)]=1;
 const B=Array.from({length:p-1},(_,i)=>i+1).filter(x=>chi[x]===1);
 const parity=Array(p).fill(-1);for(const x of B)parity[mod(x*x)]=1;
 const f=B.reduce((m,x)=>(m[x]=chi[mod(1-x)],m),[]);
 const g=B.reduce((m,x)=>(m[x]=BigInt(mod(x+inv[x]+2)-p/2+.5),m),[]);
 const h=B.reduce((m,x)=>(m[x]=BigInt(mod((x+inv[x])*((x+inv[x])+3))-p/2+.5),m),[]);
 const groups=Array.from({length:4},()=>({n:0n,g:0n,h:0n,gh:0n}));
 const index=(c,s)=>(c===1?0:2)+(s===1?0:1);
 for(const x of B)if(x!==1){const P=groups[index(parity[x],f[x])];P.n++;P.g+=g[x];P.h+=h[x];P.gh+=g[x]*h[x];}
 const scale=groups.reduce((m,G)=>m*G.n,1n);
 if(scale===0n) throw Error('empty sign class');
 let target=0n;
 for(const i of [0,2]){
   const A=groups[i],Q=groups[i+1];
   target+=4n*(Q.n*A.gh+A.n*Q.gh-A.g*Q.h-A.h*Q.g);
 }
 const roots=B.filter(x=>x!==1&&x!==p-1&&x<inv[x]);
 const q=z=>mod((z+2+inv[z])*inv[4]);
 if(roots.length!==n || new Set(roots.map(q)).size!==n) throw Error('bad quotient');
 let gram=0n,cr=0n,cdr=0n,uu=0n,dd=0n,lift=0;
 for(const z of roots)for(const w of roots)if(z!==w){
   const u=mod(w*inv[z]),v=mod(w*z), c=parity[u], sg=f[u], tg=f[v];
   if(!sg||!tg||parity[v]!==c||c!==parity[z]*parity[w]||chi[mod(q(z)-q(w))]!==sg*tg) throw Error('bad sign lift');
   if(sg===tg)continue;lift++;
   const d=BigInt(sg-tg), M=groups[index(c,sg)],N=groups[index(c,tg)];
   gram+=d*d*(g[u]-g[v])*(h[u]-h[v]);
   const r=d*(scale*(g[u]-g[v])-scale/M.n*M.g+scale/N.n*N.g);
   cr-=r; cdr-=BigInt(c)*r;uu+=r;dd+=BigInt(c)*r;
 }
 if(gram!==target||cr!==0n||cdr!==0n||uu!==0n||dd!==0n)throw Error('Gram/parity identity failure at '+p);
 return lift;
}
const ps=Array.from({length:501},(_,p)=>p).filter(p=>p>=17&&p%4===1&&Array.from({length:Math.floor(Math.sqrt(p))-1},(_,j)=>j+2).every(d=>p%d));
console.log(JSON.stringify({primes:ps.length,nonedgeEntries:ps.reduce((v,p)=>v+verify(p),0)}));
