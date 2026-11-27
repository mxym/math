const gram=(a,q)=>(a%q+q)%q;
const comb=(n,r)=>{const out=[];function f(i,V){if(V.length===r){out.push(V);return}for(let j=i;j<n;j++)f(j+1,V.concat(j))}f(0,[]);return out};
function cert(q,d,B,w,t){
 const roots=d===1?[q-1]:Array.from({length:q},(_,k)=>k).filter(k=>gram(k*k+1,q)===0);if(roots.length!==d)throw Error("toy assumes fully split");
 const labels=Array.from({length:2*d},(_,k)=>k);
 const bits=[];for(const S of comb(B,w)){function fill(j,V){if(j===w){bits.push(V);return;}for(const label of j===0?[0]:labels){const W=V.slice();W[S[j]]=label;fill(j+1,W)}}fill(0,Array(B).fill(-1));}
 const fieldRows=roots.map(r=>bits.map(row=>row.map(u=>u<0?0:gram((u>=d?-1:1)*r**(u%d),q))));
 const rank=(mat)=>{const A=mat.map(a=>a.slice());let j=0;for(let k=0;k<B&&j<A.length;k++){let p=j;while(p<A.length&&A[p][k]===0)p++;if(p===A.length)continue;[A[p],A[j]]=[A[j],A[p]];let inv=1;while(gram(inv*A[j][k],q)!==1)inv++;A[j]=A[j].map(x=>gram(x*inv,q));for(let r=j+1;r<A.length;r++){const c=A[r][k];A[r]=A[r].map((x,z)=>gram(x-c*A[j][z],q));}j++;}return j};
 const N=bits.length,H=q**(d*t*B),mom=Array(4).fill(0),pred=Array(4).fill(0),types={};
 for(let x=0;x<H;x++){const M=Array.from({length:d*t},(_,r)=>Array.from({length:B},(_,j)=>Math.floor(x/q**(r*B+j))%q));let z=0;for(let i=0;i<N;i++)if(M.every((v,r)=>gram(v.reduce((s,y,j)=>s+y*fieldRows[r%d][i][j],0),q)===0))z++;for(let k=1;k<=3;k++){let c=1;for(let i=0;i<k;i++)c*=z-i;mom[k]+=c;}}
 for(let k=1;k<=3;k++){let fac=1;for(let i=1;i<=k;i++)fac*=i;for(const I of comb(N,k)){const m=fieldRows.map(A=>rank(I.map(j=>A[j])));pred[k]+=fac*H/q**(t*m.reduce((a,b)=>a+b));if(k===3){const s=m.join(",");types[s]=(types[s]||0)+1;}}}
 if(pred.some((x,j)=>x!==mom[j])||mom[1]!==N*H/q**(d*t)||mom[2]!==N*(N-1)*H/q**(2*d*t))throw Error("moment mismatch");
 return {q,d,B,w,t,N,H,momentNumerators:mom.slice(1),tripleRanks:types};
}
const out=[cert(5,1,4,2,1),cert(5,2,3,2,1),cert(5,2,3,3,1)];
console.log(JSON.stringify(out));
