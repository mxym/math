"use strict";
/* Integer microstate replay for the blocked-shortcut lower bound on cubic bond p_c.
   Default: all N=12 entering axes. --axis=0, --axis=1, --axis=2: one row only.
   --small-test: independent literal O(N^2)-per-leaf geometry at N=8.
   This file uses no external data, packages or floating-point probabilities. */
const assert=require("node:assert/strict");
function starFast(N,axis0){
 // Every vertex has distance <=N+1 from the centre, so coordinate encoding is injective.
 // The low bits of mask[z] record adjoining anchors; bit 7 records a forbidden pair.
 // Bits are redone when extending to a new anchor. K counts flagged unvisited z.
 const L=2*N+9,D=[1,-1,L,-L,L*L,-L*L],o=Math.floor(L**3/2),board=new Uint8Array(L**3),mask=new Uint8Array(L**3),hist=Array.from({length:3},()=>Array.from({length:2*N+8},()=>Array(3*N/2+1).fill(0))), bak=new Int16Array(6*(N+1)), time=Date.now();
 let start=o+D[2*axis0];board[o]=board[start]=1;
 function dfs(pos,d,last,C,K){if(d===N){hist[last>>1][C][K]++;return;}
 for(let i=0;i<6;i++){
  const q=pos+D[i];if(board[q])continue;
  // A previously flagged centre ceases to be outside when the path visits it.
  let c=board[q+1]+board[q-1]+board[q+L]+board[q-L]+board[q+L*L]+board[q-L*L]-1, kk=K-((mask[q]&128)!==0);
  board[q]=1;
  if(d%2===1&&d<N-2){
   let ind=d*6,bit=1<<((d-1)/2),prev=bit>>1;
   for(let j=0;j<6;j++){
    const z=q+D[j],a=mask[z];bak[ind+j]=a;
    if(board[z])continue;
    let f=a|bit;
    if(a&&(a&128)===0&&((a&~prev)!==0 || (j>>1)<(i>>1))){f|=128;kk++;}
    mask[z]=f;
   }
   dfs(q,d+1,i,C+c,kk);
   for(let j=0;j<6;j++)mask[q+D[j]]=bak[ind+j];
  }else dfs(q,d+1,i,C+c,kk);
  board[q]=0;
 }}
 dfs(start,0,2*axis0,0,0);return {ms:Date.now()-time,hist};}

function evalExact(H, P, Q, n){const max=n+(H[0][0].length-1)+2*(H[0][0][0].length-1), a=BigInt(P),b=BigInt(Q),ex=Array.from({length:max+1},(_,i)=>b**BigInt(i));const A=a**BigInt(n),den=ex[max];let rows=[];
 for(const r of H){let fin=0n;for(const t of r)for(let c=0;c<t.length;c++)for(let k=0;k<t[c].length;k++)if(t[c][k])fin+=BigInt(t[c][k])*A*(b-a)**BigInt(c)*(b*b-a*a)**BigInt(k)*ex[max-n-c-2*k];
 rows.push({ppm:String((10n**6n*fin+den-1n)/den),exactBelow:fin<den});}
return rows}
function literal(N,axis) {
  const L=2*N+9, dirs=[1,-1,L,-L,L*L,-L*L];
  const w=[0,dirs[2*axis]], steps=[2*axis], used=new Set(w);
  const out=Array.from({length:3},()=>Array.from({length:2*N+8},()=>Array(3*N/2+1).fill(0)));
  function visit() {
    if(w.length===N+2) {
      let c=0;
      for(let j=2;j<w.length;j++) for(let i=0;i+1<j;i++)
        if(dirs.includes(w[j]-w[i])) c++;
      const centres=new Set;
      // w[0] is the memory vertex, so displayed path anchors are 3, 5, ...
      for(let i=3;i<=N-1;i+=2) for(let j=i+2;j<=N-1;j+=2)
        for(const d of dirs) {
          const z=w[i]+d, zi=dirs.indexOf(z-w[j]);
          if(zi>=0&&!used.has(z)&&(j-i>=4||(zi>>1)<(steps[j-1]>>1)))
            centres.add(z);
        }
      out[steps.at(-1)>>1][c][centres.size]++;
      return;
    }
    for(let d=0;d<6;d++){
      const v=w.at(-1)+dirs[d];if(used.has(v))continue;
      w.push(v);steps.push(d);used.add(v);visit();used.delete(v);steps.pop();w.pop();
    }
  }
  visit();
  return out;
}

function main(){
  const arg=process.argv[2];
  if(arg==="--small-test") {
    for(let i=0;i<3;i++)assert.deepEqual(starFast(8,i).hist,literal(8,i));
    console.log("PASS literal/online summaries, N=8");
    return;
  }
  assert(arg===undefined||/^--axis=[0-2]$/.test(arg));
  for(const i of arg===undefined?[0,1,2]:[Number(arg.at(-1))]){
    const o=starFast(12,i), total=o.hist.flat(2).reduce((s,x)=>s+x,0);
    assert(total===157329085);
    const [r]=evalExact([o.hist],215805,1000000,12);
    assert(r.exactBelow);
    assert(r.ppm===["999945","999972","999999"][i]);
    console.log("axis",i,"paths",total,"upward ppm",r.ppm,"ms",o.ms);
  }
  console.log("PASS exact at p=215805/1000000");
}
if(require.main===module) main();
