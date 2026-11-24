/* Run with Node.js: node check_eac_six_three_quarter.js */
console.log(JSON.stringify((()=>{
"use strict";

// No prime/center search. Labels 0,...,5 are in increasing order.
// The exact odd-prime geometry used here is explained in the accompanying proof.
function run(ascending) {
  const all=63, out=[];
  const table=Array.from({length:6},()=>[0,0,0,0,0]); // ordered, SCC, detA=0, both, geometry
  const pc=Array.from({length:64},(_,x)=>x.toString(2).replace(/0/g,"").length);
  function determinant(A) {
    const v=Array(64).fill(0); v[0]=1;
    for(let m=0;m<63;m++) {
      const i=pc[m];
      for(let j=0;j<6;j++) if(!(m>>j&1))
        v[m|(1<<j)] += (pc[m>>(j+1)]%2 ? -1:1)*v[m]*A[i][j];
    }
    return v[63];
  }
  function strong(R) {
    for(let s=0; s<6; s++){
      let reach=1<<s;
      for(let k=0;k<6;k++) for(let i=0;i<6;i++)
        if(reach>>i&1) for(const j of R[i]) reach|=1<<j;
      if(reach!==all) return false;
    }
    return true;
  }
  function geometry(R,r) {
    const semi=R.filter((_,i)=>i!==r);
    const pEdges=semi.filter(([a])=>a===0);
    if(pEdges.length){
      const giants=new Set(pEdges.map(([,b])=>b));
      if(giants.has(0)||giants.size!==pEdges.length) return false;
      if([...giants].some(g=>g<6-giants.size)) return false;
      if(semi.some(([a,b])=>a!==0&&(giants.has(a)||giants.has(b)))) return false;
      let rowcount=0;
      for(const g of giants) if(g===r||R[g][0]===0) rowcount++;
      return rowcount<=1;
    }
    // Largest label's cofactor component is a star when all pairs omit 0.
    const e=semi.filter(([,b])=>b===5); if(e.length!==1)return false;
    const c=e[0][0];
    for(const s of semi) if(s.includes(c)){
      if(s[0]===s[1]) return false;
      const z=s[0]===c?s[1]:s[0];
      if(semi.filter(t=>t.includes(z)).length!==1) return false;
    }
    return true;
  }
  const options=Array.from({length:6},(_,i)=>{
    const R=[];
    for(let a=0;a<6;a++) for(let b=a;b<6;b++)
      if(a!==i&&b!==i&&!(a===5&&b===5)) R.push([a,b]);
    return R;
  });
  for(let r=1;r<6;r++) {
    const R=Array(6).fill(null); R[r]=[0,0,0];const roworder=[0,1,2,3,4,5].filter(i=>i!==r);
    if(!ascending)roworder.reverse();
    function recurse(depth,parentMask) {
      if(depth===5) {
        table[r][0]++;
        if(!strong(R))return;table[r][1]++;
        const A=R.map(x=>Array.from({length:6},(_,j)=>x.reduce((s,k)=>s+(k===j),0)));
        if(determinant(A)!==0) return;table[r][2]++;
        const B=A.map((x,i)=>x.map((m,j)=>+(i===j)-m));
        if(determinant(B)!==0) return;table[r][3]++;
        if(!geometry(R,r))return;table[r][4]++;
        out.push([r,R.map(x=>x.join("")).join("/")]);return;
      }
      const i=roworder[depth];
      option:for(const row of options[i]) {
        let parents=0; for(const j of row) if(i<j) parents|=1<<j;
        if(parentMask&parents)continue;
        for(let j=0;j<6;j++){
          if(j===r||!R[j])continue;
          const [a,b]=i<j?row:R[j], [c,d]=i<j?R[j]:row;
          if(a<=c&&b<=d)continue option;
        }
        R[i]=row;recurse(depth+1,parentMask|parents);R[i]=null;
      }
    }
    recurse(0,0);
  }
  return {table:table.slice(1),out:out.sort((a,b)=>a[0]-b[0]||a[1].localeCompare(b[1]))};
}
const first=run(true), second=run(false);
if(JSON.stringify(first)!==JSON.stringify(second))throw Error("row-order mismatch");
const expected=[[1,"33/000/15/14/23/22"],[2,"33/25/000/24/13/11"]];
if(JSON.stringify(first.out)!==JSON.stringify(expected))throw Error("lone cube residual mismatch");
return first;

})()));
