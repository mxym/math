"use strict";
// Two complete necessary cubic wing diagrams at seven five-site shores.
// B--C matching 0 is the identity, 1 the interchange. No exterior search.
function diagram(swap) {
  const types = ["A","B","C"];
  const sites = [], copies = ["A0","A1","A2","B0","B1","C0","C1"];
  let wing = [];
  for (const x of copies) {
    sites.push("U"+x); wing.push(x[0]);
    for (const j of types) if (j!==x[0]) {
      sites.push("H"+x+j,"L"+x+j); wing.push(j,j);
    }
  }
  sites.push("Z"); wing.push("A");
  const N=sites.map(()=>new Set());
  function edge(x,y) {
    const i=sites.indexOf(x),j=sites.indexOf(y);
    if(i<0||j<0||i===j||N[i].has(j))throw Error("bad edge");
    N[i].add(j);N[j].add(i);
  }
  for (const x of copies) {
    const [i,j]=types.filter(t=>t!==x[0]);
    edge("U"+x,"H"+x+i); edge("U"+x,"H"+x+j);
    edge("H"+x+i,"H"+x+j); edge("H"+x+i,"L"+x+i);
    edge("H"+x+j,"L"+x+j); edge("L"+x+i,"L"+x+j);
  }
  edge("UA0","Z"); edge("UA1","UA2"); edge("UB0","UB1"); edge("UC0","UC1");
  edge("LA1B","Z"); edge("LA2C","Z");
  for (const [x,y] of [["A0","B0"],["A2","B1"],["A0","C0"],["A1","C1"],
                       ["B0",swap?"C1":"C0"],["B1",swap?"C0":"C1"]])
    edge("L"+x+y[0],"L"+y+x[0]);
  for (const [i,row] of N.entries()) for (const t of types)
    if([...row].filter(j=>wing[j]===t).length!==1)throw Error("not wing-matched");
  if(types.some(t=>wing.filter(x=>x===t).length!==12))throw Error("physical counts");
  const reached=new Set([0]),pending=[0];
  while(pending.length)for (const j of N[pending.pop()])
    if(!reached.has(j)){reached.add(j);pending.push(j);}
  if(reached.size!==36)throw Error("not connected");
  const joinedTriangle = !swap;
  // The values tested in this note are the 35-by-35 matrix-tree cofactor.
  const matrix = N.slice(1).map((row,i)=>N.slice(1).map((_,j)=>3*(i===j)-row.has(j+1)));
  return [joinedTriangle,det7(matrix)];
}
function det7(a) {
  const inv=[0,1,4,5,2,3,6], red=x=>(x%7+7)%7;
  let d=1;
  a=a.map(r=>r.map(red));
  for(let j=0;j<a.length;j++){
    const k=a.findIndex((r,i)=>i>=j&&r[j]);
    if(k<0)return 0;
    if(k!==j){[a[k],a[j]]=[a[j],a[k]];d=red(-d);}
    d=red(d*a[j][j]);
    const u=inv[a[j][j]];
    for(let i=j+1;i<a.length;i++){
      const v=red(a[i][j]*u);
      for(let k=j;k<a.length;k++)a[i][k]=red(a[i][k]-v*a[j][k]);
    }
  }
  return d;
}
const out=[diagram(0),diagram(1)];
if(JSON.stringify(out)!=="[[true,0],[false,4]]")throw Error(JSON.stringify(out));
console.log(JSON.stringify(out));
