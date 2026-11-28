// Verify the three universal short-cycle certificates for six-layer quotients.
// Every length-two witness certifies coincident parallel matchings, which
// is impossible in a simple lift. Every other witness is a 4/8/16-cycle.
// Usage: node verify_erdos_gyarfas_six_layer_extremal.mjs

function verify(input){
 function require(ok,why){if(!ok)throw new Error(why);}
 function subsets(n,k,first=0,prefix=[]){
  if(!k)return [prefix];
  return Array.from({length:n-first-k+1},(_,i)=>first+i).flatMap(i=>subsets(n,k-1,i+1,[...prefix,i]));
 }
 function det(a){
  if(a.length===0)return 1n;
  return a[0].reduce((total,entry,j)=>total+(j%2?-entry:entry)*det(a.slice(1).map(row=>row.filter((_,i)=>i!==j))),0n);
 }
 function gcd(a,b){a=a<0n?-a:a;b=b<0n?-b:b;while(b)[a,b]=[b,a%b];return a;}
 const signatures=new Map();
 function signature(rows,rank){
  const key=JSON.stringify([rank,rows]);
  if(signatures.has(key))return signatures.get(key);
  for(let r=Math.min(rank,rows.length);r>0;r--){
   let g=0n;
   const columnChoices=subsets(rank,r);
   for(const is of subsets(rows.length,r)){
    for(const js of columnChoices){
     g=gcd(g,det(is.map(i=>js.map(j=>BigInt(rows[i][j])))));
     if(g===1n)break;
    }
    if(g===1n)break;
   }
   if(g){const sig=r+":"+g;signatures.set(key,sig);return sig;}
  }
  return "0:1";
 }
 function contains(rows,v,d){return signature(rows,d)===signature([...rows,v],d);}
 function sameLattice(a,b,d){return a.every(v=>contains(b,v,d))&&b.every(v=>contains(a,v,d));}
 return input.map(({matrix,edges,tree,rank})=>{
  require(matrix.flat().reduce((a,b)=>a+b,0)-5===rank,"wrong rank");
  const seenGen=Array(rank).fill(0),span=Array.from({length:6},()=>[]);
  const count=matrix.map(row=>row.map(()=>0));
  for(let u=0;u<6;u++)for(let i=0;i<edges[u].length;i++){
   const e=edges[u][i], [from,v,k,s,j]=e;
   const reverse=edges[v][j];
   require(from===u&&v<6&&u!==v&&(u<3)!==(v<3),"invalid edge");
   require(JSON.stringify(reverse)===JSON.stringify([v,u,k,-s,i]),"invalid reverse dart");
   require(k>=-1&&k<rank&&s===(u<3?1:-1),"invalid edge label");
   if(u<3){
    count[u][v-3]++;
    if(k>=0)seenGen[k]++;
   }
   if(k===-1)span[u].push(v);
  }
  require(JSON.stringify(matrix)===JSON.stringify(count),"quotient matrix mismatch");
  require(seenGen.every(x=>x===1),"cotree generator repeated");
  const reach=new Set([0]),queue=[0];
  for(let p=0;p<queue.length;p++)for(const v of span[queue[p]])if(!reach.has(v)){reach.add(v);queue.push(v);}
  require(reach.size===6&&span.flat().length===10,"zero arrows must form spanning tree");
  const nodes=new Set();let links=0,depth=0;
  function visit(node,level){
   const {R,start,steps,kids,len}=node;
   const tag=JSON.stringify(R);
   if(nodes.has(tag))return;
   nodes.add(tag);depth=Math.max(depth,level);
   require([2,4,8,16].includes(len)&&len===steps.length,"invalid witness length");
   require(R.every(v=>v.length===rank&&v.every(Number.isSafeInteger)),"invalid lattice vectors");
   const prefixes=[];
   let u=start,previous=-1,voltage=Array(rank).fill(0);
   for(const i of steps){
    require(i!==previous&&Number.isInteger(i)&&i>=0&&i<edges[u].length,"invalid nonbacktracking traversal");
    prefixes.push([u,voltage.slice()]);
    const [,v,k,s,reverse]=edges[u][i];
    if(k!==-1)voltage[k]+=s;
    u=v;
    previous=reverse;
   }
   require(u===start&&previous!==steps[0]&&contains(R,voltage,rank),"witness fails to close");
   const children=new Set();
   for(let i=0;i<len;i++)for(let j=i+1;j<len;j++){
    if(prefixes[i][0]!==prefixes[j][0])continue;
    const a=prefixes[i][1],b=prefixes[j][1];
    const v=b.map((k,h)=>k-a[h]);
    require(!contains(R,v,rank),"witness collides in current lattice");
    const choice=kids.findIndex(child=>sameLattice(child.R,[...R,v],rank));
    require(choice>=0,"missing collision child");
    children.add(choice);links++;
   }
   require(children.size===kids.length,"extraneous collision child");
   for(const c of kids)visit(c,level+1);
  }
  require(tree.R.length===0,"root must be full free lattice");
  visit(tree,0);
  return {matrix,states:nodes.size,collisionPairs:links,depth};
 });
}

const certificates = [{"matrix":[[0,1,2],[1,1,1],[2,1,0]],"edges":[[[0,4,-1,1,0],[0,5,-1,1,0],[0,5,0,1,1]],[[1,3,-1,1,0],[1,4,-1,1,1],[1,5,1,1,2]],[[2,3,-1,1,1],[2,3,2,1,2],[2,4,3,1,2]],[[3,1,-1,-1,0],[3,2,-1,-1,0],[3,2,2,-1,1]],[[4,0,-1,-1,0],[4,1,-1,-1,1],[4,2,3,-1,2]],[[5,0,-1,-1,1],[5,0,0,-1,2],[5,1,1,-1,2]]],"rank":4,"tree":{"R":[],"len":16,"start":0,"steps":[0,1,0,1,1,0,1,0,1,2,0,2,0,0,2,0],"kids":[{"R":[[0,0,1,0]],"len":2,"start":2,"steps":[0,2],"kids":[]},{"R":[[0,1,0,0]],"len":4,"start":0,"steps":[0,1,2,0],"kids":[]},{"R":[[0,1,1,0]],"len":8,"start":0,"steps":[0,1,0,1,1,0,2,0],"kids":[{"R":[[0,1,0,0],[0,0,1,0]],"len":2,"start":2,"steps":[0,2],"kids":[]}]},{"R":[[0,1,-1,0]],"len":8,"start":0,"steps":[0,1,0,2,0,0,2,0],"kids":[{"R":[[0,1,0,0],[0,0,1,0]],"len":2,"start":2,"steps":[0,2],"kids":[]}]}]}},{"matrix":[[0,1,2],[1,2,0],[2,0,1]],"edges":[[[0,4,-1,1,0],[0,5,-1,1,0],[0,5,0,1,1]],[[1,3,-1,1,0],[1,4,-1,1,1],[1,4,1,1,2]],[[2,3,-1,1,1],[2,3,2,1,2],[2,5,3,1,2]],[[3,1,-1,-1,0],[3,2,-1,-1,0],[3,2,2,-1,1]],[[4,0,-1,-1,0],[4,1,-1,-1,1],[4,1,1,-1,2]],[[5,0,-1,-1,1],[5,0,0,-1,2],[5,2,3,-1,2]]],"rank":4,"tree":{"R":[],"len":16,"start":0,"steps":[0,1,2,0,1,1,1,1,0,2,1,0,2,0,2,0],"kids":[{"R":[[1,0,0,0]],"len":2,"start":0,"steps":[1,1],"kids":[]},{"R":[[0,1,0,0]],"len":2,"start":1,"steps":[1,2],"kids":[]},{"R":[[2,0,0,0]],"len":4,"start":0,"steps":[1,1,1,1],"kids":[{"R":[[1,0,0,0]],"len":2,"start":0,"steps":[1,1],"kids":[]}]},{"R":[[2,-1,0,0]],"len":8,"start":1,"steps":[1,0,2,0,2,0,0,2],"kids":[{"R":[[1,0,0,0],[0,1,0,0]],"len":2,"start":0,"steps":[1,1],"kids":[]},{"R":[[2,0,0,0],[0,1,0,0]],"len":2,"start":1,"steps":[1,2],"kids":[]}]},{"R":[[1,-1,0,0]],"len":16,"start":0,"steps":[0,1,0,1,1,0,1,2,0,2,0,0,1,0,2,0],"kids":[{"R":[[1,0,0,0],[0,1,0,0]],"len":2,"start":0,"steps":[1,1],"kids":[]},{"R":[[1,-1,0,0],[0,0,1,0]],"len":2,"start":2,"steps":[0,2],"kids":[]},{"R":[[1,0,-1,0],[0,1,-1,0]],"len":16,"start":1,"steps":[0,1,1,0,2,0,1,2,0,2,0,2,2,0,0,1],"kids":[{"R":[[1,0,0,0],[0,1,0,0],[0,0,1,0]],"len":2,"start":0,"steps":[1,1],"kids":[]},{"R":[[1,0,1,0],[0,1,1,0],[0,0,2,0]],"len":4,"start":0,"steps":[1,1,1,1],"kids":[{"R":[[1,0,0,0],[0,1,0,0],[0,0,1,0]],"len":2,"start":0,"steps":[1,1],"kids":[]}]},{"R":[[1,0,-1,0],[0,1,-1,0],[0,0,0,1]],"len":8,"start":0,"steps":[0,1,0,1,1,1,2,1],"kids":[{"R":[[1,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]],"len":2,"start":0,"steps":[1,1],"kids":[]}]},{"R":[[1,0,0,-1],[0,1,0,-1],[0,0,1,-1]],"len":8,"start":0,"steps":[0,1,2,1,0,2,2,1],"kids":[{"R":[[1,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]],"len":2,"start":0,"steps":[1,1],"kids":[]}]},{"R":[[1,0,1,-1],[0,1,1,-1],[0,0,2,-1]],"len":8,"start":0,"steps":[2,0,2,2,0,0,1,0],"kids":[{"R":[[1,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]],"len":2,"start":0,"steps":[1,1],"kids":[]}]}]},{"R":[[1,0,1,0],[0,1,1,0]],"len":16,"start":1,"steps":[0,1,1,0,1,0,1,2,0,2,0,2,2,0,0,2],"kids":[{"R":[[1,0,0,0],[0,1,0,0],[0,0,1,0]],"len":2,"start":0,"steps":[1,1],"kids":[]},{"R":[[1,0,1,0],[0,1,1,0],[0,0,2,0]],"len":4,"start":0,"steps":[1,1,1,1],"kids":[{"R":[[1,0,0,0],[0,1,0,0],[0,0,1,0]],"len":2,"start":0,"steps":[1,1],"kids":[]}]},{"R":[[1,0,0,-1],[0,1,0,-1],[0,0,1,1]],"len":8,"start":0,"steps":[0,1,0,1,1,1,2,0],"kids":[{"R":[[1,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]],"len":2,"start":0,"steps":[1,1],"kids":[]}]},{"R":[[1,0,1,0],[0,1,1,0],[0,0,0,1]],"len":8,"start":0,"steps":[0,1,2,1,0,1,2,1],"kids":[{"R":[[1,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]],"len":2,"start":0,"steps":[1,1],"kids":[]}]},{"R":[[1,0,0,1],[0,1,0,1],[0,0,1,-1]],"len":8,"start":0,"steps":[1,1,1,2,0,0,1,0],"kids":[{"R":[[1,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]],"len":2,"start":0,"steps":[1,1],"kids":[]}]}]}]},{"R":[[2,1,0,0]],"len":8,"start":1,"steps":[1,0,1,1,1,1,0,2],"kids":[{"R":[[1,0,0,0],[0,1,0,0]],"len":2,"start":0,"steps":[1,1],"kids":[]},{"R":[[2,0,0,0],[0,1,0,0]],"len":2,"start":1,"steps":[1,2],"kids":[]}]},{"R":[[1,1,0,0]],"len":16,"start":0,"steps":[0,1,0,1,1,0,1,2,0,2,0,0,1,0,1,1],"kids":[{"R":[[1,0,0,0],[0,1,0,0]],"len":2,"start":0,"steps":[1,1],"kids":[]},{"R":[[1,1,0,0],[0,0,1,0]],"len":2,"start":2,"steps":[0,2],"kids":[]},{"R":[[1,0,1,0],[0,1,-1,0]],"len":16,"start":1,"steps":[0,1,1,0,2,0,1,2,0,2,0,2,2,0,0,1],"kids":[{"R":[[1,0,0,0],[0,1,0,0],[0,0,1,0]],"len":2,"start":0,"steps":[1,1],"kids":[]},{"R":[[1,0,1,0],[0,1,1,0],[0,0,2,0]],"len":4,"start":0,"steps":[1,1,1,1],"kids":[{"R":[[1,0,0,0],[0,1,0,0],[0,0,1,0]],"len":2,"start":0,"steps":[1,1],"kids":[]}]},{"R":[[1,0,1,0],[0,1,-1,0],[0,0,0,1]],"len":8,"start":0,"steps":[0,1,2,1,0,2,2,0],"kids":[{"R":[[1,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]],"len":2,"start":0,"steps":[1,1],"kids":[]}]},{"R":[[1,0,0,1],[0,1,0,-1],[0,0,1,-1]],"len":8,"start":0,"steps":[1,1,1,2,0,0,1,0],"kids":[{"R":[[1,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]],"len":2,"start":0,"steps":[1,1],"kids":[]}]},{"R":[[1,0,1,0],[0,1,1,-1],[0,0,2,-1]],"len":8,"start":0,"steps":[0,1,0,2,0,2,2,0],"kids":[{"R":[[1,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]],"len":2,"start":0,"steps":[1,1],"kids":[]}]}]},{"R":[[1,0,-1,0],[0,1,1,0]],"len":16,"start":1,"steps":[0,1,1,0,1,0,1,2,0,2,0,2,2,0,0,2],"kids":[{"R":[[1,0,0,0],[0,1,0,0],[0,0,1,0]],"len":2,"start":0,"steps":[1,1],"kids":[]},{"R":[[1,0,1,0],[0,1,1,0],[0,0,2,0]],"len":4,"start":0,"steps":[1,1,1,1],"kids":[{"R":[[1,0,0,0],[0,1,0,0],[0,0,1,0]],"len":2,"start":0,"steps":[1,1],"kids":[]}]},{"R":[[1,0,0,1],[0,1,0,-1],[0,0,1,1]],"len":8,"start":0,"steps":[0,1,0,1,1,1,2,0],"kids":[{"R":[[1,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]],"len":2,"start":0,"steps":[1,1],"kids":[]}]},{"R":[[1,0,-1,0],[0,1,1,0],[0,0,0,1]],"len":8,"start":0,"steps":[0,1,0,1,1,1,2,1],"kids":[{"R":[[1,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]],"len":2,"start":0,"steps":[1,1],"kids":[]}]},{"R":[[1,0,0,-1],[0,1,0,1],[0,0,1,-1]],"len":8,"start":0,"steps":[0,1,2,1,0,1,2,0],"kids":[{"R":[[1,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]],"len":2,"start":0,"steps":[1,1],"kids":[]}]}]}]}]}},{"matrix":[[1,1,2],[1,1,1],[1,1,1]],"edges":[[[0,3,-1,1,0],[0,4,-1,1,0],[0,5,-1,1,0],[0,5,0,1,1]],[[1,3,-1,1,1],[1,4,1,1,1],[1,5,2,1,2]],[[2,3,-1,1,2],[2,4,3,1,2],[2,5,4,1,3]],[[3,0,-1,-1,0],[3,1,-1,-1,0],[3,2,-1,-1,0]],[[4,0,-1,-1,1],[4,1,1,-1,1],[4,2,3,-1,1]],[[5,0,-1,-1,2],[5,0,0,-1,3],[5,1,2,-1,2],[5,2,4,-1,2]]],"rank":5,"tree":{"R":[],"len":16,"start":0,"steps":[0,1,1,2,0,0,2,1,0,2,1,1,0,0,3,0],"kids":[{"R":[[1,0,0,0,0]],"len":2,"start":0,"steps":[2,1],"kids":[]},{"R":[[0,1,0,-1,0]],"len":4,"start":1,"steps":[0,2,1,1],"kids":[]},{"R":[[1,-1,0,1,0]],"len":8,"start":0,"steps":[0,1,1,2,0,0,2,1],"kids":[{"R":[[1,0,0,0,0],[0,1,0,-1,0]],"len":2,"start":0,"steps":[2,1],"kids":[]}]},{"R":[[1,1,0,-1,0]],"len":8,"start":0,"steps":[0,1,1,2,0,0,3,0],"kids":[{"R":[[1,0,0,0,0],[0,1,0,-1,0]],"len":2,"start":0,"steps":[2,1],"kids":[]}]}]}}];
const report = verify(certificates);
if (JSON.stringify(report.map(row=>[row.states,row.collisionPairs,row.depth])) !==
    JSON.stringify([[6,20,2],[31,164,4],[6,20,2]])) {
 throw new Error("Certificate census differs from the frozen result");
}
console.log(JSON.stringify(report, null, 2));
