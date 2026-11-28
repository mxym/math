// Independent wide census for four abelian orbits on one side.
// Run from any directory: node verify_erdos_gyarfas_four_on_one_side_wide.mjs
import {readFileSync} from "node:fs";
function verify(certificates){
 function require(ok,text){if(!ok)throw Error(text);}
 function matrixKinds(){
  function* arrangements(xs){
   if(xs.length===0){yield [];return;}
   for(let i=0;i<xs.length;i++)for(const rest of arrangements(xs.filter((_,j)=>j!==i)))yield [xs[i],...rest];
  }
  const relabel=[...arrangements([0,1,2,3])];
  const permitted=[];
  for(let a=0;a<=2;a++)for(let b=0;b<=2;b++)for(let c=0;c<=2;c++)for(let d=0;d<=2;d++){
   const v=[a,b,c,d];
   if(a+b+c+d>=3&&v.filter(x=>x===2).length<=1)permitted.push(v);
  }
  const results=[];
  for(let n=4;n<=6;n++){
   const classSet=new Set();let count=0;
   function limit(rows){
    const doubledRows=Array(4).fill(0);
    for(const column of rows)for(let i=0;i<4;i++)if(column[i]===2&&++doubledRows[i]>1)return false;
    for(let i=0;i<4;i++)for(let j=i+1;j<4;j++){
     let support=0,marked=false,two=0;
     for(const v of rows)if(v[i]&&v[j]){
      support++;
      marked||=v[i]===2||v[j]===2;
      if(v.filter(x=>x!==0).length===2)two++;
     }
     if(support>(marked?2:3)||two>1)return false;
    }
    return true;
   }
   function generate(path,first){
    if(path.length===n){
     if([0,1,2,3].some(i=>path.reduce((s,v)=>s+v[i],0)<3))return;
     count++;
     const key=relabel.map(p=>path.map(v=>p.map(i=>v[i]).join("")).sort().join("/")).sort()[0];
     classSet.add(key);return;
    }
    for(let i=first;i<permitted.length;i++){
     const next=[...path,permitted[i]];
     if(limit(next))generate(next,i);
    }
   }
   generate([],0);
   results.push({n,count,types:[...classSet].sort()});
  }
  return results;
 }
 function bezout(a,b){
  let x=1n,y=0n,z=0n,w=1n;
  while(b!==0n){
   const q=a/b;
   [a,b]=[b,a-q*b];
   [x,z]=[z,x-q*z];
   [y,w]=[w,y-q*w];
  }
  return a<0n?[-a,-x,-y]:[a,x,y];
 }
 function quotient(x,y){
  const q=x/y;
  return x%y<0n?q-1n:q;
 }
 function addRelation(rows,d){
  const M=[...rows,d].map(v=>v.slice());let used=0;
  for(let i=0;i<d.length&&used<M.length;i++){
   const k=M.findIndex((v,j)=>j>=used&&v[i]!==0n);
   if(k<0)continue;
   [M[k],M[used]]=[M[used],M[k]];
   for(let j=used+1;j<M.length;j++){
    if(M[j][i]===0n)continue;
    const A=M[used],B=M[j],a=A[i],b=B[i];
    const [g,s,t]=bezout(a,b);
    M[used]=A.map((x,l)=>s*x+t*B[l]);
    M[j]=B.map((x,l)=>(a*x-b*A[l])/g);
   }
   if(M[used][i]<0n)M[used]=M[used].map(x=>-x);
   for(let j=0;j<used;j++){
    const q=quotient(M[j][i],M[used][i]);
    M[j]=M[j].map((x,l)=>x-q*M[used][l]);
   }
   used++;
  }
  require(M.slice(used).every(v=>v.every(x=>x===0n)),"integer lattice elimination lost rank");
  return M.slice(0,used);
 }
 function vanishes(rows,d){
  const v=d.slice();
  for(const a of rows){
   const j=a.findIndex(x=>x!==0n);
   if(v[j]%a[j])return false;
   const q=v[j]/a[j];
   for(let k=j;k<v.length;k++)v[k]-=q*a[k];
  }
  return v.every(x=>x===0n);
 }
 const asKey=M=>"["+M.map(a=>"["+a.join(",")+"]").join(",")+"]";
 function checkCase(type,data){
  const cols=type.split("/").map(x=>[...x].map(Number));
  const darts=[],required=[];
  const groups=Array.from({length:4+cols.length},(_,i)=>i);
  let dim=0;
  const zero=()=>Array(dim).fill(0n);
  for(let i=0;i<4;i++)for(let j=0;j<cols.length;j++){
   let old=-2;
   for(let m=0;m<cols[j][i];m++){
    const right=j+4;
    const a=groups[i],b=groups[right];
    let coord=-1;
    if(a!==b){for(let k=0;k<groups.length;k++)if(groups[k]===b)groups[k]=a;}
    else coord=dim++;
    if(m===1)required.push([old,coord]);
    old=coord;
    const p=darts.length;
    darts.push([i,right,coord,1n,p+1],[right,i,coord,-1n,p]);
   }
  }
  require(new Set(groups).size===1,"expected connected reduced template");
  const forbid=required.map(([a,b])=>{const v=zero();if(a>=0)v[a]--;if(b>=0)v[b]++;return v;});
  const reached=new Set(), depthMemo=new Map(), terminalMemo=new Map();let maxDepth=0;
  function verify(R,depth){
   if(forbid.some(d=>vanishes(R,d)))return [-1,0];
   const id=asKey(R);
   if(reached.has(id)){ require(depthMemo.has(id),"cycle in the relation DAG"); return [depthMemo.get(id),terminalMemo.get(id)]; }
   reached.add(id);maxDepth=Math.max(maxDepth,depth);
   const word=data[id];
   require(Array.isArray(word)&&[4,8,16].includes(word.length),"missing length-4/8/16 witness "+type+" "+id);
   require(word.every(j=>Number.isInteger(j)&&j>=0&&j<darts.length),"invalid dart number");
   const at=Array.from({length:groups.length},()=>[]);
   const v=zero(), children=new Map();
   for(let i=0;i<word.length;i++){
    const [base,to,coordinate,sign,inverse]=darts[word[i]];
    const next=word[(i+1)%word.length];
    require(to===darts[next][0]&&next!==inverse,"path is not cyclically nonbacktracking");
    for(const prefix of at[base]){
     const diff=v.map((x,j)=>x-prefix[j]);
     require(!vanishes(R,diff),"cycle already collides at purported proof node");
     const child=addRelation(R,diff);
     children.set(asKey(child),child);
    }
    at[base].push(v.slice());
    if(coordinate>=0)v[coordinate]+=sign;
   }
   require(vanishes(R,v),"cycle does not close");
   let longest=0,terminal=0; for(const child of children.values()){const [h,t]=verify(child,depth+1); longest=Math.max(longest,h+1);terminal=Math.max(terminal,t+1);} depthMemo.set(id,longest);terminalMemo.set(id,terminal); return [longest,terminal];
  }
  const [longest,terminal]=verify([],0);
  require(reached.size===Object.keys(data).length,"certificate has unused rows");
  return {type,states:reached.size,maxDepth,longest,terminal};
 }
 const census=matrixKinds();
 const whole=census.flatMap(row=>row.types);
 require(Object.keys(certificates).length===whole.length,"incomplete template coverage");
 const details=whole.map(key=>{require(Object.hasOwn(certificates,key),"unknown template "+key);return checkCase(key,certificates[key]);});
 return {census:census.map(row=>[row.n,row.count,row.types.length]),states:details.reduce((sum,x)=>sum+x.states,0),depth:Math.max(...details.map(x=>x.maxDepth)),trueNonterminalDepth:Math.max(...details.map(x=>x.longest)),throughTerminalDepth:Math.max(...details.map(x=>x.terminal)),byN:census.map(c=>[c.n,details.filter(d=>c.types.includes(d.type)).reduce((s,a)=>s+a.states,0)])};
}

const paths=process.argv.length>2?process.argv.slice(2):[4,5,6].map(n=>new URL(
  "./erdos_gyarfas_four_on_one_side_wide_4_by_"+n+".json", import.meta.url));
if(paths.length!==3)throw Error("Expected exactly three certificate files");
const certificates=Object.assign({},...paths.map(path=>JSON.parse(readFileSync(path,"utf8"))));
const result=verify(certificates);
const expected={census:[[4,1366,75],[5,1403,71],[6,260,18]],states:1486,depth:4,
    trueNonterminalDepth:4,throughTerminalDepth:4,byN:[[4,576],[5,728],[6,182]]};
if(JSON.stringify(result)!==JSON.stringify(expected))throw Error("Unexpected proof census");
console.log(JSON.stringify(result,null,2));
