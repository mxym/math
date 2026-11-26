'use strict';
// Exact checks for two largest-branch markers at cutoff two.
const add=(M,k,c=1)=>M.set(k,(M.get(k)||0)+c);
const check=(ok,msg)=>{if(!ok)throw Error(msg);};
const canon=(pairs,lo)=>pairs.sort().join(',')+'|'+lo.sort().join(',');
function checkDeck(connected){
  const h=2,g=7,S=7,M=2,q=3,N=q*S;
  const core=connected?[[0,1],[1,2]]:[[0,1],[0,2]];
  const marks=connected?[true,true,false]:[false,true,true];
  const E=core.slice();
  for(let v=0;v<q;v++){
    let p=q+v*(S-1);
    if(marks[v]){E.push([v,p],[p,p+1]);p+=2;}
    for(;p<q+(v+1)*(S-1);p++)E.push([v,p]);
  }
  const par=new Int32Array(N),sz=new Int32Array(N),p=new Int32Array(N);
  for(const [a,b] of E)par[b]=a;
  const actual=new Map,expected=new Map;
  let maxOne=0;
  for(let mask=0;mask<2**(N-1);mask++){
    sz.fill(1);let k=0,nh=0;
    for(let v=N-1;v>0;v--){
      if(mask&(1<<(v-1))){p[k++]=sz[v];nh+=sz[v]===h;}
      else sz[par[v]]+=sz[v];
    }
    p[k++]=sz[0];nh+=sz[0]===h;
    if(nh!==M)continue;
    const hi=[],lo=[];let nsum=0,j=0,nmark=0;
    for(let i=0;i<k;i++){
      const a=p[i];
      if(a<h)lo.push(a);
      if(a<=h)continue;
      const n=g*Math.ceil(a/g), d=n-a;
      if(d>=h&&(d%h!==0||d>M*h)){nsum=-N;break;}
      if(d>=h){j+=d/h;nmark++;}
      nsum+=n;hi.push(n+':'+d);
    }
    if(nsum!==N||j!==M)continue;
    if(nmark===1)maxOne=Math.max(maxOne,hi.length);
    add(actual,canon(hi,lo));
  }
  check(maxOne===(connected?2:1),'connectivity certificate');
  for(let m=0;m<4;m++){
    const groups=[[0],[1],[2]], rep=[0,1,2];
    for(let j=0;j<2;j++)if(!(m&(1<<j))){
      const [a,b]=core[j], u=rep[a], v=rep[b];
      for(const x of groups[v])rep[x]=u;
      groups[u].push(...groups[v]);groups[v]=[];
    }
    const parts=groups.filter(A=>A.length);
    function rec(i,hi,lo,c){
      if(i===parts.length){add(expected,canon(hi.slice(),lo.slice()),c);return;}
      const A=parts[i], n=S*A.length, j=A.filter(v=>marks[v]).length;
      rec(i+1,[...hi,n+':'+(h*j)],lo,c);
      if(j===0)rec(i+1,[...hi,n+':1'],[...lo,1],c*A.length*(S-1));
    }
    rec(0,[],[],1);
  }
  check(actual.size===expected.size,'support mismatch');
  for(const [k,v] of expected)check(actual.get(k)===v,'coefficient mismatch at '+k);
  return [connected?'adjacent':'separated',2**(N-1),actual.size,maxOne];
}
for(const c of [true,false]) (typeof console==='undefined'?text:console.log)(checkDeck(c).join(' | '));
