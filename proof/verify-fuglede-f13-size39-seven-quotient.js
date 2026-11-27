'use strict';

const p=13,R=Array.from({length:p},(_,i)=>i),m=x=>(x%p+p)%p;
const inv=R.map(a=>R.find(b=>m(a*b)===1));
const V=Array.from({length:169},(_,i)=>[Math.floor(i/p),i%p]),T=[0,13,1];
const E=V.map(([x,y])=>V.map(([a,b])=>{
 const X=m(a-x),Y=m(b-y);
 return X?[m(Y*inv[X]),Math.min(X,p-X),m(y-m(Y*inv[X])*x)]:[13,Math.min(Y,p-Y),x];
}));
for(let exception=-1;exception<14;exception++){
 const used=[],len=Array(14).fill(0),cnt=Array(13).fill(0);let n=0,low=15;
 function tryPush(j){
  const news=[];
  for(const i of used){
   const [d,q]=E[i][j];if(d===exception)continue;
   if(len[d]&&len[d]!==q){for(const b of news)len[b]=0;return null;}
   if(!len[d]){len[d]=q;news.push(d);}
  }
  const [x,y]=V[j],line=exception<0?null:exception===13?x:m(y-exception*x);
  if(line!==null&&cnt[line]===4){for(const b of news)len[b]=0;return null;}
  if(line!==null)cnt[line]++;
  used.push(j);return ()=>{used.pop();if(line!==null)cnt[line]--;for(const b of news)len[b]=0;};
 }
 for(const v of T)if(!tryPush(v))throw Error("triangle rejected");
 const C=V.flatMap((_,i)=>T.includes(i)?[]:[i]);
 function go(j){
  if(used.length===7){n++;low=Math.min(low,len.filter(Boolean).length);return;}
  for(let i=j;i<=C.length-(7-used.length);i++){
   const pop=tryPush(C[i]);if(!pop)continue;
   go(i+1);pop();
  }
 }
 go(0);
 if(exception===-1?(n!==210||low!==12):(n===0||low<6))throw Error("incorrect seven-point census");
 console.log({exception,n,low});
}
