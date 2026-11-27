'use strict';
const W=570n,C=26n,V=307n,p=17n;
const lower=(x,y)=>x<y?x:y;
function ceil(a,b){return (a+b-1n)/b;}
function floor(a,b){return a>=0n?a/b:-ceil(-a,b);}
function indicatorDiff(N,q,d){
 const a=18n*W-C*V, den=p*V*(V-N),num=W*W*p*(V-N)+a*a*N;
 return d*num-q*den;
}
function profileEnvelopes(){
 const peak=[0,0,0],S6={s:0},S7={s:0};
 function part(b,s,min,max,h,sq,cb){
  if(!b){if(!s)cb(h,sq);return;}
  for(let w=min;w<=max&&w*b<=s;w++)part(b-1,s-w,w,max,h+(w>=7?1:0),sq+w*w,cb);
 }
 for(let b=8;b<=18;b++){
  part(b,26,2,12,0,0,(_,s)=>{S6.s=Math.max(S6.s,s);});
  part(b,26,b===8?2:1,11,0,0,(h,s)=>{if(h>=3)throw Error('heavy count');peak[h]=Math.max(peak[h],s);S7.s=Math.max(S7.s,s);});
 }
 if(String(peak)!=='122,172,192'||S6.s!==172||S7.s!==192)throw Error('local square bounds');
 if(peak.some((s,h)=>s>122+50*h))throw Error('heavy envelope');
}
profileEnvelopes();
// Local S6<=172, local S7<=192, refined septic norm<=122W/C + 450.
// Use the weaker S7<=212 for the asymmetric interval to keep comparison simple.
const S6=172n*W, S7loose=212n*W, S7ref=122n*W+450n*C;
function checkCut(a,q){if(indicatorDiff(a,q,C)<=0n||indicatorDiff(a-1n,q,C)>0n)throw Error('support upper');}
checkCut(225n,S6);checkCut(241n,S7loose);checkCut(208n,S7ref);
if(ceil(8n*W,C)!==176n||ceil(9n*W-9n*12n,C)!==194n||ceil(9n*W-9n*11n,C)!==194n)throw Error('support lower');
function check(label,n0,n1,m0,m1,upper,sym){
 let min=null,checked=0;
 for(let n=n0;n<=n1;n++)for(let m=sym?n:m0;m<=m1;m++){
  const e=upper(n,m),t=18n*n*m-V*e,delta=t*t-p*n*(V-n)*m*(V-m);
  if(t<=0n||delta<=0n)throw Error('mixed polarity');
  checked++;if(min===null||delta<min)min=delta;
 }
 console.log({label,checked,gap:min.toString()});
}
check('sextic/septic',176n,240n,194n,224n,(n,m)=>
 lower(8n*m+26n*n-4560n,9n*n-9n+floor(26n*m-5130n+108n,2n)),false);
const e7=(n,m)=>9n*m-9n+26n*n-5130n+99n;
check('septic/septic',194n,207n,194n,207n,(n,m)=>lower(e7(n,m),e7(m,n)),true);
