"use strict";
// Small exact arithmetic verification of the starts in the Stewart supplement.
let checks=0, tested=0, lastHigh=0n;
const ok=(b,m)=>{++checks;if(!b)throw Error(m);};
function isqrt(n){
 if(n<2n)return n;
 let r=1n<<BigInt((n.toString(2).length+1)>>1);
 while(true){const t=(r+n/r)>>1n;if(t>=r)return r;r=t;}
}
const windows=[
 {p:1n,q:1n,name:"one"}, {p:9n,q:16n,name:"three_quarters"},
 {p:1n,q:5n,name:"endpoint"}, {p:4n,q:25n,name:"below"}
];
const results=Object.fromEntries(windows.map(w=>[w.name,
  Object.fromEntries(["+","-"].map(s=>[s,{success:0,orders:{},meanNormSum:0}]))]));
function starts(m,B,p,q){
 const fits=N=>q*(B-N)**2n<=p*N;
 if(!fits(m))return 0n;
 let lo=B-isqrt(p*B/q),hi=m;
 while(lo<hi){
   const mid=(lo+hi)>>1n;
   if(fits(mid))hi=mid;else lo=mid+1n;
 }
 ok(fits(lo)&&!fits(lo-1n),"exact least starting integer");
 ok(lo<=m,"nonempty interval of starts");
 return m-lo+1n;
}
for(let n=1n;n<=10000n;n++){
 for(const sign of [-1n,1n]){
   ++tested;
   const n5=n**5n,n10=n5*n5,n15=n10*n5;
   const F=(125n*n**6n+sign*3n*n)**5n,C=(3125n*n10+sign*125n*n5+1n)**3n;
   ok(C-F===sign*78125n*n15+5625n*n10+sign*132n*n5+1n,"signed polynomial identity");
   const R=isqrt(F),down=R*R,up=(R+1n)**2n;
   ok(down<=F&&F<up,"neighboring squares");
   ok(F-2n*R>lastHigh,"checked disjoint centers including both signs");
   lastHigh=F+2n*R;
   const f= C>F?C-F:F-C, slack=isqrt(F/5n)-f;
   const slackErr=2n*slack+sign*1875n*n10;
   ok(-1000n*n5<=slackErr&&slackErr<=1000n*n5,"second-order endpoint comparison");
   ok(sign===1n?slack<0n:slack>0n,"different endpoint signs");
   for(const {p,q,name} of windows){
     let sum=0n,res=results[name][sign===1n?"+":"-"];
     for(const S of [down,up]){
       if(S===F||S===C)continue;
       const ordered=[[S,"S"],[F,"F"],[C,"C"]].sort((a,b)=>a[0]<b[0]?-1:1);
       const count=starts(ordered[0][0],ordered[2][0],p,q);
       if(count>0n){
         const order=ordered.map(x=>x[1]).join("");
         res.orders[order]=(res.orders[order]||0)+1;
         sum+=count;
       }
     }
     if(sum>0n)res.success++;
     res.meanNormSum+=Number(sum)/Number(name==="endpoint"?n10:R);
     if(name==="below"&&n>=2n)ok(sum===0n,"no sampled below-endpoint starts");
     if(name==="endpoint"&&sign===1n)ok(sum===0n,"no positive-sign endpoint starts");
   }
 }
}
for(const name of Object.keys(results))for(const sign of ["+","-"]){
 const row=results[name][sign];
 row.meanNormalized=+(row.meanNormSum/10000).toFixed(6);
 delete row.meanNormSum;
}
ok(Object.keys(results.one["+"].orders).length===3&&
   Object.keys(results.one["-"].orders).length===3,"all six orders");
ok(results.endpoint["-"].success>0,"nonempty endpoint sample");
console.log({checks,tested,results});
