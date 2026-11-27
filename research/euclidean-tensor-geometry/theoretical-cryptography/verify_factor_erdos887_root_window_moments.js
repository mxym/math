"use strict";
// Finite checks for the #887 note: direct windows vs. gcd collision coordinates.
const X=100000, cx=[[1,1],[5,4],[4,3],[3,2],[2,1],[5,2]];
let checks=0;
const ok=(b,msg)=>{++checks;if(!b)throw Error(msg);};
const gcd=(a,b)=>b?gcd(b,a%b):a;
const phi=n=>{let s=0;for(let a=1;a<=n;++a)if(gcd(a,n)===1)++s;return s;};
const results=[];
for(const [p,q] of cx){
 const nn=new Uint16Array(X+1), pair=new Uint16Array(X+1);
 const p2=BigInt(p*p),q2=BigInt(q*q),q4=q2*q2;
 const fits=(n,b)=>{
   const N=BigInt(n),B=BigInt(b),S=B*B+N,R=2n*B*q2+p2;
   return B*B>N&&q4*S*S<N*R*R;
 };
 for(let a=1;a*a<X;++a){
   for(let b=a+1;a*b<=X;++b){
     const n=a*b;
     if(fits(n,b))++nn[n];
   }
 }
 let K=0;
 for(let u=1;u*q*q<p*p;++u){
   for(let v=1;u*v*q*q<p*p;++v){
     K+=phi(u)/u*Math.acosh(p/(q*Math.sqrt(u*v)));
     for(let g=1;g*(g+v)*(1+u)<=X;++g){
       const lo=Math.floor(g*u/v)+1;
       if(g*(g+v)*lo*(lo+u)>X)break;
       for(let s=lo;g*(g+v)*s*(s+u)<=X;++s){
         if(gcd(s,u)!==1)continue;
         const a1=g*(s+u),a2=g*s,b1=(g+v)*s,b2=(g+v)*(s+u),n=a2*b2;
         if(!fits(n,b2))continue;
         ok(a1*b1===n&&a1>a2&&b2>b1&&b1>a1&&fits(n,b1),"both indicated divisors are in the window");
         ok(g===gcd(a1,a2),"uniqueness coordinate");
         ++pair[n];
       }
     }
   }
 }
 let first=0,second=0,seenTwo=0;
 for(let n=1;n<=X;++n){
   const r=nn[n];
   ok(r<=Math.ceil((p*p)/(q*q)),"strict sum interval is bounded");
   ok(pair[n]===r*(r-1)/2,"all unordered collision pairs match");
   first+=r; second+=pair[n]; if(r===2)++seenTwo;
 }
 if(p*p<=2*q*q)ok(seenTwo===second,"second moment counts distinct integers in narrow regime");
 const C=p/q;
 results.push({C,first,second,pairMain:+(K*Math.sqrt(X)).toFixed(2),
   firstMain:+((4*C/3)*X**.75-(C*C+.5)*Math.sqrt(X)).toFixed(2)});
}
console.log({checks,X,results});
