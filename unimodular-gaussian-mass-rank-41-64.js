'use strict';
// Exact rational proof certificates for short shells and all real nomes.
let checks=0;
function check(x,m){if(!x)throw Error(m);checks++;}
const abs=x=>x<0n?-x:x;
function gcd(x,y){x=abs(x);y=abs(y);while(y){[x,y]=[y,x%y];}return x;}
function f(x,y=1){x=BigInt(x);y=BigInt(y);if(y<0n){x=-x;y=-y;} if(!y)throw Error("zero denominator");let g=gcd(x,y);return [x/g,y/g];}
const plus=(x,y)=>f(x[0]*y[1]+y[0]*x[1],x[1]*y[1]);
const neg=x=>[-x[0],x[1]],sub=(x,y)=>plus(x,neg(y)),times=(x,y)=>f(x[0]*y[0],x[1]*y[1]);
const div=(x,y)=>f(x[0]*y[1],x[1]*y[0]),gt=(x,y)=>x[0]*y[1]>y[0]*x[1],eq=(x,y)=>x[0]===y[0]&&x[1]===y[1];
function pow(x,k){return f(x[0]**BigInt(k),x[1]**BigInt(k));}
function binom(a,k){if(k>a)return 0n;let r=1n;for(let i=1;i<=k;i++)r=r*BigInt(a-i+1)/BigInt(i);return r;}
function gegen(n,x,m){
 const t=[f(1),x];
 for(let j=1;j<m;j++)t.push(div(sub(times(times(f(2*j+n-2),x),t[j]),times(f(j),t[j-1])),f(j+n-2)));
 return t;
}
const polys={
 38:[[2,f(8)],[6,f(3300)]],39:[[4,f(140)],[8,f(21400)]],41:[[4,f(7400)],[8,f(72500)]],
 48:[[4,f(16)],[6,f(3800)],[10,f(201000)]],
 56:[[2,f(178,25)],[6,f(48211,10)],[10,f(368346)]],
 64:[[2,f(1253,100)],[6,f(26071,5)],[10,f(748230)]]
};
function value(n,x){
 const tab=gegen(n,x,polys[n].at(-1)[0]);
 return polys[n].reduce((v,[j,b])=>plus(v,times(tab[j],b)),f(1));
}
const tests=[
 [38,[f(0),f(1,3)],3309,null],
 [39,[f(1,7),f(3,7)],21541,null],
 [41,[f(1,9),f(1,3)],79901,[f(5,9),473]],
 [48,[f(0),f(1,4),f(1,2)],204817,[f(3,4),5146]],
 [56,[f(0),f(1,4),f(1,2)],373176,[f(3,4),10590]],
 [64,[f(0),f(1,4),f(1,2)],753458,[f(3,4),23195]]
];
for(const [n,ang,p1,bad] of tests){
 for(const [j,c] of polys[n])check(j%2===0&&gt(c,f(0)),'degree and sign');
 for(const t of ang){check(gt(f(0),value(n,t)),'common inner product strict sign');check(eq(value(n,t),value(n,neg(t))),'evenness');}
 const tend=gegen(n,f(1),10);for(const t of tend)check(eq(t,f(1)),'normalized at 1');
 check(!gt(value(n,f(1)),f(p1)),'diagonal bound');
 if(bad)check(gt(f(bad[1]),value(n,bad[0])),'rare positive upper bound');
}
check(2*(79901+135*473)===287512,'rank 41 sparse root cover');
check(2n*binom(14,6)+82n*binom(13,4)+3280n===67916n,'rank 41 large D projective fiber cover');
const shadow={33:0,34:2,35:2,36:72,37:1406,38:6618,39:43082,40:6240,41:67916};
let odd=[];
for(let n=33;n<=41;n++){
 for(const sparse of (n===41?[false,true]:[false])){
   const A2=(sparse?41*60:2*n*(n-1))+2*n*n-46*n,B=sparse?287512:shadow[n];
   check(A2>0&&n<96&&n>=32,'signs in polynomial domination');
   const gap=sub(f(2*n),plus(f(A2,64),f(BigInt(B*(n-32)),1n<<BigInt(n-24))));
   check(gt(gap,f(0)),'strict odd all-width bound');
   odd.push([n,sparse?"low root density":"standard / large D",gap.join("/")]);
 }
}
const evens=[[48,4279426,204817,5146],[56,10065552,373176,10590],[64,24887476,753458,23195]];
let even=[];
for(const [n,B,p1,pbad] of evens){
 const m=n/8,R=2*n*(n-1),a=R-240*m,k=240*m-744;
 check(B===2*(p1+8*(n-1)*pbad),'norm-four count from rare adjacency');
 check(a===128*m*(m-2)&&a>0&&k>0,'even root coefficient');
 check(gt(f(27,64),f(k,4096)),'root coefficient has positive net effect');
 const C=B + m*(28800*m-151920)-k*R;
 check(C=== B-(2160*m+57600*m*(m-1)/2)-k*(R-240*m)&&C>0,'Fourier coefficient calculation');
 const e=f(3,4),u=f(1,64);
 const bound=plus(pow(e,m),plus(times(f(a),times(pow(e,m-3),pow(u,2))),times(f(C),times(pow(e,m-6),pow(u,4)))));
 check(gt(f(1),bound),'strict even left endpoint');
 const deriv=times(f(a,256),times(pow(e,m-4),sub(f(m-3),times(f(m-2),e))));
 check(gt(f(4),deriv),'worst middle derivative <4');
 check((m-4)-(m-2)*3/4<0,'middle derivative is decreasing');
 check((m-6)/4-9/4<0&&gt(plus(f(1),plus(times(f(2),e),times(f(3),pow(e,2)))),f(4)),'remaining factor signs');
 even.push([n,C,bound.join("/")]);
}
console.log(JSON.stringify({checks,odd,even}));
