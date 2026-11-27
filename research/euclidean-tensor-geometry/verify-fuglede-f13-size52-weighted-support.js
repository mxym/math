'use strict';
const p=13, r=Array.from({length:p},(_,i)=>i), mod=x=>(x%p+p)%p;
const assert=(b,s)=>{if(!b)throw Error(s);};
const quad=r.map(()=>[]);
const profiles={};
for(let d=2;d<=4;d++){
  const hist={};
  function visit(a,c){
    if(c.length<d-1){for(const x of r)visit(a,[...c,x]);return;}
    const coeff=[...c,0,a];
    const f=r.map(t=>coeff.reduceRight((z,k)=>mod(z*t+k),0));
    const l=(52-f.reduce((s,k)=>s+k,0))/13;
    if(!Number.isInteger(l)||l<0||l>f.filter(n=>n===0).length)return;
    const w=(f.reduce((s,n)=>s+n*(n-1)/2,0)+78*l-78)/13;
    assert(Number.isInteger(w)&&w>=6-d,"inadmissible weight");
    hist[w]=(hist[w]||0)+1;
    if(d===2)quad[a].push(w);
  }
  for(let a=1;a<p;a++)visit(a,[]);
  profiles[d]=hist;
}
assert(JSON.stringify(profiles)===JSON.stringify({
  2:{4:6,6:6},
  3:{3:20,4:12,5:24,6:48,7:12,8:24,9:4},
  4:{2:30,3:108,4:309,5:360,6:399,7:312,8:183,9:57,10:27}
}),"wrong census");
let leading=0, tight=0;
for(let s=2;s<p;s++)for(let a3=1;a3<p;a3++){
  const a2=mod(-s*a3),a0=mod(-a2-a3),a1=mod(-a2-s*s*a3);
  if(!a0||!a1||!a2)continue;
  leading++;
  for(const w0 of quad[a0])for(const w1 of quad[a1])
    for(const w2 of quad[a2])for(const w3 of quad[a3])
      if(w0+w1+w2+w3===18)tight++;
}
assert(leading===132&&tight===0,"quadratic pencil");
for(let b=5;b<=9;b++){
  const lo=b===5?3:2;
  const max=(18-(b-1)*lo)**2+(b-1)*lo**2;
  assert(max<=12*b+12,"local squared weight bound");
}
const dif=14n*330n-18n*183n;
let min=null;
for(let n=92n;n<=165n;n++){
  const gap=dif*dif*n-13n*(183n-n)*(183n*(12n*n+220n)-330n*330n);
  assert(gap>0n,"incidence inequality");
  if(min===null||gap<min)min=gap;
}
console.log({profiles,leading,tight,incidenceCases:74,minExactGap:String(min)});
