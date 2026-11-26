
const gcd=(a,b)=>b?gcd(b,a%b):a;
const rules=[
{R:[8,32,192],S:[[[12,24,48,96],2,2],[[16,64],0,-4]],A:[[[3,9],1,0]]},
{R:[8,32,36,40,72,180,192,240],S:[[[12,24,48,60,96,108,120],2,2],[[16,64,80],0,-4],[[216],0,-8]],A:[[[3,9,27],1,1],[[15,45,135],3,1]]},
{R:[4,16,20,36,40,64,72,240,384,432],S:[[[12,24,48,96,192],2,2],[[60,108,120,216],2,-2],[[8,128],0,-4],[[80,144],0,4],[[32],0,-6]],A:[[[3,45,81],1,-1],[[5,9],1,1],[[15,27],1,0]]},
];
const cmp=([a,b],[c,d])=>a*d-b*c;
function check(rule){
 const candidates=[...rule.S,...rule.A].flatMap(([vs,a,b])=>vs.map(v=>[v,a,b]));
 const qs=rule.R.concat(rule.S.flatMap(([vs])=>vs)), f=[];
 let checks=0;
 for(const q of qs)for(let k=0;k<q;k++)if(gcd(k,q/2)===1){
   checks++;
   const I=candidates.filter(([v,a])=>(4*v*k+a*q)%(4*q)===0)
    .map(([v,,b])=>[[-q*(4+b),4*v],[q*(4-b),4*v]])
    .sort((a,b)=>cmp(a[0],b[0]));
   let t=[-1,1];for(const [l,h] of I){
     if(cmp(l,t)>0)break;
     if(cmp(h,t)>0)t=h;
   }
   if(cmp(t,[1,1])<0)f.push({q,k,t});
 }
 return {checks,fail:f.length,first:f.slice(0,5)};
}


const rows=[
 [96,[[0,1]]],
 [120,[[1,1]]],
 [216,[[2,1]]],
 [864,[[0,1],[1,5],[0,9]]],
 [1080,[[0,1],[0,9],[2,5]]],
 [3000,[[0,1],[2,9],[1,25]]],
 [5400,[[0,3],[0,15],[1,27],[2,25]]],
 [5832,[[0,3],[0,5],[2,25],[2,27]]],
 [9720,[[2,1],[0,45],[2,25],[1,81]]],
];
const results=rules.map(check);
if(JSON.stringify(results.map(z=>[z.checks,z.fail]))!=="[[184,0],[536,0],[882,0]]")throw Error('local check');
const bigGcd=(a,b)=>b?bigGcd(b,a%b):a;
let a=0n,b=1n;
for(let i=0;i<rows.length;i++){
 const [T,row]=rows[i], used=new Set();
 let gain=0;
 for(const [j,s] of row){
   const r=rules[j], A=r.A.flatMap(([v])=>v), S=r.S.flatMap(([v])=>v);
   let x=s;for(const p of [3,5])while(x%p===0)x/=p;
   if(x!==1 || Math.max(...r.R,...S)*s>2*T)throw Error('inadmissible scale');
   gain+=r.R.length-A.length;
   for(const v of [...r.R,...S,...A]){if(used.has(v*s))throw Error('overlap');used.add(v*s);}
 }
 if(gain!==i+1)throw Error('gain');
 [a,b]=[a*15n*BigInt(T)+4n*b,b*15n*BigInt(T)];
 const d=bigGcd(a,b);a/=d;b/=d;
}
if(143n*a<=b || 9n*b+1n*(b-a)>=11n*(b-a))throw Error('claimed bound');
const out={localCases:results.map(z=>z.checks),packs:rows.length,saveFraction:[String(a),String(b)],excessCoefficient:[String(a),String(b-a)]};
if(typeof console==="undefined")text(out);else console.log(out);
