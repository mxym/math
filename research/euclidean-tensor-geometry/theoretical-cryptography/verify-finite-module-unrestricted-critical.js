const norm=(x,q)=>(x%q+q)%q;
function cert(B,w,q,roots){
const d=2,C=d*B,H={seen:0,orbits:0,shell:0,fullExceptional:0,inactive:0,dormantDegreeCounts:[0,0,0],weightedInactiveNumerator:0}; 
function cmp(a,b){for(let i=0;i<C;i++){if(a[i]!==b[i])return a[i]-b[i];}return 0;}
function y(a){const out=[];for(let i=0;i<C;i+=2)out.push(-a[i+1],a[i]);return out;}
function visit(a,E){
 if(a.length<C){const s=Math.floor(Math.sqrt(w-E));for(let k=-s;k<=s;k++)visit(a.concat(k),E+k*k);return;}
 if(!E)return;H.seen++;
 const v=y(a),na=a.map(x=>-x),nv=v.map(x=>-x);if([v,na,nv].some(b=>cmp(a,b)>0))return;H.orbits++;
 const rows=Array.from({length:B},(_,i)=>a.slice(2*i,2*i+2));const active=rows.filter(x=>x[0]||x[1]),s=active.length;
 const miss=roots.filter(r=>rows.every(x=>norm(x[0]+r*x[1],q)===0)).length;
 if(q**miss * s>w)throw Error("norm marginal bound");
 if(miss){H.inactive++;H.dormantDegreeCounts[miss]++;H.weightedInactiveNumerator+=q**miss;}
 else if(s===w&&E===w)H.shell++;else H.fullExceptional++;
}
visit([],0);
if(H.seen!==4*H.orbits||H.orbits!==H.shell+H.fullExceptional+H.inactive)throw Error("orbit");
if(B===6&&w===5&&q===5&&(H.shell!==1536||H.inactive!==12||H.weightedInactiveNumerator!==60))throw Error("toy count");
return {B,w,q,...H};
}
const results=[cert(6,4,5,[2,3]),cert(6,5,5,[2,3])];
console.log(JSON.stringify(results));
