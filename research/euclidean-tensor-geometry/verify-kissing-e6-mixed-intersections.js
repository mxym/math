'use strict';
/* Finite pieces of the mixed-E6 intersection theorem. No dependencies. */
const T=[...Array.from({length:6},(_,k)=>['A'+(k+1),k+1,(k+1)*(k+2),k+2]),...[4,5,6].map(k=>['D'+k,k,2*k*(k-1),4]),['E6',6,72,3]];
const lists=[];function factors(i,r,c,d,n){if(c>=24)lists.push([n.join('+'),c,r,d]);for(let j=i;j<T.length;j++){const [k,rr,cc,dd]=T[j];if(r+rr<=6)factors(j,r+rr,c+cc,d*dd,n.concat(k));}}factors(0,0,0,1,[]);
lists.sort((a,b)=>b[1]-a[1]||a[0].localeCompare(b[0]));
const wanted=['E6','D6','A1+D5','A6','D5','A1+A5','A2+D4','A5','A1+A1+D4','A1+D4','A2+A4','A1+A1+A4','A3+A3','D4'];
if(lists.map(x=>x[0]).sort().join()!==wanted.sort().join())throw Error('ADE table');
console.log('root systems with 24 or more roots in rank at most six:',lists);
const D=Array.from({length:4},(_,k)=>[1,-1].map(s=>Array.from({length:4},(_,i)=>i===k?2*s:0))).flat();
const C=[D,[],[]];for(let m=0;m<16;m++){const v=Array.from({length:4},(_,k)=>m>>k&1?-1:1);C[v.filter(x=>x<0).length%2+1].push(v);}
const dot=(u,v)=>u.reduce((a,x,i)=>a+x*v[i],0);
let graphs=0;
for(let i=0;i<3;i++)for(let j=i+1;j<3;j++)for(const s of [-1,1]){
 if(C[i].some(a=>C[j].some(b=>Math.abs(dot(a,b))!==2)))throw Error('mutual unbiasedness');
 const ns=Array.from({length:16},()=>[]);for(let a=0;a<8;a++)for(let b=0;b<8;b++)if(dot(C[i][a],C[j][b])===2*s){ns[a].push(b+8);ns[b+8].push(a);}
 const Q=[0],seen=new Set([0]);for(const a of Q)for(const b of ns[a])if(!seen.has(b)){Q.push(b);seen.add(b);}
 if(seen.size!==16||ns.some(v=>v.length!==4))throw Error('fiber graph');graphs++;
}
const perms=a=>a.length?a.flatMap((x,k)=>perms(a.filter((_,j)=>j!==k)).map(v=>[x,...v])):[[]];
const dist=(a,b,n)=>Math.min((a-b+n)%n,(b-a+n)%n);
let sectors=0;
for(const delta of [0,1])for(const colors of perms([0,1,2])){
 // projective circumference 6 in units of 30 degrees. delta=1 tests the
 // whole open 0<delta<2 sector, where strict distance <2 never changes.
 if(delta===0&&colors.some((c,i)=>c===i))continue;
 for(let i=0;i<3;i++){
  if(![0,1,2].some(j=>i!==colors[j]&&dist(2*i,2*j+delta,6)<2))throw Error('unforced first fiber');
  if(![0,1,2].some(j=>j!==colors[i]&&dist(2*j,2*i+delta,6)<2))throw Error('unforced second fiber');
 }sectors++;
}
function pm(A){if(!A.length)return [[]];return A.slice(1).flatMap(b=>pm(A.filter(x=>x!==A[0]&&x!==b)).map(v=>[[A[0],b],...v]));}
const admiss=pm([0,1,2,3,4,5]).filter(P=>P.every(([a,b])=>dist(a,b,6)>=2));
if(admiss.some(P=>!P.some(([a,b])=>dist(a,b,6)===3)))throw Error('no diameter');
console.log({fiberGraphs:graphs,relativeSectors:sectors,hexagonMatchings:admiss.length,allContainDiameter:true});
