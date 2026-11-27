"use strict";
const A = (test) => { if (!test) throw new Error("certificate failure"); };
const p = 599, target = 4*p;
for (let d = 2; d*d <= p; d++) A(p % d !== 0);
A(p-1 === 2*13*23);
const odds = Array.from({length: Math.floor((Math.sqrt(target)+1)/2)}, (_,i) => 2*i+1);
const candidates = q => odds.filter(x => x%q === 1 || x%q === q-1);
A(JSON.stringify(candidates(13)) === "[1,25,27]");
A(JSON.stringify(candidates(23)) === "[1,45,47]");
const special = new Set([...candidates(13), ...candidates(23)]);
const direct = [];
for (const a of odds) for (const b of odds) if (b >= a)
  for (const c of odds) if (c >= b) for (const d of odds) if (d >= c)
    if (a*a+b*b+c*c+d*d === target) direct.push([a,b,c,d]);
A(direct.length === 28);
const two = direct.filter(q => q.filter(x => special.has(x)).length === 2);
A(direct.every(q => q.filter(x => special.has(x)).length <= 2));
A(JSON.stringify(two) === "[[1,3,19,45],[1,9,17,45],[1,21,27,35],[9,25,27,31]]");
const specialList = [...special].sort((a,b)=>a-b), squares = new Set(odds.map(x=>x*x));
for(const a of specialList) for(const b of specialList) for(const c of specialList)
  A(!squares.has(target-a*a-b*b-c*c));
for(const [a,b,c,d] of two){
  const T=[[a,-b,-c,-d],[b,a,-d,c],[c,d,a,-b],[d,-c,b,a]];
  for(let i=0;i<4;i++) for(let j=0;j<4;j++){
    const dot=T[i].reduce((x,y,k)=>x+y*T[j][k],0);
    A(dot === (i===j ? target : 0));
  }
}
console.log({p, profiles:direct.length, maximumSpecialRows:2, twoRowProfiles:two});
