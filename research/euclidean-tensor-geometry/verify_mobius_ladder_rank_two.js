// Node.js exact expansion by (degree-2 left, degree-3 left, degree-2 right, degree-3 right).
'use strict';
const edges=[];
for(let i=0;i<10;i++)edges.push([i,(i+1)%10]);
for(let i=0;i<5;i++)edges.push([i,i+5]);
const counts={};
for(let mask=0;mask<2**edges.length;mask++){
 const degrees=Array(10).fill(0);
 for(let e=0;e<edges.length;e++)if(mask&(1<<e)){const [i,j]=edges[e];degrees[i]++;degrees[j]++;}
 if(degrees.includes(1))continue;
 const m=Array(4).fill(0);
 for(let i=0;i<10;i++)if(degrees[i]>=2)m[2*(i%2)+degrees[i]-2]++;
 const key=m.join('');
 counts[key]=(counts[key]||0)+1;
}
const got=Object.entries(counts).sort(([a],[b])=>a.localeCompare(b));
const expected=[["0000",1],["0432",5],["0505",1],["1240",5],["1341",30],["1414",15],["2020",5],["2121",5],["2222",15],["2250",35],["2323",75],["3030",15],["3131",60],["3204",5],["3232",145],["4012",5],["4040",30],["4113",30],["4141",95],["5022",35],["5050",13]];
if(JSON.stringify(expected)!==JSON.stringify(got))throw Error(JSON.stringify(got));
console.log(got);
