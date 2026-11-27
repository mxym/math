const p=17, P=Array.from({length:289},(_,i)=>[i%17,i/17|0]),m=x=>(x%p+p)%p,R=Array.from({length:p},(_,i)=>i),inv=R.map(a=>R.find(b=>a*b%p===1));
const tr=[0,1,17];function diff(i,j){const [x,y]=P[i],[u,v]=P[j];let a=m(x-u),b=m(y-v),s=a?m(b*inv[a]):17,vv=a||b;return [s,Math.min(vv,17-vv)];}
for(let target of [6]){let visits=0,sets=[],hist={};let allow=Array(18).fill(0);for(let i=0;i<3;i++)for(let j=0;j<i;j++){let [s,v]=diff(tr[i],tr[j]);allow[s]=v;}
function go(C,tail){visits++;if(C.length===target){const d=allow.filter(Boolean).length;hist[d]=(hist[d]||0)+1;sets.push(C);return;}for(let i=0;i<tail.length;i++){let a=tail[i],add=[],ok=true;for(let b of C){const [s,v]=diff(a,b);if(allow[s]&&allow[s]!==v){ok=false;break;}if(!allow[s]){allow[s]=v;add.push(s);}}
 if(ok){let ts=tail.slice(i+1).filter(q=>C.every(b=>{let [s,v]=diff(q,b);return !allow[s]||allow[s]===v;})&&(()=>{let [s,v]=diff(q,a);return !allow[s]||allow[s]===v;})());if(C.length+1+ts.length>=target)go([...C,a],ts);}
 for(let s of add)allow[s]=0;
}}
go(tr,P.map((_,i)=>i).filter(i=>!tr.includes(i)));if(visits!==37118||sets.length!==30360||String(Object.entries(hist))!=="9,300,10,900,11,1920,13,18120,15,9120")throw Error("equal-chord census");console.log({target,visits,hist});}
