// A4 parabolic rotation parity graph; all threshold signs are exact.
'use strict';const A=[0,1,2,3,4];const V=A.map(i=>({S:[i],a:2,b:0}));for(const i of A)for(const j of A)if(j>i)for(const h of [-1,1])V.push({S:[i,j],a:-1,b:h});V.push({S:[],a:0,b:2});const T=[];for(const [i,u] of V.entries())for(const [j,v] of V.entries()){const C=10*u.S.filter(x=>v.S.includes(x)).length-2*u.S.length*v.S.length,D=3*u.a*v.a+5*u.b*v.b,E=u.b*v.a-u.a*v.b;T.push({i,j,C,D,E});}

const abs=z=>z<0n?-z:z,sg=z=>z<0n?-1:z>0n?1:0;function gcd(a,b){return b?gcd(b,a%b):abs(a);}
const rat=(p,q=1n)=>{if(!q)throw Error('zero denominator');const g=gcd(p,q)*(q<0n?-1n:1n);return {p:p/g,q:q/g};};
const rk=r=>r.q?r.p+'/'+r.q:[r.a,r.b,r.c,r.s].join(':');
function comp(r,p,q=1n){ // sign(r-p/q) with q normalized positive.
 if(q<0n)return comp(r,-p,-q);if(r.q)return sg(r.p*q-p*r.q);
 const x=-r.b*q-2n*r.a*p,s=r.s;if(sg(x)===s||!x)return s;
 return s*sg(q*q*r.dis-x*x);
}
function addRoot(a,b,c){
 if(!a)return b?[rat(-c,b)]:[];const g=gcd(gcd(a,b),c)*(a<0n?-1n:1n);a/=g;b/=g;c/=g;
 const dis=b*b-4n*a*c;if(dis<0n)return [];let sq=0n;while((sq+1n)**2n<=dis)sq++;
 if(sq*sq===dis)return [-1n,1n].map(k=>rat(-b+k*sq,2n*a));
 return [-1,1].map(s=>({a,b,c,s,dis}));
}
function coeff({C,D,E},t){return [BigInt(C-t-D),BigInt(30*E),BigInt(15*(C-t+D))];}
const roots=new Map();for(const v of T)for(const t of [-20,-10,10,20])for(const r of addRoot(...coeff(v,t)))if(comp(r,0n)>=0)roots.set(rk(r),r);
const gaps=[[1,1],[2,1],[9,4],[5,2],[31,10],[4,1],[6,1],[7,1],[9,1],[12,1],[20,1],[40,1]].map(([p,q])=>rat(BigInt(p),BigInt(q)));
if(gaps.some((r,i)=>i&&comp(r,gaps[i-1].p,gaps[i-1].q)<=0))throw Error('samples not increasing');
const ends=gaps.map((g,i)=>[...roots.values()].filter(r=>comp(r,g.p,g.q)<0&&(!i||comp(r,gaps[i-1].p,gaps[i-1].q)>0)));
if(roots.size!==gaps.length||ends.some(z=>z.length!==1)||comp(ends[0][0],0n)!==0)throw Error('incomplete isolation');
function signAt(y,v,t){
 const [a,b,c]=coeff(v,t);if(!y)return sg(a);if(y.q)return sg(a*y.p*y.p+b*y.p*y.q+c*y.q*y.q);
 const u=b*y.a-a*y.b,z=c*y.a-a*y.c;if(!u)return sg(z);return sg(u)*comp(y,-z,u);
}
function test(y){const edges=Array.from({length:52},()=>[]);let common=10;
 for(const v of T){let s;if(signAt(y,v,10)>0)s=-1;else if(signAt(y,v,-10)<0)s=1;else continue;
 if(signAt(y,v,-20*s)===0){s=-s;common++;}
 edges[v.i].push([26+v.j,s]);edges[26+v.j].push([v.i,s]);}
 const signs=new Int8Array(52);let ok=true;for(let i=0;i<52;i++)if(!signs[i]){signs[i]=1;const q=[i];for(let k=0;k<q.length;k++)for(const [v,s] of edges[q[k]]){if(!signs[v]){q.push(v);signs[v]=s*signs[q[k]];}else if(signs[v]!==s*signs[q[k]])ok=false;}}
 return [ok,common];
}
const records=[];for(let i=0;i<ends.length;i++){const y=ends[i][0],r=test(y);records.push([rk(y),r]);const special=comp(y,0n)===0?36:comp(y,5n)===0?20:10;
 if(r[1]!==special||r[0]!== (special>10)||JSON.stringify(test(gaps[i]))!=='[false,10]')throw Error('atlas');
}if(JSON.stringify(test(null))!=='[false,11]')throw Error('infinity');console.log(records);

{
function determinant(matrix) {
  const m = matrix.map(row => row.slice());
  let previous = 1n;
  let sign = 1n;
  for (let k = 0; k < 4; k++) {
    const pivotRow = m.findIndex((row, i) => i >= k && row[k] !== 0n);
    if (pivotRow < 0) return 0n;
    if (pivotRow !== k) {
      [m[k], m[pivotRow]] = [m[pivotRow], m[k]];
      sign = -sign;
    }
    const pivot = m[k][k];
    for (let i = k + 1; i < 5; i++) {
      for (let j = k + 1; j < 5; j++) {
        const numerator = m[i][j] * pivot - m[i][k] * m[k][j];
        if (numerator % previous !== 0n) throw Error('Nonexact Bareiss division');
        m[i][j] = numerator / previous;
      }
    }
    previous = pivot;
  }
  return sign * m[4][4];
}

function gcd(a, b) {
  if (a < 0n) a = -a;
  if (b < 0n) b = -b;
  while (b !== 0n) [a, b] = [b, a % b];
  return a;
}

function certify(second){const rows=[];for(let i=0;i<4;i++){const q=[0n,0n,0n,0n,0n];q[i]=1n;q[i+1]=-1n;rows.push([q,0n]);}rows.push([[0n,0n,0n,0n,1n],0n],[[1n,1n,1n,1n,-1n],2n],...(second?[[[1n,0n,0n,0n,-1n],1n],[[4n,4n,4n,4n,4n],9n]]:[[[1n,0n,0n,0n,0n],1n],[[0n,0n,0n,1n,1n],1n]]));
const rel=[];function go(J,k){if(J.length<5){for(let i=k;i<=rows.length-5+J.length;i++)go(J.concat([i]),i+1);return;}const A=J.map(i=>rows[i][0]),b=J.map(i=>rows[i][1]);let D=determinant(A);if(!D)return;const P=b.map((_,i)=>determinant(A.map((r,j)=>r.map((t,k)=>k===i?b[j]:t))));if(D<0n){D=-D;for(let i=0;i<5;i++)P[i]*=-1n;}
 if(rows.some(([r,b],i)=>{const z=r.reduce((a,t,j)=>a+t*P[j],0n)-D*b;return i<5?z<0n:z>0n;}))return;
 const L=rows[5][0].reduce((a,t,i)=>a+t*P[i],0n),q=3n*P.reduce((a,t)=>a+t*t,0n)+(2n*D-L)**2n-6n*D*D;
 if(q>=0n){if(q>0n)throw Error('positive vertex');const isRoot=P[0]===D&&P[1]===D&&P.slice(2).every(z=>!z),special=P[0]===D&&P.slice(1).every(z=>2n*z===D);if(!isRoot&&(second||!special))throw Error('unexpected equality');rel.push(isRoot?'root':'exceptional');}}
go([],0);if(!rel.includes('root')||!second&&!rel.includes('exceptional'))throw Error('missing witness');console.log([...new Set(rel)]);}
certify(false);certify(true);
}
{
const n=6,ix=[0,1,2,3,4,5],G=ix.map(i=>ix.map(j=>i===j?2:((i<5&&j<5&&Math.abs(i-j)===1)||(Math.min(i,j)===2&&Math.max(i,j)===5))?-1:0));const dot=(a,b)=>a.reduce((s,t,i)=>s+t*b[i],0);
const roots=ix.map(i=>ix.map(j=>+(i===j))),known=new Set(roots.map(r=>r.join()));for(const r of roots)for(const i of ix){const s=r.slice();s[i]-=dot(r,G[i]);if(!known.has(s.join())){known.add(s.join());roots.push(s);}}
const T=roots.filter(v=>v.every(t=>t>=0));const P=T.map(r=>T.map(v=>dot(r,G.map(g=>dot(g,v)))));
if(roots.length!==72||P.some(r=>r.filter(x=>x===0).length!==15))throw Error('A5 centralizer count');
}
