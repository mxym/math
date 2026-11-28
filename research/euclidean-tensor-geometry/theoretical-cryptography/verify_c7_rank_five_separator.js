'use strict';
// Standard-library exact verifier. Run next to c7_rank_five_separator_certificate.json.
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const tables=JSON.parse(fs.readFileSync(path.join(__dirname,'c7_rank_five_separator_certificate.json'),'utf8'));

const F=7,D=343,Q=49, FULL=(1<<24)-1;
function digits(x,n=3){return Array.from({length:n},()=>{const y=x%F;x=Math.floor(x/F);return y;});}
function num(a){return a.reduceRight((v,w)=>F*v+w,0);}
const all = Array.from({length:D},(_,x)=>digits(x));
const neg = all.map(x=>num(x.map(t=>(F-t)%F)));
const add = all.map(a=>Int16Array.from(all,b=>num(b.map((v,j)=>(a[j]+v)%F))));
const ray=all.map((a,i)=>i===0?0:Math.min(...Array.from({length:6},(_,j)=>num(a.map(x=>(j+1)*x%F)))));
const positives=all.map((_,i)=>i).filter(i=>i<neg[i]);
const plane=positives.filter(i=>i<Q);
assert.equal(plane.length,24);
const indexOf=new Int16Array(Q).fill(-1);
for(let i=0;i<24;i++)indexOf[plane[i]]=indexOf[neg[plane[i]]]=i;
const masksOfLines=[];
for(const l of [7,...Array.from({length:7},(_,i)=>1+7*i)]){
    let A=0,x=0;
    for(let j=1;j<7;j++){x=add[x][l];A|=1<<indexOf[x];}
    masksOfLines.push(A);
}
const hasLine=A=>masksOfLines.some(m=>(A&m)===m);
const maps=[];
for(let a=0;a<7;a++)for(let b=0;b<7;b++)for(let c=0;c<7;c++)for(let d=0;d<7;d++)
    if((a*d-b*c)%7!==0)maps.push(plane.map(v=>{
        const [x,y]=all[v];
        return 1<<indexOf[(a*x+b*y)%7+7*((c*x+d*y)%7)];
    }));
function expand(A,cover){
    for(const perm of maps){
        let B=0;
        for(let j=0;j<24;j++)if(A&(1<<j))B|=perm[j];
        cover.add(B);
    }
}
function signedAdd(supp,h){
    const seen=new Uint8Array(D),out=[];
    for(const x of supp)for(const v of [x,add[x][h],add[x][neg[h]]])
        if(!seen[v]){seen[v]=1;out.push(v);}
    return [seen,out];
}
function fromColumns(cols){
    let M=new Uint8Array(D);M[0]=1;
    let support=[0];
    for(const v of cols){assert.equal(M[v],0);[M,support]=signedAdd(support,v);}
    return M;
}
function toMask(M,h=0){
    let A=0;
    for(let i=0;i<24;i++){
        const x=plane[i];
        if(M[x]||h&&(M[add[x][h]]||M[add[x][neg[h]]]))A|=1<<i;
    }
    return A;
}

const C=100000000n,Z=1000000n;
const intervals=[
    [2n*C,2n*C], [124697960n,124697961n],
    [-44504187n,-44504186n],[-180193774n,-180193773n],
];
function evalPoly(x){return x*x*x+C*x*x-2n*C*C*x-C*C*C;}
function abs(x){return x<0n?-x:x;}
for(const [l,u] of intervals.slice(1))assert(evalPoly(l)*evalPoly(u)<0n);
assert(intervals[3][1]<intervals[2][0]&&intervals[2][1]<intervals[1][0]);
const K=[0,...plane].map(u=>plane.map(v=>{
    const r=(all[u][0]*all[v][0]+all[u][1]*all[v][1])%F;
    return intervals[Math.min(r,F-r)];
}));

function certificate(group,capNum,capDen){
    const covered=new Set(), used=new Set();
    for(const [mask,duals] of group){
        assert(Number.isInteger(mask)&&mask>0&&mask<=FULL&&!used.has(mask));used.add(mask);
        let W=0n;
        const weights=[];
        for(const [i,w] of duals){
            assert(Number.isInteger(i)&&i>=0&&i<25&&weights[i]===undefined);
            assert(Number.isSafeInteger(w)&&w>0);
            weights[i]=BigInt(w);
            W+=BigInt(w);
        }
        let total=W*C;
        for(let v=0;v<24;v++)if(!(mask&(1<<v))){
            let l=2n*Z*C,u=l;
            for(let i=0;i<weights.length;i++)if(weights[i]!==undefined){
                l+=weights[i]*K[i][v][0];u+=weights[i]*K[i][v][1];
            }
            total+=abs(l)>abs(u)?abs(l):abs(u);
        }
        assert(BigInt(capDen)*(total+Z*C)<=BigInt(capNum)*Z*C,mask);
        expand(mask,covered);
    }
    return covered;
}
const sizes=[50,191,83,5,1];
assert.deepEqual(tables.map(l=>l.length),sizes);
const [S4,S5,S6,P4,P3]=tables.map((t,i)=>certificate(t,...[[16,1],[8,1],[15,4],[9,4],[5,1]][i]));
function bounds3(){
    let totals=[0,0,0];
    const seen=[new Set(),new Set(),new Set()];
    for(let a=0;a<4;a++)for(let b=a;b<4;b++){
        const B=[1+49*a,7+49*b,49], rays=new Set(B.map(x=>ray[x]));
        const pool=positives.filter(x=>!rays.has(ray[x]));
        let M0, supp=[0];
        for(const v of B)[M0,supp]=signedAdd(supp,v);
        let counts=[0,0,0];
        for(let i=0;i<pool.length;i++){
            const x=pool[i];if(M0[x])continue;
            const [M1,L1]=signedAdd(supp,x);
            const p=toMask(M1);
            assert(hasLine(p)||S4.has(p));seen[0].add(p);counts[0]++;
            for(let j=i+1;j<pool.length;j++){
                const y=pool[j];if(M1[y]||ray[y]===ray[x])continue;
                const [M2,L2]=signedAdd(L1,y);
                const q=toMask(M2);
                assert(hasLine(q)||S5.has(q));seen[1].add(q);counts[1]++;
                for(let k=j+1;k<pool.length;k++){
                    const z=pool[k];if(M2[z]||ray[z]===ray[x]||ray[z]===ray[y])continue;
                    const r=toMask(M2,z);
                    assert(S6.has(r));seen[2].add(r);counts[2]++;
                }
            }
        }
        assert.deepEqual(counts,[152,9561,219900]);
        totals=totals.map((x,i)=>x+counts[i]);
    }
    assert.deepEqual(seen.map(s=>s.size),[831,50360,14737]);
    return totals;
}
function bounds2(){
    const B=[1,7], base=fromColumns(B), rays=new Set(B.map(x=>ray[x]));
    const pool=plane.filter(x=>!rays.has(ray[x]));
    let count=0,min=7;
    for(let i=0;i<pool.length;i++){
        const x=pool[i];if(base[x])continue;
        const M=fromColumns([...B,x]);
        for(let j=i+1;j<pool.length;j++){
            const y=pool[j];if(M[y]||ray[x]===ray[y])continue;
            const S=fromColumns([...B,x,y]);count++;
            const A=toMask(S);
            assert(P4.has(A));
            for(const l of masksOfLines){
                const bits=(A&l).toString(2).replace(/0/g,'').length;
                assert(bits>=2);min=Math.min(min,1+2*bits);
            }
        }
    }
    assert(P3.has(toMask(fromColumns([1,7,22])))); // (1,3) = 22
    assert.equal(count,61);assert.equal(min,5);
}
function scalarChecks(){
    // The positive 2 cos(pi/7) is -c_3 in the above root ordering.
    const U=-intervals[3][0], top=1659n, bot=500n;
    assert(7n*U*bot<top*(2n*C+U));
    const L=-intervals[3][1];
    assert(7n*L*200n>663n*(2n*C+L));
    assert(663n**13n>7n**8n*200n**13n);
    for(const [rank,n] of [[1,3],[2,6],[3,8],[4,11],[5,14]])
        assert(top**BigInt(n)<7n**BigInt(n-rank)*bot**BigInt(n));
    for(const [a,b,n,k] of [[1,1,8,5],[9,4,9,6],[16,1,9,7],[8,1,8,6],[15,4,7,5],[5,1,10,7]])
        assert(BigInt(a)*top**BigInt(n)<BigInt(b)*7n**BigInt(k)*bot**BigInt(n));
    for(const cols of [[1,2],[1,7,9,11,22]]){
        const seen=new Set([0]);
        for(const h of cols)for(const x of [...seen])seen.add(add[x][h]);
        assert.equal(seen.size,1<<cols.length);
    }
}
scalarChecks();bounds2();const totals=bounds3();
console.log('PASS',sizes,'rational Fourier tables;',totals,'normalized rank-three systems');
