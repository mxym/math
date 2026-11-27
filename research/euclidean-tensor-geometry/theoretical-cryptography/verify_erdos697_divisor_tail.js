"use strict";
// These are finite arithmetic cross-checks, not tests of analytic estimates.
let checked = 0, tuples = 0, residues = 0;
function requireThat(x, msg) {
  ++checked;
  if (!x) throw Error(msg);
}
function gcd(a,b) { for (;b;) [a,b]=[b,a%b]; return a; }
function lcm(a,b) { return a/gcd(a,b)*b; }
function compareGroup(g, id, op, maxQ) {
  for (let q=0;q<=maxQ;++q) {
    const T=2**q-1, all=g**q, sums=new Int32Array(g), pairs=new Int32Array(g), any=new Int32Array(g);
    const vals=[id], count=new Int32Array(g);
    function visit(depth) {
      if (depth===q) {
        ++tuples;
        count.fill(0);
        for(let j=1;j<vals.length;++j) ++count[vals[j]];
        for(let a=0;a<g;++a) {
          sums[a]+=count[a];
          pairs[a]+=count[a]*(count[a]-1);
          any[a]+=Number(count[a]>0);
        }
        return;
      }
      const n=vals.length;
      for(let x=0;x<g;++x) {
        for(let j=0;j<n;++j) vals[n+j]=op(vals[j],x);
        visit(depth+1);
        vals.length=n;
      }
    }
    visit(0);
    for(let a=0;a<g;++a) {
      requireThat(sums[a]*g===all*T,"first moment");
      requireThat(pairs[a]*g*g===all*T*(T-1),"ordered second factorial moment");
      requireThat(any[a]*g<=all*T,"union bound");
      if (T>0) {
        requireThat(any[a]*(T+g-1)>=all*T,"second-moment lower bound");
        requireThat((all-any[a])*T<=all*(g-1),"no-hit bound");
      } else {
        requireThat(any[a]===0,"the empty subset is not a nontrivial witness");
      }
    }
  }
}
for(let g=1;g<=15;++g) compareGroup(g,0,(a,b)=>(a+b)%g,g<=7?6:4);
for(let a=2;a<=4;++a) for(let b=2;b<=5;++b)
  compareGroup(a*b,0,(x,y)=>(x%a+y%a)%a+a*((Math.floor(x/a)+Math.floor(y/a))%b),4);
for(let m=2;m<=25;++m) {
  const list=Array.from({length:m},(_,i)=>i).filter(a=>gcd(m,a)===1);
  compareGroup(list.length,list.indexOf(1),(a,b)=>list.indexOf(list[a]*list[b]%m),list.length<=8?5:3);
}
const primes=[2,3,5,7,11,13,17,19,23,29,31,37,41,43];
function crtExperiment(m,N) {
  const ds=[];
  let period=1;
  for(let d=m+1;d<N;d+=m) {
    ds.push(d); period=lcm(period,d);
    if(period>160000) return;
  }
  let brute=0;
  for(let n=0;n<period;++n) {
    ++residues;
    if(ds.some(d=>n%d===0)) ++brute;
  }
  let denominator=1, weighted=0, all=0;
  const factors=[];
  for(const p of primes) {
    let h=period,e=0,K=1;
    while(h%p===0) {h/=p;++e;K*=p;}
    if(e>0) {factors.push([p,e,K]);denominator*=K;}
  }
  requireThat(denominator===period,"factorization of test period");
  function integrate(i,n,w) {
    if(i===factors.length) {
      all+=w;
      if(ds.some(d=>n%d===0)) weighted+=w;
      return;
    }
    const [p,e,K]=factors[i];
    for(let j=0,k=1;j<=e;++j,k*=p)
      integrate(i+1,n*k,w*(j===e?1:K/k-K/(k*p)));
  }
  integrate(0,1,1);
  requireThat(all===period,"full product mass");
  requireThat(weighted===brute,"exact weighted valuations vs periodic density");
}
for(let m=2;m<=37;++m) for(let N=3;N<=46;++N) crtExperiment(m,N);
for(let n=1;n<=12;++n) {
  const ps=primes.slice(0,n).map(BigInt);
  const common=ps.reduce((x,p)=>x*(p-1n),1n);
  for(let s=0;s<(1<<n);++s) {
    let weightBern=1n, weightOdds=1n,k=0;
    for(let i=0;i<n;++i) {
      if(s>>i&1) {weightOdds*=common/(ps[i]-1n);++k;}
      else weightBern*=ps[i]-1n;
    }
    requireThat(weightOdds*common===weightBern*common**BigInt(k),"conditional odds identity");
  }
}
console.log(JSON.stringify({assertions:checked,groupTuples:tuples,periodResidues:residues}));
