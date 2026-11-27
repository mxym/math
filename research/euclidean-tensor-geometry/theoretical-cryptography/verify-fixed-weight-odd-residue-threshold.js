'use strict';
// Small synthetic probability spaces only. No external inputs, secrets or inversion.
// Usage: node verify-fixed-weight-odd-residue-threshold.js
let checks=0, vectors=0, spaces=0;
function check(ok,msg) { if(!ok) throw Error(msg); ++checks; }
const mod=(x,p)=>((x%p)+p)%p;
function field(p,D=0) {
  const q=D?p*p:p;
  const add=D?((x,y)=>mod(x%p+y%p,p)+p*mod((x/p|0)+(y/p|0),p)):((x,y)=>mod(x+y,p));
  const neg=D?(x=>mod(-(x%p),p)+p*mod(-(x/p|0),p)):(x=>mod(-x,p));
  const mul=D?((x,y)=> {
    let a=x%p,b=x/p|0,c=y%p,d=y/p|0;
    return mod(a*c+D*b*d,p)+p*mod(a*d+b*c,p);
  }):((x,y)=>mod(x*y,p));
  function pow(x,e) { let y=1; while(e>0){if(e%2)y=mul(x,y);x=mul(x,x);e=Math.floor(e/2);}return y; }
  const trace=D?(x=>mod(2*(x%p),p)):(x=>x);
  if(D) check(!Array.from({length:p},(_,x)=>x).some(x=>mod(x*x-D,p)===0),'irreducible x^2-D');
  function primitive() {
    for(let g=2;g<q;g++){
      const got=new Set(); for(let j=0;j<q-1;j++) got.add(pow(g,j));
      if(got.size===q-1) return g;
    }
    throw Error('no primitive element');
  }
  return {p,q,add,neg,mul,pow,trace,primitive};
}
function choose(n,k){ let c=1; for(let j=1;j<=k;j++) c=c*(n-j+1)/j; return c; }
function synthetic(p,D,ell,weights) {
  const {q,add,neg,mul,pow,trace,primitive}=field(p,D);
  const d=(q-1)/2,g=primitive(), J=Array.from({length:ell},(_,i)=>2*i+1);
  const keep=J.map((_,h)=>h).filter(h=>J[h]%p!==0);
  const r=keep.length;
  const roots=J.map(e=>pow(g,e));
  const reps=Array.from({length:d},(_,j)=>pow(g,j));
  check(new Set(reps.flatMap(x=>[x,neg(x)])).size===q-1,'antipodal partition');
  check(new Set(roots).size===ell && roots.every(x=>pow(x,d)===neg(1)),'split roots');
  const evaluation=roots.map(root=>reps.map((_,j)=>pow(root,j)));
  for(const k of weights) {
    if(k<1 || k>d) throw Error('weight');
    const hist=new Map(), reduced=new Map();
    const active=[];
    function generate(start,left) {
      if(left===0){
        const value=evaluation.map(row=>active.reduce((s,[j,sgn])=>add(s,sgn?neg(row[j]):row[j]),0));
        const signed=active.map(([j,sgn])=>sgn?neg(reps[j]):reps[j]);
        const moments=J.map(e=>signed.reduce((s,x)=>add(s,pow(x,e)),0));
        check(value.every((x,i)=>x===moments[i]),'evaluation equals signed moments');
        for(let h=0;h<ell;h++) if(J[h]%p===0) check(value[h]===pow(value[(J[h]/p-1)/2],p),'Frobenius graph');
        const key=value.join(','), project=keep.map(h=>value[h]).join(',');
        hist.set(key,(hist.get(key)??0)+1);
        reduced.set(project,(reduced.get(project)??0)+1);
        ++vectors; return;
      }
      for(let j=start;j<=d-left;j++) for(let sgn=0;sgn<2;sgn++){
        active.push([j,sgn]); generate(j+1,left-1); active.pop();
      }
    }
    generate(0,k); ++spaces;
    const M=2**k*choose(d,k), Q=q**r;
    const entries=[...reduced].map(([s,n])=>[s.split(',').map(Number),n]);
    check(hist.size===reduced.size,'graph projection injective');
    check(entries.reduce((s,[,n])=>s+n,0)===M,'input total');
    const tvNumerator=entries.reduce((s,[,n])=>s+Math.abs(n*Q-M),(Q-entries.length)*M);
    check(tvNumerator>=2*M*Math.max(0,Q-M),'support bound');
    if(k<=r && p>2*k-1) {
      check(entries.length===M && entries.every(([,n])=>n===1),'boundary support count');
      check(tvNumerator===2*M*(Q-M),'exact boundary TV');
    }
    if(r===1 && k===1) check(tvNumerator*q===2*M*Q,'one-coordinate weight one');

    // Compare actual additive-phase counts to the exact polynomial product in
    // Z[Z]/(Z^p-1), retaining each coefficient rather than floating-point DFTs.
    const frequencies=Array.from({length:r},(_,j)=>keep.map((_,i)=>+(i===j)));
    frequencies.push(keep.map(()=>1));
    for(let h=1;h<=5;h++) frequencies.push(keep.map((_,j)=>mod(3*h*h+j*h+2*j,q)));
    for(const a of frequencies){
      if(a.every(x=>x===0)) continue;
      const phase=v=>trace(v.reduce((s,x,j)=>add(s,mul(a[j],x)),0));
      const expected=Array(p).fill(0);
      for(const [v,n] of entries) expected[phase(v)]+=n;
      const coeff=Array.from({length:k+1},()=>Array(p).fill(0)); coeff[0][0]=1;
      for(let j=0;j<d;j++){
        const t=phase(keep.map(h=>evaluation[h][j]));
        for(let m=Math.min(j+1,k);m>=1;m--) for(let v=0;v<p;v++)
          coeff[m][v]+=coeff[m-1][mod(v-t,p)]+coeff[m-1][mod(v+t,p)];
      }
      check(expected.every((c,i)=>c===coeff[k][i]),'exact phase count coefficients');
    }
    if(q===31 && r===2 && [1,2,3,4].includes(k))
      console.log('q=31 r=2 k='+k+' exact TV='+tvNumerator+'/'+(2*M*Q));
  }
}
synthetic(5,0,2,[1,2]);
synthetic(7,0,2,[1,2,3]);
synthetic(11,0,3,[1,2,3,4,5]);
synthetic(13,0,4,[1,2,3,4,5,6]);
synthetic(17,0,4,[1,2,3,4,5,6,7,8]);
synthetic(23,0,4,[2,3,4,5,11]);
synthetic(31,0,2,[1,2,3,4]);
synthetic(3,2,2,[1,2,3,4]);
synthetic(3,2,4,[1,2,3,4]);
synthetic(5,2,4,[1,2,3,4,5,12]);
synthetic(7,3,5,[1,2,3,4]);
console.log('PASS: '+checks+' exact assertions on '+vectors+' vectors in '+spaces+' synthetic spaces');
