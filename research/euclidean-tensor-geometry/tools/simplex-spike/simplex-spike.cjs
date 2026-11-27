#!/usr/bin/env node
'use strict';

// Usage: node simplex-spike.cjs < input.json
// Input: {"lambda":["1/2","1/2","0"],"a":["1/2","1/2","-1"]}
// Values: JSON safe integers, or strings containing integers or fractions p/q.
// All reported numbers are reduced exact rational strings.
const fs = require('node:fs');

function gcd(a,b) {
  if (a < 0n) a = -a;
  while (b) [a,b] = [b,a%b];
  return a;
}
class Q {
  constructor(n,d=1n) {
    if (d===0n) throw new Error('zero denominator');
    if (d<0n) { n=-n; d=-d; }
    const g=gcd(n,d);
    this.n=n/g;
    this.d=d/g;
  }
  static parse(x) {
    if (typeof x==='number' && Number.isSafeInteger(x)) return new Q(BigInt(x));
    if (typeof x==='string' && /^[+-]?[0-9]+(?:\/[+-]?[0-9]+)?$/.test(x)) {
      const [n,d='1']=x.split('/');
      return new Q(BigInt(n),BigInt(d));
    }
    throw new Error('rational entries must be quoted integers/fractions or JSON safe integers');
  }
  add(b) {return new Q(this.n*b.d+b.n*this.d,this.d*b.d);}
  sub(b) {return this.add(b.neg());}
  neg() {return new Q(-this.n,this.d);}
  mul(b) {return new Q(this.n*b.n,this.d*b.d);}
  div(b) {return new Q(this.n*b.d,this.d*b.n);}
  cmp(b) {const v=this.n*b.d-b.n*this.d; return v<0n?-1:v>0n?1:0;}
  pow(k) {return new Q(this.n**BigInt(k),this.d**BigInt(k));}
  toString() {return this.d===1n?String(this.n):this.n+'/'+this.d;}
  toJSON() {return this.toString();}
}
const ZERO=new Q(0n), ONE=new Q(1n), TWO=new Q(2n);
const qi=x=>new Q(BigInt(x));
const sum=xs=>xs.reduce((acc,x)=>acc.add(x),ZERO);
function fact(n) {
  let r=1n;
  for(let i=2;i<=n;i++) r*=BigInt(i);
  return r;
}
function choose(n,k) {return qi(fact(n)/(fact(k)*fact(n-k)));}

// Uniform barycentric expectation of (sum x_j gamma_j)_+^k.
// Repeated nodes use the confluent divided difference f^(r)(x)/r!.
function moment(nodes,k) {
  const x=nodes.slice().sort((a,b)=>a.cmp(b));
  const p=k+x.length-1;
  let dd=x.map(v=>v.n>0n?v.pow(p):ZERO);
  for(let r=1;r<x.length;r++) {
    const next=[];
    for(let i=0;i<x.length-r;i++) {
      const a=x[i],b=x[i+r];
      next.push(a.cmp(b)===0
        ? (a.n>0n?choose(p,r).mul(a.pow(p-r)):ZERO)
        : dd[i+1].sub(dd[i]).div(b.sub(a)));
    }
    dd=next;
  }
  return dd[0].div(choose(p,k));
}

function coefficients(input) {
  if (input===null || typeof input!=='object' || !Array.isArray(input.lambda)
      || !Array.isArray(input.a) || input.lambda.length!==input.a.length
      || input.lambda.length<2) throw new Error('expected lambda and a arrays of the same length >= 2');
  const lambda=input.lambda.map(Q.parse), a=input.a.map(Q.parse);
  if (lambda.some(x=>x.n<0n) || sum(lambda).cmp(ONE)!==0) throw new Error('lambda must be nonnegative and sum to 1');
  if (sum(a).n!==0n) throw new Error('a must sum to 0');

  const m=lambda.length, n=m-1, J=[];
  let prod=ONE, k=0;
  for(let i=0;i<m;i++) {
    if (lambda[i].n===0n) J.push(i);
    else {prod=prod.mul(lambda[i]); k++;}
  }
  if (J.length===0) throw new Error('lambda must lie on a proper face (have a zero entry)');
  const x=J.map(j=>a[j].neg()), q=x.length;
  const C=choose(n,k).div(prod);
  const base=moment(x,k);
  const y=new Array(m).fill(base);
  const cache=new Map();
  for(let j=0;j<q;j++) {
    const key=x[j].toString();
    if (!cache.has(key)) cache.set(key,moment(x.concat(x[j]),k).div(qi(q)));
    y[J[j]]=base.sub(qi(m).mul(cache.get(key)));
  }
  const g=y.map(v=>C.mul(v));
  const primal=sum(x.filter(v=>v.n>0n)), polarLoss=C.mul(base);
  return {
    dimension:n, faceDimension:k-1, spikeOutside:primal.n>0n,
    primalGainOrder:1, primalGainCoefficient:primal,
    polarLossOrder:k, polarLossCoefficient:polarLoss,
    santaloShiftOrder:k, santaloShiftCoefficient:g.map(v=>v.div(qi(m))),
    recenterGainOrder:2*k, recenterGainCoefficient:sum(g.map(v=>v.mul(v))).div(TWO),
    optimizedProductLinearCoefficient:k===1?primal.sub(polarLoss):primal
  };
}

if(require.main===module) {
  try {
    if (process.argv.length!==2) throw new Error('usage: node simplex-spike.cjs < input.json');
    const input=JSON.parse(fs.readFileSync(0,'utf8'));
    process.stdout.write(JSON.stringify(coefficients(input),null,2)+'\n');
  } catch(e) {
    process.stderr.write('simplex-spike: '+e.message+'\n');
    process.exitCode=1;
  }
}
module.exports={coefficients};
