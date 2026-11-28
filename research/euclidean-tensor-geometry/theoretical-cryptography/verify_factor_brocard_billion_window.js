"use strict";
// Exact Brocard window verifier; no external runtime modules.

// Build WebAssembly entirely in memory; no compiler or third-party module.
const OP={
 block:0x02,loop:0x03,if:0x04,else:0x05,end:0x0b,br:0x0c,br_if:0x0d,
 ret:0x0f,call:0x10,get:0x20,set:0x21,tee:0x22,load8:0x2d,store8:0x3a,
 C:0x41,J:0x42,z:0x45,eq:0x46,ge_u:0x4f,
 lz:0x50,leq:0x51,llt_s:0x53,lge_u:0x5a,lltu:0x54,
 add:0x6a,sub:0x6b,imul:0x6c,and:0x71,or:0x72,shl:0x74,shr:0x76,
 ctz:0x7a,ladd:0x7c,lsub:0x7d,lmul:0x7e,lrem:0x82,land:0x83,lshr:0x88,
 dmul:0xa2,ddiv:0xa3,trunc:0xb1,conv:0xba
};
function u(n){let a=[];do{let b=n&127;n>>>=7;a.push(b|(n?128:0));}while(n);return a;}
function s(n){let a=[];while(true){let b=n&127;n>>=7; if((n===0&&(b&64)===0)||(n===-1&&(b&64)!==0)){a.push(b);return a;} a.push(b|128);}}
function asm(z){
 const result=[], t=z.trim().split(/\s+/);
 for(let i=0;i<t.length;i++){
   const op=t[i]; if(!(op in OP))throw Error(op);result.push(OP[op]);
   if(op==="C"||op==="J")result.push(...s(Number(t[++i])));
   if(["get","set","tee","br","br_if","call"].includes(op))result.push(...u(Number(t[++i])));
   if(["block","loop","if"].includes(op))result.push(0x40);
   if(op==="load8"||op==="store8") result.push(0,0);
 }
 return result;
}
function sec(id,p){return [id,...u(p.length),...p];}
function vec(a){return [...u(a.length),...a.flat()];}
const I=0x7f,L=0x7e;
function fun(params,result){return [0x60,...vec(params),...vec(result)];}
function body(locals,source){return vec([...vec(locals.map(([n,t])=>[...u(n),t])),...asm(source),0x0b]);}
const mb=body([[1,L]],`
 get 0 get 1 lmul get 0 conv get 1 conv dmul get 2 conv ddiv trunc
 get 2 lmul lsub tee 3 J 0 llt_s if get 3 get 2 ladd set 3 end
 get 3 get 2 lge_u if get 3 get 2 lsub set 3 end get 3
`);
const mbInt=body([[1,L]],`
 get 0 get 1 J 39 lshr lmul get 2 lrem set 3
 get 3 J 8192 lmul get 0 get 1 J 26 lshr J 8191 land lmul ladd get 2 lrem set 3
 get 3 J 8192 lmul get 0 get 1 J 13 lshr J 8191 land lmul ladd get 2 lrem set 3
 get 3 J 8192 lmul get 0 get 1 J 8191 land lmul ladd get 2 lrem
`);
const jb=body([[1,I],[2,L]],`
 C 1 set 2
 block loop
  get 0 lz br_if 1
  get 0 ctz set 3
  get 0 get 3 lshr set 0
  get 3 J 1 land J 1 leq if
   get 1 J 7 land tee 4 J 3 leq get 4 J 5 leq or
   if C 0 get 2 sub set 2 end
  end
  get 0 get 1 land J 3 land J 3 leq if C 0 get 2 sub set 2 end
  get 0 set 3 get 1 get 0 lrem set 0 get 3 set 1
  br 0
 end end
 get 1 J 1 leq if get 2 ret end C 0
`);
const jbInt=body([[1,I],[2,L]],`
 C 1 set 2
 block loop
  get 0 lz br_if 1
  get 0 ctz set 3
  get 0 get 3 lshr set 0
  get 3 J 1 land J 1 leq if
   get 1 J 7 land tee 4 J 3 leq get 4 J 5 leq or
   if C 0 get 2 sub set 2 end
  end
  get 0 get 1 lltu if
   get 0 get 1 land J 3 land J 3 leq if C 0 get 2 sub set 2 end
   get 0 set 3 get 1 set 0 get 3 set 1
  end
  get 0 get 1 lsub set 0
  br 0
 end end
 get 1 J 1 leq if get 2 ret end C 0
`);
// scan(p, p-B, length), with memory one bit per entry, MSB position arbitrary.
const sb=body([[5,I],[2,L],[1,I]],`
 J 1 set 8 J 1 set 9
 block loop
  get 9 get 1 lge_u br_if 1
  get 8 get 9 get 0 call 0 set 8
  get 9 J 1 ladd set 9
  br 0
 end end
 block loop
  get 3 get 2 ge_u br_if 1
  get 3 C 3 shr tee 4 load8 set 5
  C 1 get 3 C 7 and shl set 6
  get 5 get 6 and z if
   get 8 get 8 J 1 ladd get 9 J 1 land J 2 lmul lsub get 0 call 0
   get 0 call 1 tee 7 C -1 eq if
    get 4 get 5 get 6 or store8
   else
    get 10 C 1 add set 10
   end
  end
  get 8 get 9 get 0 call 0 set 8
  get 9 J 1 ladd set 9
  get 3 C 1 add set 3
  br 0
 end end
 get 10
`);
const sbInt=body([[5,I],[2,L],[1,I]],`
 J 1 set 8 J 1 set 9
 block loop
  get 9 get 1 lge_u br_if 1
  get 8 get 9 get 0 call 0 set 8
  get 9 J 1 ladd set 9
  br 0
 end end
 block loop
  get 3 get 2 ge_u br_if 1
  get 3 C 3 shr tee 4 load8 set 5
  C 1 get 3 C 7 and shl set 6
  get 5 get 6 and z if
   get 8 get 0 call 1
   get 8 J 1 ladd get 9 J 1 land J 2 lmul lsub get 0 call 1
   imul tee 7 C -1 eq if
    get 4 get 5 get 6 or store8
   else
    get 10 C 1 add set 10
   end
  end
  get 8 get 9 get 0 call 0 set 8
  get 9 J 1 ladd set 9
  get 3 C 1 add set 3
  br 0
 end end
 get 10
`);
function inst(n, integerOnly=false){
 const pack=(name,kind,index)=>[...vec([...name].map(x=>x.charCodeAt(0))),kind,index];
 const m=new WebAssembly.Module(Uint8Array.of(
  0,97,115,109,1,0,0,0,
  ...sec(1,vec([fun([L,L,L],[L]),fun([L,L],[I]),fun([L,L,I],[I])])),
  ...sec(3,vec([0,1,2])),
  ...sec(5,vec([[0,...u(Math.ceil(n/(8*65536)))]])),
  ...sec(7,vec([pack("mul",0,0),pack("jac",0,1),pack("scan",0,2),pack("mem",2,0)])),
  ...sec(10,vec(integerOnly?[mbInt,jbInt,sbInt]:[mb,jb,sb]))
 ));
 return new WebAssembly.Instance(m).exports;
}


const die=(x)=>{throw Error(x);};
const need=(b,s)=>{if(!b)die(s);};
function bnum(n){need(Number.isSafeInteger(n),"input exceeds exact decoding");return BigInt(n);}
function power(base,n,p){let a=1n;while(n){if(n&1n)a=a*base%p;base=base*base%p;n>>=1n;}return a;}
function certify(w,B,N){
 let known=new Set([2n]);
 for(const [pp,rr,row] of w.certificates){
  const p=bnum(pp),a=bnum(rr);
  need(p>2n&&(p&1n)&&a>=2n&&a<p&&!known.has(p),"Lucas certificate range");
  let m=1n,last=0n;
  for(const [qq,ee] of row){
   const q=bnum(qq),e=bnum(ee);
   need(q>last&&known.has(q)&&e>0n&&e<=53n,"Lucas factor");
   m*=q**e;last=q;
  }
  need(m===p-1n&&power(a,m,p)===1n,"Lucas factorization/order");
  for(const [qq] of row)need(power(a,m/BigInt(qq),p)!==1n,"Lucas proper order");
  known.add(p);
 }
 need(Number.isSafeInteger(B)&&Number.isSafeInteger(N)&&N>0&&N<=2147483647&&B>=N,"interval");
 let last=BigInt(B);
 for(const pp of w.primes){
  const p=bnum(pp);
  need(p>last&&p<=2n**50n&&known.has(p),"scan prime range");
  last=p;
 }
}
function scanAll(w, N=w.length, verbose=true, integerOnly=false){
 const B=w.upper;certify(w,B,N);
 const {scan}=inst(N, integerOnly), counts=[];
 let s=N, last=0;
 for(const p of w.primes){
  if(s===0) break;
  const t=Date.now(), v=scan(BigInt(p),BigInt(p-B),N);
  need(v>=0&&v<=s,"survivors must decrease");
  counts.push(v);s=v;last=p;
  if(verbose)console.log("p",p,"remaining",v,"ms",Date.now()-t);
 }
 return {N,last,counts,survivors:s};
}


function oracle(p,B,len,alive) {
 let n0=B-len+1;const pb=BigInt(p);
 let tail=1n;for(let t=p-1;t>n0;t--)tail=tail*BigInt(t)%pb;
 let f=power(tail,pb-2n,pb),s=0;
 f=pb-f; // Wilson, f * tail = -1
 for(let n=n0;n<=B;n++) {
  const i=B-n;
  if(alive[i]!==0) {
   if(power((f+1n)%pb,(pb-1n)/2n,pb)===pb-1n)alive[i]=0;
   else s++;
  }
  f=f*BigInt(n+1)%pb;
 }
 return s;
}
function smallTests(integerOnly=false){
 let tests=0;
 for(let p=3;p<=199;p+=2){
  if(Array.from({length:Math.floor(Math.sqrt(p))-1},(_,k)=>k+2).some(q=>p%q===0))continue;
  const B=p-1,N=B,{scan,mem}=inst(N,integerOnly);
  let rows=new Uint8Array(mem.buffer);
  const ct=scan(BigInt(p),1n,N), pb=BigInt(p);
  let f=1n, good=0;
  for(let n=1;n<=B;n++){
   f=f*BigInt(n)%pb;
   const item=power(f+1n,(pb-1n)/2n,pb)!==pb-1n, i=B-n;
   need(item===((rows[i>>3]&(1<<(i&7)))===0),"direct factorial mask");
   if(item)good++;
   tests++;
  }
  need(good===ct,"direct factorial count");
 }
 let seed=123456789n;
 const rng=()=>{seed=(seed*6364136223846793005n+1n)%(1n<<64n);return seed;};
 const {mul}=inst(1,integerOnly);
 for(const p of [3n,900719925474099n,1000001000000017n,2n**50n-1n,2n**50n]){
  for(const a of [0n,1n,p-2n,p-1n,p])for(const b of [0n,1n,p-2n,p-1n,p]){
   need(mul(a,b,p)===a*b%p,"wide mul edge");tests++;
  }
  for(let k=0;k<20000;k++){
   const a=rng()%p,b=rng()%p;
   need(mul(a,b,p)===a*b%p,"wide mul differential");tests++;
  }
 }
 return tests;
}
function verifySample(w,N,integerOnly=false){
 certify(w,w.upper,N);
 const {scan,mem}=inst(N,integerOnly);
 const alive=new Uint8Array(N).fill(1), counts=[];
 let final=N;
 for(const p of w.primes){
  const p1=scan(BigInt(p),BigInt(p-w.upper),N), p2=oracle(p,w.upper,N,alive);
  need(p1===p2,"independent sieve counts");
  // Compare actual masks, not only sizes.
  const b=new Uint8Array(mem.buffer);
  for(let i=0;i<N;i++)need(((b[i>>3]>>(i&7))&1)===1-alive[i],"independent sieve mask");
  counts.push(p1);final=p1;if(final===0)break;
 }
 return {length:N,counts,final};
}


const {readFileSync}=require("node:fs");
const {join}=require("node:path");
const equal=(a,b)=>JSON.stringify(a)===JSON.stringify(b);
function main(){
  const mode=process.argv[2]??"--quick";
  need(["--quick","--full","--full-integer","--quick-integer"].includes(mode),
       "usage: node verify_factor_brocard_billion_window.js [--quick|--full|--full-integer|--quick-integer]");
  const w=JSON.parse(readFileSync(join(__dirname,"factor_brocard_billion_window.json"),"utf8"));
  need(w.upper===1000001000000000&&w.length===1000000000&&
       w.quickLength===1000000&&w.primes.length===31&&
       w.certificates.length===203, "frozen window or certificate dimensions");
  const integerOnly=mode.endsWith("-integer");
  if(mode.startsWith("--quick")){
    console.log("direct-factorial and arithmetic tests",smallTests(integerOnly));
    const r=verifySample(w,w.quickLength,integerOnly);
    need(r.final===0&&equal(r.counts,w.quickCounts),"quick replay did not match");
    console.log(JSON.stringify(r));
  }else{
    const r=scanAll(w,w.length,true,integerOnly);
    need(r.survivors===0&&equal(r.counts,w.fullCounts),"full replay did not match");
    console.log(JSON.stringify(r));
  }
  console.log("PASS",mode);
}
if(require.main===module)main();
