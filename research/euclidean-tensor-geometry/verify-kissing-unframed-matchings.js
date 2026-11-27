#!/usr/bin/env node
// Unframed kissing-code matchings. Run together with verify-kissing-unframed-component-costs.js.
// The inherited 4--20 and 33/40/47/56 uniform bounds are proved by the
// two predecessor replays cited in KissingUnframedMatchings.md; this script
// verifies every NEW polynomial, rational upper value and Tutte partition bound.
'use strict';
const zlib=require('node:zlib');
function gcd(x,y){if(x<0n)x=-x;if(y<0n)y=-y;while(y){let t=x%y;x=y;y=t;}return x;}
function R(n,d=1n){n=BigInt(n);d=BigInt(d);if(!d)throw Error('zero denominator');if(d<0n){n=-n;d=-d;}const z=gcd(n,d);return [n/z,d/z];}
const Z=R(0),O=R(1),add=(x,y)=>R(x[0]*y[1]+x[1]*y[0],x[1]*y[1]),mul=(x,y)=>R(x[0]*y[0],x[1]*y[1]),neg=x=>[-x[0],x[1]],cmp=(x,y)=>x[0]*y[1]-x[1]*y[0], show=x=>x.join('/');
const P=(k=0,c=O)=>c[0]?new Map([[k,c]]):new Map();
function put(A,k,v){if(!v[0])return;const c=add(A.get(k)||Z,v);if(c[0])A.set(k,c);else A.delete(k);}
function plus(A,B){const C=new Map(A);for(const [k,b]of B)put(C,k,b);return C;}
function scale(A,b){const C=P(0,Z);for(const [k,v]of A)put(C,k,mul(v,b));return C;}
function prod(A,B){const C=P(0,Z);for(const[i,a]of A)for(const[j,b]of B)put(C,i+j,mul(a,b));return C;}
const sum=(...A)=>A.reduce(plus,P(0,Z)),diff=(A,B)=>plus(A,scale(B,R(-1))),a=P(1),b=P(32),c=P(1024);
function bases(x,k){const p=[P(),x];for(let j=2;j<=k;j++)p.push(diff(scale(prod(x,p[j-1]),R(2)),p[j-2]));return p;}
function lin(u,p){return sum(...u.map((v,i)=>scale(p[i],v)));}
const enc=(i,j,k)=>i+32*j+1024*k,idx=v=>[v%32,(v>>5)%32,v>>10];
function build(data,ep,et){
 const[n,q,d,D,h,g,B,fac]=data,den=BigInt(D),ch=bases(a,g.length),chb=bases(b,d),ab=prod(a,b),w=diff(c,ab),z=prod(diff(P(),prod(a,a)),diff(P(),prod(b,b))),Q=[P(),w];
 if(h.some(x=>x<0)||fac.length!==d+1)throw Error('not a positive kernel');
 for(let k=1;k<d;k++)Q.push(scale(diff(scale(prod(w,Q[k]),R(2*k+n-3)),scale(prod(z,Q[k-1]),R(k))),R(1,k+n-3)));
 let K=P(0,Z);for(let k=0;k<=d;k++){const M=fac[k];if(M.length!==d+1-k||M.some(r=>r.length!==M[0].length))throw Error('factor dimensions');let S=P(0,Z);
  for(let j=0;j<M[0].length;j++){const u=M.map(r=>R(r[j],den));S=plus(S,prod(lin(u,ch),lin(u,chb)));}K=plus(K,prod(S,Q[k]));}
 let H=P(0,Z);for(const[e,v]of K){const[i,j,k]=idx(e),u=mul(v,R(1,3));for(const ee of [e,enc(j,k,i),enc(k,i,j)])put(H,ee,u);}
 const gp=lin(g.map(x=>R(x,den)),ch);let T=diff(P(0,ep),H);for(const[i,v]of gp)for(const e of [i,i*32,i*1024])put(T,e,v);
 const cc=[P(),a];for(let k=1;k<h.length;k++)cc.push(scale(diff(scale(prod(a,cc[k]),R(2*k+n-2)),scale(cc[k-1],R(k))),R(1,k+n-2)));
 const hp=lin(h.map(x=>R(x,den)),cc.slice(1)),aa=prod(a,a),f=diff(prod(aa,aa),scale(aa,R(1,4)));let H11=P(0,Z),H111=Z;
 for(const[e,v]of H){const[i,j,k]=idx(e);put(H11,j+k,v);H111=add(H111,v);}
 const Y=diff(P(0,add(R(B,den),et)),sum(f,hp,scale(H11,R(3)),scale(gp,R(3*(q-2)))));
 const energy=[R(3,4),R(h.reduce((v,w)=>v+BigInt(w),0n),den),H111,mul(R(q-1),add(R(B,den),et)),mul(R((q-1)*(q-2)),ep)].reduce(add,Z);
 return [T,Y,energy];
}
function choose(n,k){if(k<0||k>n)return 0n;let x=1n;for(let i=1;i<=k;i++)x=x*BigInt(n-i+1)/BigInt(i);return x;}
function divfloor(x,d){let z=x/d;return x<0n&&x%d?z-1n:z;}
function bern(A,dim,up=false){
 const ds=Array(dim).fill(0);for(const i of A.keys())idx(i).slice(0,dim).forEach((v,j)=>ds[j]=Math.max(ds[j],v));const stride=ds.map((_,j)=>ds.slice(0,j).reduce((s,n)=>s*(n+1),1)),L=ds.reduce((s,n)=>s*(n+1),1),v=Array(L).fill(Z);
 for(const[i,r]of A){const I=idx(i);if(I.slice(dim).some(x=>x))throw Error('nonunivariate');v[I.slice(0,dim).reduce((s,n,k)=>s+n*stride[k],0)]=r;}
 let V=v;
 for(let k=0;k<dim;k++){const d=ds[k],s=stride[k],W=V.slice(),T=Array.from({length:d+1},(_,i)=>Array.from({length:d+1},(_,j)=>{let f=Z;for(let t=0;t<=Math.min(i,j);t++)f=add(f,R(choose(j,t)*choose(i,t)*BigInt((j-t)%2?-1:1)*3n**BigInt(t),choose(d,t)*2n**BigInt(t)));return f;}));
  for(let i=0;i<L;i++){const t=Math.floor(i/s)%(d+1),base=i-t*s;let x=Z;for(let j=0;j<=d;j++)if(V[base+j*s][0]&&T[t][j][0])x=add(x,mul(T[t][j],V[base+j*s]));W[i]=x;}V=W;
 }
 const gg=Float64Array.from(V,r=>{const n=r[0]*(1n<<34n),v=up?-divfloor(-n,r[1]):divfloor(n,r[1]);if(v>2n**50n||v< -(2n**50n))throw Error('dyadic guard');return Number(v);});return {A:gg,ds,stride,L};
}
function split(V,k,up){const {A,ds,stride,L}=V,s=stride[k],d=ds[k],W=new Float64Array(L),Zz=new Float64Array(L),u=new Float64Array(d+1);
 for(let h=0;h<L;h+=s*(d+1))for(let b=0;b<s;b++){const base=h+b;for(let j=0;j<=d;j++)u[j]=A[base+j*s];W[base]=u[0];Zz[base+d*s]=u[d];for(let j=1;j<=d;j++){
  for(let i=0;i<=d-j;i++){const t=(u[i]+u[i+1])/2;u[i]=up?Math.ceil(t):Math.floor(t);}W[base+j*s]=u[0];Zz[base+(d-j)*s]=u[d-j];}}
 return [{...V,A:W},{...V,A:Zz}];
}
function check(V,G){const dim=V.ds.length;let nodes=0,close=0,out=0;
 function go(U,Q,lo,hi,d){nodes++;if(nodes>9000000||d>75)throw Error('unresolved Bernstein box');if(U.A.every(x=>x>=0)){close++;return;}if(Q&&(Q.A.every(x=>x<0)||lo.some((v,i)=>i<dim-1&&v>hi[i+1]))){out++;return;}
  const k=d%dim,[l,r]=split(U,k,false),[p,q]=Q?split(Q,k,true):[null,null],mid=(lo[k]+hi[k])/2,h=hi.slice(),a=lo.slice();h[k]=mid;a[k]=mid;go(l,p,lo,h,d+1);go(r,q,a,hi,d+1);}
 go(V,G,Array(dim).fill(0),Array(dim).fill(1),0);return {nodes,close,out};
}
const determinant=sum(P(),scale(prod(prod(a,b),c),R(2)),scale(sum(prod(a,a),prod(b,b),prod(c,c)),R(-1)));


function direct(C,sl){
 const [T,Y,U]=build(C,Z,Z),q=C[1],V=plus(scale(T,R(3*(q-2))),P(0,mul(R(3),sl)));for(const[i,v]of Y){for(const k of[i,32*i,1024*i])put(V,k,v);}
 const c=check(bern(V,3),bern(determinant,3,true));return [add(U,mul(R(q-1),sl)),c];
}
const invQ=x=>R(x[1],x[0]),divQ=(x,y)=>mul(x,invQ(y)),mn=(x,y)=>cmp(x,y)<=0n?x:y,mx=(x,y)=>cmp(x,y)>=0n?x:y;
const splitQ=s=>{const [a,b]=s.split('/');return R(a,b);},fracInt=x=>Number(divfloor(x[0]*1000000n,x[1]));
// Published uniform per-point bounds (not the nonlinear component capacities).
const oldSmall=[15002,15002,15003,15005,15032,15073,15121,15174,15231,15293,15357,15423,15492,15528,15634,15709,15784];
const pre=[[2,R(3,2)],...oldSmall.map((v,i)=>[i+4,R(v,10000)]),[33,R(16498,10000)],[40,R(16659,10000)],[47,R(16779,10000)],[56,R(16796,10000)]];
const tan=[[7,46,[838750,0,4538155,0,2801139,0,0,0,0,0,0,0],31832],
[7,82,[847305,0,4524998,358140,3723215,1294305,0,0,158349,0,0,0],-8490]],hac=[[7,61,7000,"4743867114278617/2800000000000000","eJx9VNmNYzEMayUFxIDuo5aH9N/GUPL7XGwwwRi2RFEUlSe/n2B8vx+m9/P9PPj+7+/37xBcHxOSAOjzPEZAPZoqBnSn1qni0aq4F1EmFpw6mrl5QB1UTiX3ZHJJDtSJ0hAU4MimvdEmkfScHOUtw1l4YbYw/BfNcJt7gOj0dDhF6s05DQpstpRMBMfvR817y3CY2jAR02rL7fdw+KoU5kPBOlJ7KhhJDb5LVk1rTQV+vlkxJJyVcjvCA2K5iLznQGUogqfEm+WSAwxuMrfeNGbpq6yMWsyeQStgB0n+JuVhThTIEq/poClpotmkRSabCSgmg4grp6pby/hOxXUAjkMsnURKWyiRoPYaCFWDfmVXwB1RpoLfHALxUENAb8fLUDBjJn+snDDRqyLGY6NWNTfqJCawEjUMMgxYhb22HneFi24eQx5Em9TtBmxr68BcqesJtOq6kkELAtgSFe0laDBEIFUoRMYhB+bCHDBmJUH4SmwVhXGvpMdpC4QgGi95p48Zr/xsOLnFuws8LoTFfBCZOouGKfyDBYilojmeYtl9A5mxYMDbtt1iHbIjrj030NZdmFsufjaM0TvTMrR6A9V3c3lCinWgicFrOiyHEbxehwwxqFFQ3R3OUbumBdHgCza1Vj+ItNFYBJ2hYAkMVxvlvrI4ua7Y2D+TTXMGgtTOCxVut4ked/2dRn+0b1DntS3so7snAd3e3YSq+DG4I8AdrYVCpeu2XDyT6IYj+IX54fMHWR7zYA=="],
[7,53,10000,"16850179333246369/10000000000000000","eJx9lNltw0AMRFtxARbA+6jFcP9tZGal/AURbEva5fJ4Q/rT71f6+1Xvl8pzvV8ffP/7fP82wfKVsZKD/c/nUtyjhq65dGWW2fs1aYqb+UovAs+WpvTjVJunXAeZaUUskpuCBRxobdoo9lU0TYZnlO/02w5nV8yyoBA3oeFYjdGVrub8pn65wejq6qRj2yy+h/o6U1WdWCZtuaIxynOX0VT33FKdyYrYiSolugyzLjMsMjQin3CDr1vGHFMXxjJRLedTKhDIKcDB6Dnjc8xVOg7CSiK5rLGASCaRi9zBstLqy1MfbWVxK2N5ELtVEOT0nkJVvbWLFTjCy0TwoG1QdxRnM8sk/TZSj9VmmATAe8+tF972IAEb2AHf7gG6HeR+NY24AgouNnXqjFYocg5mAdDRRQb+EU8oohqEDfZBeqOuk8R2urYdtVv2pgJhbj3K96AfAOqjbXTNgQWwqdVy1wiJ2EyypA5STkae0LeRie/igZDwKyj/RnqxmxRgcdvdsTkcoWV76qNVZElxX3roAqUhTvndNRyuCfJXcMrKo2M4pbDfhmzYkwdGYe+n9HSgOFWTQy1RZ6NvOCMX1ECW+6TJKUBycFVgnC5nXmAJ+CcN943TAdscP5dAKaxt10z2yHlmIa2dlmhhj3vsvCjAsXCtMzhww7Po8VLK1s4/kDsZQx7HX0cOpvfgb3d/ckVDUHt0GbiaPY3kbOtF9eiY2/CL6we0gOtP"],
[7,59,7000,"14810705924620269/8750000000000000","eJx9lOmtajEMhFuhACJ5X2pB9N/GHTuHf08PgQI58TKfJ3zy/fJ+v+L9Ynpe79cHn/+9v/8+gu1j3tyF55/PKXu/xBWPTpiTYxUVxm8N4/mpTGLB+NZB7S5P5sOJTXa1mqCyCnQYyV6KnNYivvHt4iQb5vNEbJJ5UuoEemrPSuGTyLVZ6MnvQmxPPTW/dXJ4KNUwQXa1iWfk45Q5YV6i1BN2eHbYXLBykxsSGQrwCgtfXaJKED0KqaSNfwrR6T2Yq0TAJTZhlbZAbbcshZMsXbkajwy7nMrF7uDLGavUVOspjK63MJmFfyfsw74hVUTbbEEHgDBTxRA9zBwS27p0lwvHBIp3jzWSLQegWcagwWmgmvGqB5nuLDAkacrLRnnSVnfnoMyiGAoSWVMZ3IzCbA5ZO4HvDbRuznlO6jOpSNE91RFQjtJawaKxY01SoZpAtkJ6xDpNPQjmyCsHmZaIAXEqL+MZ6a0I//R6RkuLRisGNrmOEkZCiFRFCz5bEF1icqGeAXC4x2qQg4nPJYLBbzks5WU/S88AvJF5uWPKNJ6DGHCp9aHnUhxK0GfDPdgk6rGLdvTPPnYRkcR4gDFPX6fauIIer2ADlGu8woomcXkmzcyl0jzi6pgBafIsQdKxJwDQOGkbO/DIYoODB4NkVM5NgZGSgrepA7XbZ/AasVq7LwecD94/DVx3nekXxt1r3oQNBg6ciYtwG/LCvZ1vyQH0m35uID/cGdNbNwYM0Nc3buPjTkFnes998foD0uz2kw=="],
[7,63,10000,"3386088072202697/2000000000000000","eJx9VNutYjEMbIUC7pH8tlMLov82dsbh7tdqEehAEnsenvDun1c5Pj8vle/r5/XG53/vz7+PYPnRmFIPHHi/Hx0s5wHG46E2AMkTiseZwZknTlpbbV1KicS3NTtYNZipn+HzybaRRD872DBWo9wzlTWq6BJJKAMDtACe8eFogNVJQ3uCWkbGmfOFerZIayy52RNNlI7RAyJW0qSMnayTMizDD64EaZzBOtnMOWzX48bznqfC2VOBGOP5C6hKXaWNJjrAXbZp5tAwBKEjgJ/QWjic9+NAwWYSDKJWlZ91j4IuyYmAxx9WvQFLPmrR/KITR2i7Spr2MtPhKu21E1kutmZa6laUYS7AnlO1JCVagWNO3r4MoLdBenkq22OgJWjZ3sdooQCXpDUxmFm7Y+BHhl4zw2Unrdr0pzA696UniTFwK92O7PRgEzpuUGw1d2E0tklpjbNa4E/vUFrg6g64Ka+vPlcWhEfe4cdY35hqqg/tFp+eWartSNS1FLMkJM4IhyHrCkzpvoSRfpj9N1rbCGaBCqzuSgGIJ3LBIeHQLMlD9ipK07VgTNUO062rbwTQzSg/NZ201JAvXCbKNmvtuEEhYrdSnClzPMjn3AvgcH2+OoL3xXFDcBQQ0GyrC1xVvsOUZuQehGVIu+w0R6BHpOpcJyFrE44y5sLa5TraIm77T6ENxSsnecUsxIXJhARYnHkZFdKyuAgPjNhkdNfkr/EIidxxJO7OMqzNFf64IPJ3Qh+8/gBk7/UN"],
[7,51,10000,"16829313074117719/10000000000000000","eJx9U9mtI0kMS+UF4AZ0H7E8TP5pLKn2/g2m4XbZVRJFUazf/vykfn7q86PyfT4/v3j/9fnz9xBsW9WU4/j312Q+P49KGvAfM0eNx63duYbbDpKessypg3wYGRl6AePIV18pwxolNv7/gXsxwSSxM64E0ui5fzVcc0xVj4ICM/pKOBPWFpDZcnnZO1cgYvuYWol0HiMVBxuvXbDfIJVHPUfvR+wGWT7layJzKXUl96hpBtV4wpACIHOZ0GCGaJs0M7QYAxkEByjBxNqgfKaQieHaWYlwxv9OFOcF3ruIkewwbtjEtJ/ogsRj4BBhfa750ZE9TQNR5NTXhgJw0LpFW6otRehsvPWOBQOCCNNV15wLxDohBZDXp2mWksQDlsKZvfKllLJk90gfs0U1mq3XaDzNtGzGPFoT0q6XubvHLRVdngIjReu4hr9HkzDXDXgNUvbJ3xUr1GInWXArl5UdQ3UOOhJ+WVosAtYUeTXlpLHXyk53OaNRtHFuxRhXgPD1PW2jHkVeje/kqAJktOfY98EPWBZ81aQDXm7EsnD05PbFet5N1WsKGGulSV0cHpT4ykh/DA0kSuVRG9NglZksyPc2QataDMSsgar1ci9vXJ0DyrgrB+kA4kEfB0Fttva9g5cT8BvnmqlzBBV+dZ09G+Xd5K1irrZ4nuLdi5vxZWI99QbDNSKvz3Prqzbc7idS9nS85FgVQo7hIka+gX/w/AeqOeuA"],
[7,55,10000,"3373768082225781/2000000000000000","eJx9VNsNIkEMa4UCWGnyTmpB9N/G2Rnu73QrYKWZPBzb4VPvV8T7le+XnN/zfn3w/d/n++8QHD8pOe64/3xEG5WfKDHcWu35EzGHx5JoVWg/liLurCnJCKvW2Yhyl/er85jhQqTiKDJcYjpbN8U0WVXN9P3C72EJiU5D5KPVJYJ+gvhzJJmDaARlC6uapQpDw3oGtbLKeaApal2xGXlCWUT7B16m2NcOptyO4uZBtC2lbcxyZdmxwzdIKD2EdOo0G7BNHL7BiNdOI+U4GYxnCC31fZMrYbtua9wDcAHalykftWyknPEiAyp+BhjD01kLyEz9hC3aVHPdVuZiYFm6a5p3kUN8ouW3CTgV1VUEtEKbS570kYWisYMVEtvYsOaSj74SV5bTYMz7chgdtYDGDCUygHzHE51DRsQ751yGZ6RA+rLSFKox17IBHeEABilKDKd4bNBIiUsafU76nbEWYiSkoQniUBvGa/qQUkvTs7bzmCnxS+rj8rMiharDkeVkhdWKGUlS9RJCL6HSATBj2AB8NX2qNLksFNt6cn28BMPfGlCNg3jABJenJfd6ekwYB43CmwggSfvYbTtAUknezD0RyD2ZHbiHrOedhTtkso3CHYMvTZzb/kqqLUzDKmgkTdTjFJCDRJ0bZezxZEGNXc84ILXuNiSU3E2RibU9zAGzUdKEYdZXbTqjP0wqvfEZid3aiUKOzY9+bPg61tVQcMXENljw78JhQLtxXzx/AOuR8Z4="],
[7,49,10000,"105034447210479/62500000000000","eJx9U8eNA0cQTOUC4ALtTSzE5Z+GqppHvQQR5M5ypl2ZeffrJ/b1U68flb/P6+eN3/99f/87BNtu4o1i7/f7UZvXj7kqnuPGxcTQsEMW/x4E6xiin1qp1P6r+5ijUmkn3qdXuXptOva1I8v20lW3JJjV2DCNZENnnopLYEnrQNaTURXLN7Va19Vvsxw+vMoQPma+bLLNkppSy2keU77tMOtRzqzqznVXe+6/CVtptMsFhLY5W7TgZO3bEdtgfYCe0EM0yAlg7VHU5c0DkRW/pAdlQZ1wkFLpO64SrIXCwoEL47H2hvr2L9Pej63kjWI5da1Xt1055UZucAsNrfc4FgW1Uh+QasBL6N02fYSDWr6oT+ZRbpnm1PkB7VAx93J3lpBc84zlmzQZWm2W56eC9xQBxW5mzcloUmKAgeJNdA9qUlRQLWCTY5t15ikiNtF2ZizNM4sudg2oQMbQNoBdLAgmSuej//qMfEGaT9CmE0UjbMJUiPdAqUGhcNT5OAgkwG5fZinagxAcJXzY1LBA75wKGAdT5ldxOnF0h0OOTAAMenR3Wh4ApfueZlHMhvmQAH9YnPctwEP5v5Y93xls5k0ppdc0aVcUbmh50HgEpxMcrpBgjdAZJZZZmFP/sCg1pXvRirdwT3VYH2j9pgPXffcU7sqmGXNx+yjM9mz2RUWSEg8wfWJTpw/jmWNtZ2XY5NhUjZNfodAxDqyeKvmZCbc4jr31GnB6qdq+f/QDqRTbJchK8Y+YYM4wVEvNwFAX+ovPP7dr+CU="],
[7,67,10000,"529950220864393/312500000000000","eJx9U9uNwzAMW6UDJIDej1mC7r/GUXLu73Bpg7q2TJMU/eT1iXmvD9P7XJ8H73/f798l3wHhqGysP0+SeWFKU3t+CYPrc0uwpBpGLJ1Bi1astosi3uCjFjET4sFTKmrcHjW1qSFYYmtpHhgKdsfAPC0WWaKxT6f6Zs9w1Ct+mfbYUsZEa2jthDMz/ZbPSb0YxlUD22oUh4SVz5FSUUY8GzhAR8A0Oae6Gg/+cwF0uZu7YfVFh0Bd0s49AyXiUXzjtM6RwUoJZd/Z8LAORjTTFIGQt/aIlyRaE7mjYdoyJgrVno3a3DbmgyfY3O7dtl228RZ81atq3VLrrvBYhpkjFZCZ403C1GHACTUDxCiEkWuMZmS7nX3oTqwwrWl3usv2u82C+eQAn5EqlHA098AQoAM8fNFVWTjXFyVeRLd25GDPJpXyTYGRrpHggDwBvsmV14Ys5GFCRIiGLNNw2KvHUsDMHBokKPfY9oEAsjjWgkORIEFvysEW7CUAOz4wqFthh2Zr0nGbR8QdURsrG1e5hNCjDTWHIbL8Atak97Zqn9QCkJC5UaCtquZrp2HJ2gjzJhvqQAd9qNxFSeFvQAbMtKZrXhZ0tGm5q+/Vwp2yEzncmLndkMY2TsGRdCjdNqzp4pD+9p/7IDW201qOm1FzftLeAkZULGcgqoQoHUKZeTqE/njYpqO9i3/dxzM2Qwtu8rl0biebYmZJp/CL5wep5Otr"],
[7,69,10000,"16969140491823137/10000000000000000","eJx9U9mt3DAMbMUF2ADvoxbj9d9GhpRfvoIsdheyJZJz6c37isbvvpi+z329+P3v+/PvI3htlt7o+b6v0DSN5PtKN8Xao93vq1Oz7usxb5U2rFy7kn7bhs67Yi88NJflPGpYo5W4Yx8bj3JyFPdUPTw17IqRQixYswvJDMtA2ZPJpAUUT4cIMH7DUKnY58pK3bFVAFfdkdPGmmTLuC07Q6dOpzBbZFhQLRxn8RqkIji3C2DO3j2PtJC/I8Pn36sGtbL3YPeywGMFzs5AD+/OpbdC9sLQtCmWtCxfFMP2YQOO2q6tKPyZslcAeToZ6ZjyQLEWHVoAab5YOAkt4uAVqBXLMJRWLKFxSKNTelUtHUpiwhG+iLQgaPL6IMJANXQnR8lGPOoq5h3O8MhzdUO5p5+y6E2Go9OYFQTl9jyZhKwPBJ23kKEKGG2hxKIE2JhIgUdoH30UTg55UxD1WNmRFpE6/GxsVzQjXv08t8UD3sETWmlAXc0NbzD9aPogsgNDEN7xhRPa8oJVcpJYx3SFb9iyNytJfL2utJakL7M7L3kJFhqmTPKFDKeojjKT/vEoaIYBdw4tNDY23TQGTZ4Q27nH4eYnGPDAMn9Bp8wZcgYh3EkH1oUMWP2ZIJHnCihPxtRh/vDHDeSR/BN8o8K6cYzA5skfdDNb7kibjaZowGCI62A108BTIaUcSI387lyFrYjdLBlXtviDjBE6GFEM+Y9kSNwAgpos/IX8B58/Uury/Q=="]];
for(const [n,seed,h,B]of tan){
 const [T,Y]=build([n,seed,0,10**7,h,[0],B,[[[]]]],Z,Z);check(bern(Y,1),null);
}
let fw=[];for(const [n,q,den,exact,bytes]of hac){
 let v=JSON.parse(zlib.inflateSync(Buffer.from(bytes,'base64')));if(v[0]!==n||v[1]!==q)throw Error('chart identity');
 const [U,z]=direct(v,R(1,den));if(show(U)!==exact)throw Error('energy fraction');fw.push([n,q,U]);console.log('uniform',n,q,exact,z.nodes);
}
const unit=1000000,inf=10**14;
function weights(n,max){
 const src=pre.concat(fw.filter(([d])=>d>=n).map(([d,k,U])=>[k,U]));
 return Array.from({length:max+1},(_,k)=>{
  if(!k)return 0;
  let U=R(3*k,4);for(let [s,u]of src)if(s<=k){const e=add(R(3,4),mul(R(k-1,s-1),add(u,R(-3,4))));U=mn(U,e);}
  for(let[d,q,h,B]of tan)if(d>=n){const e=add(R(3,4),R(h.reduce((a,b)=>a+BigInt(b),0n)+BigInt((k-1)*B),10**7));U=mn(U,e);}
  if(cmp(U,R(3,4))<0n)throw Error('uniform mass-norm check');
  let w=divQ(R(k),U);
  if(k===1||k===2||k===3||k===4||k===6)w=mx(w,R(4*({1:1,2:1,3:2,4:2,6:3}[k]),3));
  if(k===5)w=mx(w,R(50,13));if(k===7)w=mx(w,R(1000,209));
  return fracInt(w); // round reciprocal DOWN
 });
}
function partDP(ws,excludes){
 const n=ws.length-1,dp=Array.from({length:n+1},()=>Array(n+1).fill(inf));dp[0][0]=0;
 for(let k=1;k<=n;k++)if(!excludes.includes(k))for(let j=k;j<=n;j++)for(let o=k%2;o<=j;o++)dp[j][o]=Math.min(dp[j][o],dp[j-k][o-k%2]+ws[k]);return dp;
}
function barriers(N,tau,m,dp,ws,repair){
 const D=N-2*m+2;
 let best=inf,arg=[];for(let t=0;2*t+D<=N;t++)for(let o=t+D;o<=N-t;o+=2){
  const sup=repair?Math.min(o,t+tau-N):o;
  for(let s=0;s<=sup;s++){const r=s*ws[1]+dp[N-t-s][o-s];if(r<best){best=r;arg=[t,o,s];}}
 }if(best>=inf) return [best,[]];return [best,arg];
}
function run(n,P,tau,base,stricts){
 let ws=weights(n,tau),dp=partDP(ws,[1,3]);const at=(v,i)=>R(v,i);
 for(let N=base;N<=tau;N++){let results=[];
  for(let [th,m,repair]of [[500,stricts[N-base],true],...((N,n)=>N!==(n===6?73:127)?[]:(n===6?[[501,33],[510,31],[520,28],[530,25],[540,22],[550,18],[560,15],[580,6]]:[[501,55],[510,49],[520,42],[530,35],[540,26],[550,17],[560,7]]).map(([a,m])=>[a,m,false]))(N,n)]){
   let [w,which]=barriers(N,tau,m,dp,ws,repair);let a=R(th,1000),x=mul(a,a),delta=mul(x,add(x,R(-1,4))),W=R(w,unit),D=n===6?22:34;
   const upper=add(invQ(W),mul(delta,mn(R(1,2),divQ(R(4*D,3),W))));
   if(cmp(upper,R(3,4*P))>=0n)throw Error('barrier not excluded '+JSON.stringify([n,N,m,th,repair,w,which,show(upper)]));
   results.push([th,m,w,which]);
  }console.log('match',n,N,JSON.stringify(results));
 }
 // If all large components have an independent half, replace them in the
 // cost recurrence by their independent-set bound. An impossible partition
 // then forces a large component WITHOUT an independent half.
 const cut=n===6?[12,16,19,21]:[11,13,15,16,19,20];
 for(let N=base;N<=tau;N++){let K=cut[N-base]-1,dp=Array(N+1).fill(inf);dp[0]=0;
  for(let k=1;k<=N;k++){let w=k<=K?ws[k]:Math.floor(4*Math.ceil(k/2)*unit/3);for(let j=k;j<=N;j++)dp[j]=Math.min(dp[j],dp[j-k]+w);}
  if(3*dp[N]<=4*P*unit)throw Error('component cutoff');console.log('large-nonhalf-component',n,N,K+1,dp[N]);
 }
}
run(6,36,76,73,[33,34,35,36]);run(7,63,132,127,[57,58,58,59,60,61]);
