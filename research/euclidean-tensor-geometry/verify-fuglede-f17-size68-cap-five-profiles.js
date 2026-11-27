const P=17,R=Array.from({length:P},(_,i)=>i),mod=x=>(x%P+P)%P,inv=R.map(x=>R.find(y=>x*y%P===1)); const B=R.slice(0,9).map(i=>{let pol=[1],den=1;for(let j=0;j<9;j++)if(i!==j){let q=Array(pol.length+1).fill(0);for(let k=0;k<pol.length;k++){q[k]=mod(q[k]-j*pol[k]);q[k+1]=mod(q[k+1]+pol[k]);}pol=q;den=mod(den*(i-j));}return pol.map(x=>mod(x*inv[den]));});
const T=R.map(x=>B.map(P=>P.reduceRight((s,a)=>(s*x+a)%17,0))),v=new Uint8Array(17),cats={},good=[];
function go(k,s){if(k<9){for(let a=0;a<=5;a++)if(s+a+5*(16-k)>=68){v[k]=a;go(k+1,s+a);}return;}
for(let i=9;i<17;i++){let r=T[i],a=0;for(let j=0;j<9;j++)a+=r[j]*v[j];a%=17;if(a>5||s+a+5*(16-i)<68)return;v[i]=a;s+=a;}if(s!==68)return;
const c=R.slice(0,9).map(j=>mod(B.reduce((s,q,k)=>s+q[j]*v[k],0)));let d=c.findLastIndex(x=>x);cats[d]=(cats[d]||0)+1;good.push({c,v:Array.from(v)});
}
go(0,0);if(String(Object.entries(cats))!=="0,1,8,34")throw Error("profile number");const expected=new Set();for(let sign of [1,-1])for(let h of R)expected.add(R.map(t=>mod(4+sign*mod((t-h)**8))).join(','));if(good.filter(x=>x.c[8]).some(x=>!expected.delete(x.v.join(',')))||expected.size)throw Error("octic shape catalogue");console.log({cats});