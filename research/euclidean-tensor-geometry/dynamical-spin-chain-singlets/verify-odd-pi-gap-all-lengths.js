// rational x^2 certificate
const K=10n**28n, d=10, fac=n=>{let r=1n;for(let i=2;i<=n;i++)r*=BigInt(i);return r;};
const coN=n=>3n**BigInt(2*n)+3n,coD=n=>4n*fac(2*n);
const D=Array(d+2).fill(0n),U=Array(d+2).fill(0n);
for(let n=0;n<=d;n++){
 U[n]=(K*coN(n)+coD(n)-1n)/coD(n);
 if(n){const k=BigInt(n),bd=(2n*k+1n)*1764n,bn=bd-1764n-k*(2n*k+1n);D[n]=K*coN(n)*bn/(coD(n)*bd);}
}
U[d+1]=(10n*K*coN(d+1)+9n*coD(d+1)-1n)/(9n*coD(d+1));
const F=Array(d+3).fill(0n);
for(let n=0;n<=d+1;n++){F[n]+=93n*93636n*D[n];F[n+1]+=93n*39940n*D[n]-5000000n*U[n];}
function check() {
 const a=F.slice(1),n=a.length-1,z=Array(n+1).fill(0n); let pow=1n;
 for(let i=0;i<=n;i++){let b=1n;
  for(let j=0;j<=n-i;j++){z[i+j]+=a[i]*pow*100n**BigInt(n-i)*b;b=b*BigInt(n-i-j)/BigInt(j+1);}
  pow*=234n;
 }return [z.map(x=>x>0n?"+":x<0n?"-":"0").join(""),a.map(x=>x>0n?"+":x<0n?"-":"0").join("")];
}
const [transformed,raw]=check();
if(transformed!=="+".repeat(12)) throw Error("fixed interval coefficient check failed: "+transformed);
console.log(JSON.stringify({positiveTransformedCoefficients:transformed.length,rawCoefficientSigns:raw}));