from hashlib import sha256
from pathlib import Path
import subprocess
import tempfile

# Reuse only the audited interval/g3 setup, not either preceding chamber.
base = Path(__file__).resolve().with_name("check_two_by_three_tag_credit.py")
raw = base.read_bytes()
if sha256(raw).hexdigest() != (
    "e8a65208294b8cdd20e766a3960f2c539e91f47a04ff3d81f0c0bf1ccc9a845d"
):
    raise ArithmeticError("different two-by-three checker")
setup, sep, remainder = raw.decode().partition('\ntext += r"""')
if not sep or remainder.count("int main(){") != 1:
    raise ArithmeticError("ambiguous setup boundary")
env = {"__file__": str(base)}
exec(compile(setup, str(base), "exec"), env)
text = env["text"]
text += r"""
I polyF(double t){
 const I z=fplus(I(.5)-t),z2=sq(z);
 return sq(z2)*(44-112*z2);
}
I upper1(int lev){
 if(lev>=3200)return (I(575)/1000)/af;
 I D=I(lev)/P;
 if(lev<=2400)return 2/D;
 I s=D/af, v=s-3;
 return (2/D)*(1+sq(v)/4);
}
I lower1(int lev){
 if(lev>=3200)return (I(549)/1000)/af;
 if(lev<=1600)return 0;
 I D=I(lev)/P, T=1-(2*af)/D, a=0;
 for(int i=0;i<10;i++)a=a+powI(T,2*i+1)/(2*i+1);
 return 4*a/D;
}
const int K=10000;
const long long scale=10000000000000LL;
long long lo[40001],hi[40001];
__int128 cs[40001];
void rho2(){
 for(int i=0;i<=K;i++)lo[i]=hi[i]=scale;
 for(int i=K;i<4*K;i++){
  const long long a=i*i,b=1LL*(i+1)*(i+1);
  lo[i+1]=max(0LL,lo[i]-(2LL*(i+1-K)*hi[i-K]+a-1)/a);
  hi[i+1]=max(0LL,hi[i]-(2LL*(i-K)*lo[i+1-K])/b);
  if(lo[i+1]>hi[i+1])abort();
 }
 for(int i=0;i<4*K;i++)cs[i+1]=cs[i]+(2LL*i+1)*(__int128)lo[i+1];
}
I bound2(int h,int j,int b){
 int z=min(4*K,int((1LL*K*499*(P-b-h-j))/(1000*800)));
 if(z<=0||z>4*K)abort();
 I G=box((double)cs[z],(double)cs[z])/(2LL*K*K)/I(scale);
 // Positive contribution from exactly one additionally tested prime above N^a.
 const int stride=125; // 1/80 unit in the Dickman variable
 I ext=0;
 for(int v=K+stride;v<=z;v+=stride){
   I pre=box((double)cs[z-v],(double)cs[z-v])/(2LL*K*K)/I(scale);
   ext=ext+pre*stride/v;
 }
 return 1/(sq(af)*(G+ext));
}
I source(int lo,int hi,int withPNT){
 I res=0;
 for(int k=lo;k<hi;k++){
  I t=I(k,k+1)/P;
  I z=I(1)-I(polyF(t.r).l,polyF(t.l).r);
  I den=withPNT?t*(1-t):t;
  res=res+z/(den*P);
 }
 return res;
}

int main(){
 static_assert(numeric_limits<double>::is_iec559);
 if(fesetround(FE_TONEAREST))abort();
 sieve_constants();rho2();prep_b(800);
 const I mZ=source(30,800,1),m0=source(30,800,0);
 const int dp=40,beta=800;
 I bounds[8100];
 for(int z=0;z<=8000;z++)bounds[z]=bound2(z,0,beta);
 int count=0;
 I V=0,full=0,ma0=0,mt0=0,signedUpper=0;
 double largest=0,smallest=1e10;
 for(int i=30;i<800;i+=dp)for(int j=i;j<800;j+=dp)for(int l=j;l<800;l+=dp){
    int iu=min(800,i+dp),ju=min(800,j+dp),lu=min(800,l+dp);
    I u=I(i,iu)/P,v=I(j,ju)/P,w=I(l,lu)/P;
    int rep=i==l?6:(i==j||j==l?2:1);
    I vv=(I(iu-i)/P)*(I(ju-j)/P)*(I(lu-l)/P)/rep;
    mark3=w;prep_g(2,u,v);
    const int hi=iu+ju+lu;
    I M=fplus(neg(at0))*upper1(4990-hi)*mZ, T=0;
    I L1=at0*lower1(4990-hi)*mZ, LT=0;
    if(at0.r>=0)abort();
    for(int k=800;k<5000;k++){
       const I e=fplus((pf[0][k]-pf[1][k])/2), o=fplus((pf[0][k]+pf[1][k])/2);
       const I g=profile[0][k],gp=fplus(g),gm=fplus(neg(g));
       const int D=4990-hi-k-1;
       I C2=bounds[hi+k+1];
       I lower=C2*(o*gp+e*gm)*m0, upper=C2*(e*gp+o*gm)*m0;
       bool chooseMain=false;
       if(D>0){
          const I U=upper1(D), K0=lower1(D);
          I ml=((U*o-K0*e)*gp+(U*e-K0*o)*gm)*mZ;
          I mu=((U*e-K0*o)*gp+(U*o-K0*e)*gm)*mZ;
          if(ml.r<lower.r){
             lower=ml;
             chooseMain=true;
          }
          if(mu.r<upper.r)upper=mu;
       }
       if(chooseMain)M=M+lower/P;else T=T+lower/P;
       LT=LT+upper/P;
    }
    const I C=M+T;
    largest=max(largest,C.r);
    smallest=min(smallest,C.r);
    full=full+vv*C; signedUpper=signedUpper+vv*(L1+LT);V=V+vv;ma0=ma0+vv*M;mt0=mt0+vv*T;
    count++;
 }
 if(count!=1540 || (2*full).r>=(I(228708)/1000000).l ||
    (2*signedUpper).r>=neg(I(9508)/1000000).l ||
    (2*mt0).r>=(I(71792)/1000000).l)abort();
 printf("E2-source %.8f %.8f, boxes %d volume %.14f max/min %.8f %.8f main %.10f tail %.10f bilateral debit %.12f, upper %.12f\n",
       mZ.r,m0.r,count,V.r,largest,smallest,(2*ma0).r,(2*mt0).r,(2*full).r,(2*signedUpper).r);
}
"""
with tempfile.TemporaryDirectory(prefix="sextic-e2-by-three-") as run:
    src = Path(run, "proof.cpp")
    out = Path(run, "proof")
    src.write_text(text)
    subprocess.run(
        ["c++", "-O3", "-std=c++17", "-ffp-contract=off", "-fno-fast-math",
         str(src), "-o", str(out)], check=True
    )
    subprocess.run([str(out)], check=True)
