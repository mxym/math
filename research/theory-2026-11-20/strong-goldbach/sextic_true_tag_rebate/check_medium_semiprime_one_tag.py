from hashlib import sha256
from pathlib import Path
import subprocess
import tempfile

# Reuse the audited real subroot coefficients, ordinary densities, and
# q-only additional denominator in the affine prime–rough upper.
base = Path(__file__).resolve().with_name("check_small_semiprime_three_tag.py")
raw = base.read_bytes()
if sha256(raw).hexdigest() != (
    "27d2df301617567e940c97f26eb7c5e82a2c9c31d6ea333f873b1b6f11b1716e"
):
    raise ArithmeticError("different affine checker")
prefix, sep, cpp = raw.decode().partition('\ntext += r"""')
if not sep or cpp.count("\nint main(){") != 1:
    raise ArithmeticError("ambiguous reused wrapper")
env = {"__file__": str(base)}
exec(compile(prefix, str(base), "exec"), env)
text = env["text"] + cpp.split("\nint main(){")[0]

text += r"""
int main(){
 static_assert(numeric_limits<double>::is_iec559);
 if(fesetround(FE_TONEAREST))abort();
 sieve_constants();rho2();prep_b(800);
 const I mZ=source(800,1251,1),m0=source(800,1251,0);
 I bounds[5300];
 for(int z=0;z<=5260;z++)bounds[z]=bound2(z,0,1251);
 I LB=0, UB=0;
 int n=0,left_tail=0,right_tail=0;
 for(int i=30;i<260;i+=10){
    const int iu=i+10;
    const I t=I(i,iu)/P;
    mark3=0;
    prep_g(0,t,0);
    if(at0.l<=0)abort();
    I L1=at0*lower1(4990-iu)*mZ;
    I U1=at0*upper1(4990-iu)*mZ;
    for(int j=800;j<5000;j++){
       const I even=fplus((pf[0][j]-pf[1][j])/2);
       const I odd=fplus((pf[0][j]+pf[1][j])/2);
       const I g=fplus(profile[0][j]); // F is nonincreasing
       const int D=4990-iu-j-1;
       const I C2=bounds[iu+j+1];
       double debit=(C2*odd*g*m0).r, addition=(C2*even*g*m0).r;
       bool lt=true, rt=true;
       if(D>0){
          const I U=upper1(D),k=lower1(D);
          const double mL=((U*odd-k*even)*g*mZ).r;
          const double mU=((U*even-k*odd)*g*mZ).r;
          if(mL<debit){debit=mL;lt=false;}
          if(mU<addition){addition=mU;rt=false;}
       }
       left_tail+=lt;right_tail+=rt;
       L1=L1-I(debit)/P;
       U1=U1+I(addition)/P;
    }
    const I vol=I(iu-i)/P;
    LB=LB+vol*L1;
    UB=UB+vol*U1;
    n++;
 }
 const I lo=2*LB,hi=2*UB;
 printf("medium E2 by one tag: %d complete cells, affine selections %d/%d, bilateral [%.12f, %.12f]\n",
        n,left_tail,right_tail,lo.l,hi.r);
 if(n!=23||lo.l<=neg(I(180204)/1000000).r||
    hi.r>=neg(I(70082)/1000000).l)abort();
}
"""
with tempfile.TemporaryDirectory(prefix="sextic-e2-by-one-") as run:
    src = Path(run, "proof.cpp")
    out = Path(run, "proof")
    src.write_text(text)
    subprocess.run(
        ["c++", "-O3", "-std=c++17", "-ffp-contract=off", "-fno-fast-math",
         str(src), "-o", str(out)], check=True
    )
    subprocess.run([str(out)], check=True)
