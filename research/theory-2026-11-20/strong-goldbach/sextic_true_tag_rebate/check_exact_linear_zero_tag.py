from pathlib import Path
import tempfile, subprocess
from hashlib import sha256
p = Path(__file__).resolve().with_name("check_full_zero_tag_affine_self.py")
r = p.read_bytes()
if sha256(r).hexdigest() != "848d4efd005f6ad5e222ff1bf4bd6967f67a66398ecd28a8ff15308b0f926a98":
    raise ArithmeticError("different full zero-tag checker")
head, sep, tail = r.decode().partition('\ntext += r"""')
before, sep2, _ = tail.partition('\nint main(){')
if not sep or not sep2:
    raise ArithmeticError("ambiguous full zero-tag checker boundary")
env = {"__file__": str(p)}
exec(compile(head, str(p), "exec"),env)
text = env["text"]+before
text += r"""
I Fscaled[4991],fscaled[4991];
void linear_delays(){
 for(int j=0;j<=2400;j++) Fscaled[j]=2;
 for(int j=1600;j<4990;j++) {
   const int t=j-800;
   I AF=I(Fscaled[t].l,Fscaled[t+1].r);
   fscaled[j+1]=fscaled[j]+AF/I(t,t+1);
   if(j>=2400) {
     I Af=I(fscaled[t].l,fscaled[t+1].r);
     Fscaled[j+1]=Fscaled[j]+Af/I(t,t+1);
   }
 }
}
I upLin(int lev){
 if(lev<=0||lev>4990)abort();
 return I(P)*Fscaled[lev]/lev;
}
I lowLin(int lev){
 if(lev<=0||lev>4990)abort();
 if(lev<=1600)return 0;
 return I(P)*fscaled[lev]/lev;
}
I exactPi(){
 I total=upLin(4990);
 for(int j=800;j<5000;j++){
   I e=fplus((pf[0][j]-pf[1][j])/2),o=fplus((pf[0][j]+pf[1][j])/2);
   I g=polybox(j,j+1);
   I plus=bound2(j+1,0,0)*e*g;
   int D=4990-j-1;
   if(D>0){
     I cand=(upLin(D)*e-lowLin(D)*o)*g;
     if(cand.r<plus.r)plus=cand;
   }
   total=total+I(plus.r)/P;
 }
 return total;
}
int main(){
 static_assert(numeric_limits<double>::is_iec559);
 if(fesetround(FE_TONEAREST))abort();
 rho2();prep_b(800);linear_delays();
 I pi=exactPi();
 I net=I(9585)/1000-2*pi-2*I(16840)/1000000;
 if(!(upLin(4990).r<7.02159 && pi.r<3.729964 && net.l>2.091))abort();
 printf("exact-linear prime atom [%.12f,%.12f], prime cross upper %.12f; old rounded %.12f; net at old raw and Q %.12f\n",
        upLin(4990).l,upLin(4990).r,pi.r,estimatePi().r, net.l);
}
"""
with tempfile.TemporaryDirectory(prefix="goldbach-full-zero-tag-linear-") as p:
    src=Path(p)/"check.cpp"
    exe=Path(p)/"check"
    src.write_text(text)
    subprocess.run(["g++","-O3","-fno-fast-math","-ffp-contract=off",str(src),"-o",str(exe)],check=True)
    subprocess.run([str(exe)],check=True)
