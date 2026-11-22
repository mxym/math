from fractions import Fraction as Q
from hashlib import sha256
from pathlib import Path
import tempfile
import subprocess

p = Path(__file__).resolve().with_name("check_exact_linear_zero_tag.py")
raw = p.read_bytes()
if sha256(raw).hexdigest() != "93836c99392dfe227966eed5c1b0baf30343a63d3ccc2520b15d70b31f89d3f6":
    raise ArithmeticError("different exact-linear checker")
head, sep, tail = raw.decode().partition('\ntext += r"""')
before, sep2, _ = tail.partition('\nint main(){')
if not sep or not sep2:
    raise ArithmeticError("ambiguous linear checker")
env = {"__file__": str(p)}
exec(compile(head, str(p), "exec"), env)
text = env["text"] + before
text += r"""
I exactPiLower(){
 I total=lowLin(4990);
 for(int j=800;j<5000;j++){
   I e=fplus((pf[0][j]-pf[1][j])/2),o=fplus((pf[0][j]+pf[1][j])/2);
   I g=polybox(j,j+1);
   I debit=bound2(j+1,0,0)*o*g;
   int D=4990-j-1;
   if(D>0){
     I cand=(upLin(D)*o-lowLin(D)*e)*g;
     if(cand.r<debit.r)debit=cand;
   }
   total=total-I(debit.r)/P;
 }
 return total;
}
int main(){
 static_assert(numeric_limits<double>::is_iec559);
 if(fesetround(FE_TONEAREST))abort();
 rho2();prep_b(800);linear_delays();
 I pi=exactPiLower();
 if(!(pi.l>3.25555))abort();
 printf("same physical prime cross lower %.12f\n",pi.l);
}
"""
with tempfile.TemporaryDirectory(prefix="goldbach-exact-prime-occupation-") as d:
    src = Path(d)/"check.cpp"
    exe = Path(d)/"check"
    src.write_text(text)
    subprocess.run(["g++", "-O3", "-fno-fast-math", "-ffp-contract=off", str(src), "-o", str(exe)], check=True)
    subprocess.run([str(exe)], check=True)

tiny = Q(".228") + Q("3.446")*(Q(".009042")+Q(".006657")+Q(".0000001"))/2
rebate = Q("3.25555")-1-Q(".52844")-tiny
if not (tiny<Q(".25506") and rebate>Q("1.472")):
    raise ArithmeticError("physical prime occupancy bound failed")
print("one-orientation signed prime occupancy lower",float(rebate))
