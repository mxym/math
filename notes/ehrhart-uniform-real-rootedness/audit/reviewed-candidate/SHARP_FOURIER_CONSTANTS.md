# Explicit Fourier constants at variance at least 20 (parent, internal)

Let C2(V) and A1(V) be the quantities in CENTERED_COMPARISON_LEMMA.md.
For V>=20 the following stronger bounds hold:
 C2(V)<(3/5)V^(-3/2), A1(V)<(1/3)V^(-3/2).
They replace the earlier deliberately crude Gaussian-envelope constants.

For |t|<=1, sin(t/2)>=t/2-t^3/48, hence
 2 sin^2(t/2)>= (11/24)t^2.
For 1<=|t|<=pi, 2 sin^2(t/2)>=529/1152, since sin(1/2)>=23/48.
Thus C2(V) is bounded by the full Gaussian second moment with precision
11V/12, plus pi^2 exp(-529V/1152). The former is less than
(12/25)V^(-3/2), using sqrt(2pi)>12/5 and squaring the rational residual
comparison. For the latter, V^(3/2)exp(-529V/1152) decreases at V>=20.
At V=20 use pi^2<10,20^(3/2)<90, and exp(9)>8000; its normalized contribution
is <900/8000=9/80. Since 12/25+9/80<3/5, the first claim follows.

For A1 put W=V-1/4>=79V/80. The bound on Im psi gives V/6 times the fourth
moment integral at variance W. Split [0,pi] at 1 and pi/2.
The first part, enlarged to the whole Gaussian line, is less than
(8/5)W^(-5/2).
On [1,pi/2], sin t>=sin 1>5/6, so
 2sin^2(t/2)>=529/1152+(5/6)(t-1).
Using t^4<7 and pi>3 bounds this portion of the normalized fourth integral
by (14/(5W))exp(-529W/1152).
The final interval has 2sin^2(t/2)>=1 and contributes <100exp(-W).
Consequently
 A1(V)<(4/15)V W^(-5/2)
       +(7/15)(V/W)exp(-529W/1152)+(50/3)V exp(-W).
Multiplying by V^(3/2), the first term is <(4/15)(26/25), since
(80/79)^(5/2)<(80/79)^3<26/25.
The second term is <(7/15)(80/79)*90/8000.
The third term is <(50/3)*1800/100000000.
For the last two comparisons the normalized exponential functions decrease
on V>=20; 529*(79/4)/1152>9, 79/4>19, and exp(19)>100000000.
The sum of these three rational upper bounds is <1/3.

The exponential inequalities have elementary exact finite certificates:
sum_(k=0)^40 9^k/k!>8000 and sum_(k=0)^60 19^k/k!>100000000.
These were checked with Python Fraction arithmetic; the sums themselves are
the proof witnesses. No numerical integral or root approximation is used.

Use only under the explicit V>=20 condition; the small-variance regime still
uses the earlier bounded integral estimates or requires sharper treatment.
No uniform real-rootedness conclusion has yet been obtained.
