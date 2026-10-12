from fractions import Fraction as F
from math import factorial
import json
from pathlib import Path

checks=[]
def need(name,condition,witness):
    if not condition: raise RuntimeError(name)
    checks.append({'name':name,'status':'PASS','witness':str(witness)})

# Additional residuals used by the analytic notes, independent of their scripts.
piu=F(22,7)
pilo=F(31,10)
need('C2 sharp Gaussian bound via sqrt(2pi)>12/5',
     (F(5,12)**2)*F(12,11)**3 < F(12,25)**2,
     F(12,25)**2-(F(5,12)**2)*F(12,11)**3)
need('A1 sharp Gaussian fourth-moment bound',
     (F(5,4)**2)*F(12,11)**5 < F(8,5)**2,
     F(8,5)**2-(F(5,4)**2)*F(12,11)**5)
need('C2 Fourier tail margin',F(12,25)+F(9,80)<F(3,5),F(3,5)-F(12,25)-F(9,80))
need('A1 ratio residual',(F(80,79)**3)<F(26,25),F(26,25)-F(80,79)**3)
need('A1 exponent exceeds nine',F(529,1152)*F(79,4)>9,F(529,1152)*F(79,4))
need('exp nine finite positive lower bound',sum((F(9)**k/factorial(k) for k in range(41)),F())>8000,'40-term positive sum')
need('exp nineteen finite positive lower bound',sum((F(19)**k/factorial(k) for k in range(61)),F())>100000000,'60-term positive sum')
sharpA=F(4,15)*F(26,25)+F(7,15)*F(80,79)*F(90,8000)+F(50,3)*F(1800,100000000)
need('A1 sharp final residual',sharpA<F(1,3),sharpA)
need('large-saddle W relative C2 constant',
     (F(7,2)*F(3,5))**2 < F(27,10)**2*F(17,20)**3,
     F(27,10)**2*F(17,20)**3-(F(7,2)*F(3,5))**2)
need('large-saddle Vn relative A1 constant',
     (F(7,2)*F(1,3))**2 < F(3,2)**2*F(6,7)**3,
     F(3,2)**2*F(6,7)**3-(F(7,2)*F(1,3))**2)
need('large-saddle variance-order margin at dv>=30',
     F(7,8)-F(3,4)/30>=F(17,20),
     F(7,8)-F(3,4)/30)
need('large-saddle Vn margin at dv>=30', F(7,8)-F(1,2)/30>=F(6,7),F(7,8)-F(1,2)/30)
need('large-saddle inverse-mode margin at dv>=30',12+F(7,30)<F(49,4),12+F(7,30))
need('large-saddle eta endpoint',F(15,16)/F(7*1001,8)<F(1,500),F(15,16)/F(7*1001,8))
need('middle-primitive A<4',(F(1001,1000)**2)*8<16,F(1001,1000)**2*8)
need('large-saddle middle atom ratio<4',F(49,4)*F(30,29)<16,F(49,4)*F(30,29))
need('majorant Gaussian coefficient<16/25',piu/8<F(16,25)**2,F(16,25)**2-piu/8)
need('small-saddle maximal smoothing coefficient',piu/(8*F(1,6)*F(4,5))<F(15,4),piu/(8*F(1,6)*F(4,5)))
need('small-saddle primitive scale>5/19',
     (F(1000,1001)**2)/(4*piu*F(11,10)) > F(5,19)**2,
     (F(1000,1001)**2)/(4*piu*F(11,10))-F(5,19)**2)
need('small-saddle large-component coefficient<35/2',
     (F(19,5)*F(23,10))**2*F(15,4)<F(35,2)**2,
     F(35,2)**2-(F(19,5)*F(23,10))**2*F(15,4))
need('small-saddle large-component divided by E<169/d',F(35,2)*8*F(4,5)*F(3,2)<169,F(35,2)*8*F(4,5)*F(3,2))
need('small-saddle Jensen first-moment cap',F(2,5)+F(16,25)*F(3,25)<F(13,25),F(2,5)+F(16,25)*F(3,25))
v_lin=F(2,5)*F(4,5)+F(2,5)+F(16,25)*F(3,25)
mean_sq=F(2,5)+2*F(16,25)*F(3,25)+F(16,25)**2*F(1,5)
need('small-saddle Jensen variance cap',v_lin<F(21,25),v_lin)
need('small-saddle component squared-mean cap',mean_sq<F(21,25),mean_sq)
need('small-saddle raw second moment cap',F(21,25)+(F(21,25)+F(169,625))/10<F(24,25),F(21,25)+(F(21,25)+F(169,625))/10)
need('small-saddle shifted absolute moment cap',F(29,25)+F(1,4*1001)<F(117,100),F(29,25)+F(1,4*1001))
need('small-saddle shifted second moment cap',
     F(24,25)+2*F(29,25)*F(1,10)*F(1,4*1001)+F(1,10)*F(1,4*1001)**2<F(97,100),
     F(24,25)+2*F(29,25)*F(1,10)*F(1,4*1001)+F(1,10)*F(1,4*1001)**2)
need('small-saddle coefficient-compare multiplier',
     F(5,4)*F(9,4)*(F(12,5)*50+F(117,100)*100+F(97,200)*50)<735,
     F(5,4)*F(9,4)*(F(12,5)*50+F(117,100)*100+F(97,200)*50))
need('small-saddle middle atom ratio<5 at y>5/2',
     F(1,2)*(F(24,5)*F(5,2)+1)/(F(9,55)*F(5,2)-F(1,11))<25,
     F(1,2)*(F(24,5)*F(5,2)+1)/(F(9,55)*F(5,2)-F(1,11)))
need('large-saddle periodic endpoint',
     F(1296000)*1001**3*F(3,8)**50<1,
     F(1296000)*1001**3*F(3,8)**50)
need('forward mass cap',F(157,64)*F(79,30)<F(13,2),F(157,64)*F(79,30))
need('forward exponential polynomial cap',F(13,2)**3+6*F(13,2)**2+7*F(13,2)+1<687,F(13,2)**3+6*F(13,2)**2+7*F(13,2)+1)
need('forward prefactor cap',5000*687<2**22,5000*687)
need('forward rho14 and rho3',F(19,20)**14<F(1,2) and F(77,100)**3<F(1,2),'exact powers')
need('forward final residual',F(1,32)+F(1,2**266)<1,F(1,32)+F(1,2**266))
need('saddle 15 mean density cap',F(15,14)-F(15,98)*F(209,100)>F(751,1000),F(15,14)-F(15,98)*F(209,100))
# ln2<7/10 and ln8<209/100: the positive exponential sum suffices.
need('nu/x upper logarithm',sum((F(7,10)**k/factorial(k) for k in range(6)),F())>2,'exp(7/10)>2')
need('saddle 15 logarithm',sum((F(209,100)**k/factorial(k) for k in range(12)),F())>8,'exp(209/100)>8')
need('sum a^-5/2 from a=2 bound<3/8',
     F(1,4)*F(5,7)+F(1,3)*F(7,12)<F(3,8),
     F(1,4)*F(5,7)+F(1,3)*F(7,12))
out={'status':'PASS','scope':'Additional exact residual checks for manually reviewed analytic reductions; not a theorem prover or finite-data reconstruction','check_count':len(checks),'checks':checks}
print(json.dumps(out,indent=2))
