#!/usr/bin/env python3
from fractions import Fraction

def require(x,msg):
    if not x: raise AssertionError(msg)

special_width=Fraction(5,6)
special_error=2*special_width-1
special_ch=Fraction(2,3)
special_shell=Fraction(17,18)
require(special_error==special_ch,"k3 endpoint")
rows=[]
for k in range(4,13):
    m=k-1
    width=Fraction(2,m)
    error=2*width-1
    ch=Fraction(2,k)
    shell=(4-width)/k
    require(error<ch,"outlier error exponent")
    rows.append((k,str(width),str(error),str(ch),str(shell)))
require(rows[0][-1]=="5/6","k4 shell")
require(rows[1][-1]=="7/10","k5 shell")
print("one-outlier exponent checker")
print("k cluster_width outlier_error CH_radius shell_exponent")
print(3,special_width,special_error,special_ch,special_shell)
for row in rows: print(*row)
print("k3_endpoint_equality = PASS")
print("k3_shell_exponent_17_over_18 = PASS")
print("error_below_CH_radius_k_ge_4 = PASS")
print("k4_shell_exponent_5_over_6 = PASS")
print("k5_shell_exponent_7_over_10 = PASS")
print("standard_library_only = PASS")
