#!/usr/bin/env python3
"""Directed rational replay of the selected real-drift constants."""
from fractions import Fraction as F


def check(b, what):
    if not b:
        raise ArithmeticError(what)


def log_bounds(q, terms=15):
    z=(q-1)/(q+1)
    v=2*sum(z**(2*j+1)/(2*j+1) for j in range(terms))
    return v, v+2*z**(2*terms+1)/((2*terms+1)*(1-z*z))


def run():
    x=F("0.000001")
    check(F(".3")<F(".7") and F(".8")<1,"true small prime order")
    check(F(".2")-F(".18")>0 and F(".1")>0,"own-root strict endpoints")
    qmin=F(".5")+x*(F(".2")+F(".7")-F(".18"))
    qmax=F(".5")+x*(F(".3")+F(".8")-F(".10")+10)
    delta=F(".00002")
    check(qmax==F(".500011")<F(".5")+delta,"physical product")
    q3_upper=F(".078")+10*x+(F(".5")+delta-qmin)
    check(q3_upper<F(".07804"),"allowed enlargement")
    check(F(".10024")-F(".029")<F(".075") and
          F(".07804")<F(".09992")-F(".6")*F(".031"),"Maynard actual wedge")
    check(F(".5")-F(".18")*x-2*(F(".031")+F(".078"))>F(".28"),
          "four-prime factor moment floor")
    for q,lo,hi in [(F(31,29),F(".06"),F(".07")),(F(78,75),F(".035"),F(".04")),
                    (F(3,2),F(".40"),F(".41")),(F(8,7),F(".13"),F(".14"))]:
        a,b=log_bounds(q)
        check(lo<a<b<hi,("true reciprocal prime band",q,a,b))
    check(log_bounds(F(3))[0]>1,"lower terminal sieve coefficient")
    m1=F(".08")*F(".5")*F(".06")*F(".035")
    a=F(".07"); b=F(".04")
    m2=F(".08")*F(2,3)*(a*a*b*b+a*b*b+a*a*b)
    check(m1==F(".000084") and m2<F(".00001685"),"factorial moments")
    check(m1-m2/2>F(".00007"),"certified actual union")
    main=F(".5")*F(".5")*F(".40")*F(".13")*F(".00007")*F(".8")
    check(main==F(".000000728")>F(".0000007"),"final strict drift reserve")
    print("all exact Maynard rails, logarithm intervals, tag moments and drift certified")


if __name__=="__main__":
    run()
