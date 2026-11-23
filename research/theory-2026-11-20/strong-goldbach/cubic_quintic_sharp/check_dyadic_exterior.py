#!/usr/bin/env python3
"""Ordinary lower from the previously certified true interior layers."""
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path

p=Path(__file__).resolve().with_name("check_wider_positive.py")
raw=p.read_bytes()
if sha256(raw).hexdigest()!="2a310afc0aeaef6f1dcf97de604731f8d9348099711dd8f1f36e28f65bcbeeac":
    raise ArithmeticError("different verified angular checker")
env={"__file__":str(p)}
exec(compile(raw,str(p),"exec"),env)
ml=sum(env["means"])/env["R"]
a=F(".077983212")+F(".00672821")
guard=1-F("2.0377")**2+2*F(".08472")+F(".08472")**2
if not (ml>F("2.0377") and a<F(".08472") and guard<-F("2.975")):
    raise ArithmeticError("dyadic weighted exterior guard failed")
print("ordinary genuine positive mass lower:",float(ml))
print("dyadic normalized exterior mean upper:",float(guard))
