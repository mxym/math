#!/usr/bin/env python3
"""Exact consequential calculations, conditional on Tandon's realized input families."""
import json
from itertools import combinations, product
from math import prod
from pathlib import Path

data = json.loads(Path(__file__).with_name("c7_data.json").read_text())
alphabet = "BNADOHV"

def check(test, error):
    if not test:
        raise ValueError(error)

def vector(xs):
    check(len(xs) == len(alphabet) and all(type(x) is int and x >= 0 for x in xs), "weights")
    return dict(zip(alphabet, xs))

check(data["alphabet"] == alphabet, "alphabet")
edges = set(data["separated_pairs"])
check(edges == set("BO BH BV NA ND NO NH NV AD AH DV".split()), "separated pairs")

def sep(a, b):
    return a+b in edges or b+a in edges

def separated(x, y):
    return any(sep(a, b) for a, b in zip(x, y))

def check_code(words, arity):
    check(len(set(words)) == len(words), "duplicate word")
    check(all(len(w) == arity and all(a in alphabet for a in w) for w in words), "bad word")
    check(all(separated(x,y) for x,y in combinations(words,2)), "nonseparated words")

S, K = data["S3b"], data["K4a"]
check(set(S) == set(alphabet), "missing lane")
for words in S.values():
    check_code(words, 3)
for a,b in edges:
    check(all(separated(x,y) for x,y in product(S[a],S[b])), "cross-family separation")
check_code(K, 4)
flip_index = dict(zip(alphabet, "BNDAOVH"))
check(all(sep(a,b) == sep(flip_index[a], flip_index[b]) for a,b in product(alphabet,repeat=2)), "bad flip")

def flip(x):
    return {a:x[b] for a,b in flip_index.items()}

def weight(words, children):
    return sum(prod(child[a] for a,child in zip(word,children)) for word in words)

def middle(children):
    return {a: weight(words, children) for a,words in S.items()}

def terminal(x):
    plain = weight(K, [x]*4)
    check(weight(K, [x, flip(x), x, flip(x)]) == plain, "instance-specific orientation equality")
    return plain

P,Q,R,T = [vector(data["Tandon"][tag]) for tag in ("6","11","8","25")]
check(middle([P,Q,R]) == T, "Tandon intermediate vector, Eq. (163)")
check(weight(K,[T]*4) == int(data["Tandon_M500"]), "Tandon terminal, Eq. (164)")
W = middle([P,Q,Q])
check(W == {a:int(v) for a,v in data["Stavriianov_W"].items()}, "Stavriianov Appendix A vector")
M0 = terminal(W)
check(M0 == int(data["Stavriianov_M560"]), "Stavriianov Appendix A integer")
check(set(S["B"]) & set(S["N"]) == {"AHN"}, "shared word")
c = P["A"] * Q["H"] * Q["N"]
check(0 < c <= min(W["B"], W["N"]), "nonempty common box")
residual = dict(W, B=W["B"]-c, N=W["N"]-c)
M = terminal(residual)
scale, lo, old = 10**15, 3258834499096250, 3258834362237710
check(old**560 < M0*scale**560 < (old+1)**560, "unpeeled bracket")
L, H = lo**140 - c*scale**140, (lo+1)**140 - c*scale**140
check(0 < L and L**4 < M*scale**560 < H**4, "new asymptotic bracket")
check(old+1 < lo, "strict improvement over cited certificate")
print("Both unpeeled orientations reproduce the exact 560th-power integer of Stavriianov.")
print("Both peeled orientations give the same M.")
print("c =", c)
print("M =", M)
print("3.258834499096250 < (c+M^(1/4))^(1/140) < 3.258834499096251")
