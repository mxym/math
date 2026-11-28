#!/usr/bin/env python3
"""Check the remaining cyclic four-player/eight-good EFX cases.

Uses exact SMT. A case can instead be emitted as portable SMT-LIB.
  python3 verify_factor_efx_cyclic_eight_goods.py
  python3 verify_factor_efx_cyclic_eight_goods.py --case fixed --emit | z3 -in
  python3 verify_factor_efx_cyclic_eight_goods.py --case pair_top --match --bv --emit
"""
import argparse
import ctypes
import ctypes.util
from itertools import combinations, permutations, product
import shutil
import subprocess

if not __debug__:
    raise RuntimeError("run without Python -O")

I = tuple(range(4))
G = tuple(range(8))
MASKS = tuple(S for S in range(256) if S.bit_count() <= 5)
TRIMS = tuple(tuple(S ^ (1 << g) for g in G if S & (1 << g) and S != (1 << g))
              for S in range(256))
CASES = {
    # name: (good orbit sizes, designated top good, second-largest good)
    "fixed": ((1,1,1,1,4), 0, None),
    "second_fixed": ((1,1,2,4), 0, 1),
    "second_pair": ((1,1,2,4), 0, 2),
    "second_four": ((1,1,2,4), 0, 4),
    "pair_top": ((1,1,2,4), 2, None),
    "two_pairs": ((2,2,4), 0, None),
}

def all_partitions():
    out = set()
    for assignment in product(I, repeat=8):
        A = [0] * 4
        for g, i in enumerate(assignment):
            A[i] |= 1 << g
        if all(A):
            out.add(tuple(sorted(A)))
    assert len(out) == 1701
    return sorted(out)

def act(shape, k):
    shift, good = 0, []
    for d in shape:
        good.extend(shift + (j+k) % d for j in range(d))
        shift += d
    assert shift == 8
    image = [0] * 256
    for x in range(1, 256):
        b = x & -x
        image[x] = image[x ^ b] | (1 << good[b.bit_length()-1])
    return image

def base_order(shape, top, second):
    arcs = {(S, S | (1 << g)) for S in MASKS if S.bit_count() < 5
            for g in G if not (S & (1 << g))}
    def above(a, b):
        assert a != b
        arcs.add((1 << b, 1 << a))
    for g in G:
        if g != top:
            above(top, g)
    fixed, pairs, four = [], [], None
    shift = 0
    for d in shape:
        if d == 1:
            fixed.append(shift)
        elif d == 2:
            pairs.append(shift)
        else:
            assert d == 4 and four is None
            four = shift
        shift += d
    assert four == 4
    for a, b in zip(fixed, fixed[1:]):
        above(a, b)
    for a in pairs:
        above(a, a+1)
    for b in (5,6,7):
        above(four, b)
    above(5, 7)  # reversal of the cyclic generator
    if second is not None:
        for b in (1,2,4):
            if b != second:
                above(second, b)
    reach = [1 << s for s in range(256)]
    for x, y in arcs:
        reach[x] |= 1 << y
    for z in MASKS:
        for s in MASKS:
            if reach[s] & (1 << z):
                reach[s] |= reach[z]
    assert all(not (reach[y] & (1 << x)) for x,y in arcs)
    return arcs, reach

def formula(case, by_matching=False, bv=False):
    shape, top, second = CASES[case]
    action = [act(shape,k) for k in I]
    for g,h in product(I, repeat=2):
        assert all(action[g][action[h][s]] == action[(g+h)%4][s]
                   for s in range(256))
    parts = [A for A in all_partitions() if A == min(
        tuple(sorted(p[s] for s in A)) for p in action)]
    arcs, R = base_order(shape, top, second)
    sort = "(_ BitVec 8)" if bv else "Int"
    op = "bvult" if bv else "<"
    def lt(a, b):
        return f"({op} v{a} v{b})"
    f = [f"(declare-const v{s} {sort})" for s in MASKS]
    f.append("(assert (= v0 #x00))" if bv else "(assert (= v0 0))")
    f += [f"(assert {lt(x,y)})" for x,y in sorted(arcs)]
    rejects = {}
    atom_defs = {}
    clauses = []
    for A in parts:
        rejects.clear()
        for i in I:
            p = action[(-i) % 4]
            for j in I:
                own = p[A[j]]
                targets = {p[t] for k in I if k != j for t in TRIMS[A[k]]}
                if any(x != own and R[own] & (1 << x) for x in targets):
                    token = "true"
                else:
                    allowed = {x for x in targets if not (R[x] & (1 << own))}
                    maximal = tuple(sorted(x for x in allowed
                                           if not any(x != y and R[x] & (1 << y)
                                                      for y in allowed)))
                    if not maximal:
                        token = "false"
                    elif len(maximal) == 1:
                        token = lt(own, maximal[0])
                    else:
                        key = (own, maximal)
                        if key not in atom_defs:
                            token = f"r{len(atom_defs)}"
                            atom_defs[key] = token
                            f.append(f"(declare-const {token} Bool)")
                            f.append(f"(assert (= {token} (or " +
                                     " ".join(lt(own,x) for x in maximal) + ")))")
                        token = atom_defs[key]
                rejects[i,j] = token
        if by_matching:
            # Independent equivalent test: exclude every labelled matching.
            rows = set()
            for p in permutations(I):
                row = {rejects[i,j] for i,j in enumerate(p)}
                if "true" not in row:
                    rows.add(tuple(sorted(row - {"false"})))
            for row in sorted(rows):
                clauses.append("(assert (or " + " ".join(row) + "))" if row
                               else "(assert false)")
        else:
            choices = set()
            for d in (2,3,4):
                for X in combinations(I,d):
                    for Y in combinations(I,5-d):
                        choice = {rejects[i,j] for i in X for j in Y}
                        if "false" not in choice:
                            choices.add(frozenset(choice - {"true"}))
            retained = []
            for option in sorted(choices, key=lambda x: (len(x), sorted(x))):
                if not any(s <= option for s in retained):
                    retained.append(option)
            if not retained:
                clauses.append("(assert false)")
            elif all(retained):
                terms = ["(and " + " ".join(sorted(s)) + ")" for s in retained]
                clauses.append("(assert (or " + " ".join(terms) + "))")
    f += clauses
    return f,len(parts),len(atom_defs),len(clauses)

def solve_z3(f, logic, timeout, text):
    path = ctypes.util.find_library("z3")
    if not path:
        prog = shutil.which("z3")
        if prog is None:
            raise RuntimeError("Z3 not found; use --emit and an exact SMT solver")
        return subprocess.run([prog,"-in"],input=text,text=True,
                              check=True,capture_output=True).stdout.strip()
    lib = ctypes.CDLL(path)
    P = ctypes.c_void_p
    C = ctypes.c_char_p
    def call(name,args,result=None):
        func = getattr(lib,name)
        func.argtypes,func.restype = args,result
        return func
    config = call("Z3_mk_config",[],P)()
    call("Z3_set_param_value",[P,C,C])(config,b"timeout",str(timeout).encode("ascii"))
    ctx = call("Z3_mk_context",[P],P)(config)
    call("Z3_del_config",[P])(config)
    sym = call("Z3_mk_string_symbol",[P,C],P)(ctx,logic.encode("ascii"))
    solver = call("Z3_mk_solver_for_logic",[P,P],P)(ctx,sym)
    call("Z3_solver_inc_ref",[P,P])(ctx,solver)
    call("Z3_solver_from_string",[P,P,C])(ctx,solver,"\n".join(f).encode("ascii"))
    value = call("Z3_solver_check",[P,P],ctypes.c_int)(ctx,solver)
    result = {-1:"unsat",0:"unknown",1:"sat"}[value]
    if value == 0:
        reason = call("Z3_solver_get_reason_unknown",[P,P],C)(ctx,solver)
        result += ": "+reason.decode("ascii")
    call("Z3_del_context",[P])(ctx)
    return result

def main():
    p = argparse.ArgumentParser()
    p.add_argument("--case",choices=CASES)
    p.add_argument("--emit",action="store_true")
    p.add_argument("--match",action="store_true",
                   help="exclude all labelled matchings instead of using Hall")
    p.add_argument("--bv",action="store_true",
                   help="use unsigned 8-bit ranks instead of unbounded integers")
    p.add_argument("--timeout-ms",type=int,default=0,
                   help="zero means no timeout; unknown is not a proof")
    q = p.parse_args()
    if q.emit and q.case is None:
        p.error("--emit requires --case")
    for key in (q.case,) if q.case else CASES:
        f, n, atoms, clauses = formula(key,q.match,q.bv)
        logic = "QF_BV" if q.bv else "QF_IDL"
        text = "\n".join([f"(set-option :timeout {q.timeout_ms})",
                          f"(set-logic {logic})", *f, "(check-sat)", ""])
        if q.emit:
            print(text,end="")
        else:
            print(key,n,atoms,clauses,flush=True)
            result = solve_z3(f, logic, q.timeout_ms, text)
            print(result,flush=True)
            if result != "unsat":
                raise RuntimeError(f"{key} did not return UNSAT: {result}")

if __name__ == "__main__":
    main()
