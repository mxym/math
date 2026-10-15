"""Author finite controls, separate from the full ordinary proof."""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import mpmath as mp
import sympy as sy


def frac(x):
    return str(x.numerator) + "/" + str(x.denominator)


def nearint(x):
    lo = x.numerator // x.denominator
    return lo + int(x - lo >= F(1, 2))


def solve(a, b):
    n = len(a)
    w = [list(row) + [b[i]] for i, row in enumerate(a)]
    for i in range(n):
        pivot = next(j for j in range(i, n) if w[j][i])
        w[i], w[pivot] = w[pivot], w[i]
        s = w[i][i]
        w[i] = [v / s for v in w[i]]
        for j in range(n):
            if j != i:
                s = w[j][i]
                w[j] = [v - s * u for v, u in zip(w[j], w[i])]
    return [row[-1] for row in w]


def positive_definite(a):
    w = [list(row) for row in a]
    for i in range(len(w)):
        if w[i][i] <= 0:
            return False
        for j in range(i + 1, len(w)):
            for k in range(j, len(w)):
                v = w[j][k] - w[j][i] * w[i][k] / w[i][i]
                w[j][k] = w[k][j] = v
    return True


def purity(m, n, kap, pos, neg):
    d, a = m * n, 2 + kap
    delta = sum(pos, F(0)) - sum(neg, F(0))
    total = sum(pos, F(0)) + sum(neg, F(0))
    energy = sum((v * v for v in pos + neg), F(0))
    bprime = d * (1 + kap) - kap * total - energy
    traceopt = 2 * bprime / a
    rank = nearint((traceopt - d - delta) / kap)
    trace = d + kap * rank + delta
    physical = (a * trace - bprime) / trace**2
    bound = a * a / (4 * bprime)
    assert bound - physical == a*a*(trace-traceopt)**2/(4*bprime*trace**2)
    assert m*(m-1)//2 <= rank <= d-m*(m+1)//2
    return physical, rank, bound, bound - physical


def body(m, n):
    d, t = m*n, F(2, m-1)
    k = ((m-1)*n+1)//2
    return F(d+(2*t+t*t)*k, (d+t*k)**2)


def parameters(m):
    z = F(2) + F(8, m)
    kap = 2 / (m-1+z)
    p = (2+kap)*z/(z+2)
    c = m*m*(F(2, m-1)-kap)
    h = 4*m*(m+z)*(z*(m+z+1)+2)/((2*m+z)*(z+2)**2)
    return z, kap, p, c, h


def main():
    mp.mp.dps = 240
    m, c, d, e, t, tt = sy.symbols("m c D E T t", positive=True)
    kap = 2/(m-1)-c/m**2
    t = 2/(m-1)
    bp = d*(1+kap)-kap*tt-e
    v = e+kap*tt-d/m**3*(c-(m*m-1)*c*c/(4*m**3))
    assert sy.cancel((2+kap)**2/(4*bp)-(2+t)**2/(4*d*(1+t))
                     -(2+t)**2*v/(4*d*(1+t)*bp)) == 0
    z, u, p = sy.symbols("z u p", positive=True)
    kh = 2/(m-1+z)
    ph = (2+kh)*z/(z+2)
    ch = m*m*(t-kh)
    cm = (m*m-1)/(4*m**3)
    hh = 4*m*(m+z)*(z*(m+z+1)+2)/((2*m+z)*(z+2)**2)
    assert sy.cancel(ch-cm*ch**2-m*z*(2*m+z)/(m-1+z)**2) == 0
    assert sy.cancel((ph**2+kh*ph)/(ch-cm*ch**2)-hh/m**2) == 0
    assert sy.cancel(kh*(m+z)/(2+kh)-1) == 0
    f = c-2*kap*m*m*p/((m-1)*(2+kap-p))
    assert sy.cancel(sy.diff(f,c)-1-2*p*(2-p)/((m-1)*(2+kap-p)**2)) == 0
    expanded = sy.series((hh/m**2).subs(m,1/u),u,0,3).removeO().expand()
    rs = [2*z/(z+2)**2, (3*z*z+2*z+4)/(z+2)**2,
          (z**3/2+z*z+2*z)/(z+2)**2]
    for j in range(3):
        assert sy.cancel(expanded.coeff(u,j)-rs[j]) == 0
    assert sy.diff(rs[0],z,2).subs(z,2) == -sy.Rational(1,32)
    assert sy.diff(rs[1],z).subs(z,2) == sy.Rational(1,4)
    assert rs[2].subs(z,2) == sy.Rational(3,4)
    bm = (m*m+5*m+7)/4
    gap = (21*m**3+24*m*m+36*m-112)/(4*(m+2)**2*(m*m+m+4))
    assert sy.cancel(hh.subs(z,2+8/m)-bm-gap) == 0
    symbolic = ["exact_signed_profit", "cost_parameterization", "scalar_crossing",
                "boundary_rank_one", "full_cost_derivative", "uniform_coefficients",
                "critical_displacement", "rational_lower_gap"]
    lower, upper, parity = [], [], []
    dims = list(range(64,81)) + [96,127,128,129,255,256,257,1024,4096]
    for mm in dims:
        zz, kk, pp, cc, hh0 = parameters(mm)
        bb = F(mm*mm+5*mm+7,4)
        nn = -(-bb.numerator//bb.denominator)
        for n, target in [(nn-1, lower),(nn, upper)]:
            ppur, rank, pbound, loss = purity(mm,n,kk,[pp],[])
            bulk = body(mm,n)
            assert (ppur > bulk) if n == nn-1 else (ppur < bulk)
            target.append({"m":mm,"n":n,"rank":rank,
                           "purity_minus_bulk":frac(ppur-bulk),
                           "integer_trace_loss":frac(loss)})
        h = nn*(mm*mm-1)
        bulk = body(mm,nn)
        closed = F(mm,h) if (mm-1)*nn%2 == 0 else F(mm*(h+2),(h+1)**2)
        assert bulk == closed
        parity.append({"m":mm,"fraction_B":frac(bb-bb.numerator//bb.denominator),
                       "body_formula_exact":True})
    patterns = []
    slots = [(i,i) for i in range(6)] + [(i,j) for i in range(6) for j in range(i+1,6)]
    for mm in [64,128,256]:
        zz, kk, pbase, cc, hh0 = parameters(mm)
        pp, pp2, beta = pbase-F(1,50),F(1,1000),F(1,2000)
        aa = 2+kk
        total = pp+pp2+beta
        for edge in [(0,2),(2,3)]:
            for negslot in slots:
                a = [[aa if i==j else F(0) for j in range(6)] for i in range(6)]
                for (i,j),weight in [((0,1),pp),(edge,pp2),(negslot,beta)]:
                    if i==j:
                        a[i][i] -= 2*weight
                    else:
                        a[i][j] -= weight
                        a[j][i] -= weight
                assert positive_definite(a)
                resolvent = sum(solve(a,[F(1)]*6),F(0))+F(mm-6)/aa
                assert kk*resolvent <= 1
                ka = resolvent-F(mm)/aa
                assert ka >= 2*pp/(aa*(aa-pp))+2*(pp2+beta)/aa**2
                assert cc >= kk*mm*mm*aa/(mm-1)*ka
                patterns.append({"m":mm,"positive_tail_edge":edge,
                                 "negative_slot":negslot,"rank_one_slack":frac(1-kk*resolvent)})
        nn = -(-(mm*mm+5*mm+7)//4)
        ppur, rank, _, _ = purity(mm,nn,kk,[pp,pp2],[beta])
        assert ppur < body(mm,nn)
    tiny = []
    for mm in [64,128,1024,10**8,10**20]:
        mmp = mp.mpf(mm)
        tp = 2/(mmp-1)
        bmp = (mmp*mmp-1)/(4*mmp**3)
        for pp in [mp.mpf("0.99"),mp.mpf(1),mp.mpf("1.01")]:
            ac = tp-2+pp-2*pp/(mmp-1)
            k0 = 2*tp*(2-pp)/(mp.sqrt(ac*ac+4*tp*(2-pp))-ac)
            c0 = mmp*mmp*(tp-k0)
            for tauexp in [2,12,60,120]:
                tau = mp.power(10,-tauexp)
                cc = c0+mp.mpf("2.5")*tau
                kk = tp-cc/mmp**2
                ceff = 2*kk*mmp*mmp*pp/((mmp-1)*(2+kk-pp))
                geff = 2*kk*mmp*mmp/((mmp-1)*(2+kk))
                assert cc >= ceff+geff*tau
                delta = mp.mpf("0.25")+mp.mpf("1.25")/mmp
                v0 = pp*pp+k0*pp-delta*(c0-bmp*c0*c0)
                vv = pp*pp+tau*tau/4+kk*(pp+tau)-delta*(cc-bmp*cc*cc)
                penalty = (v0-vv)/tau
                assert penalty > mp.mpf("0.25")
                tiny.append({"m":str(mm),"p":str(pp),"tau_exp":tauexp,
                             "profit_penalty_per_tau":mp.nstr(penalty,45)})
    pole, qsmall = F(32,676),F(3,64)
    assert pole > qsmall
    small_family = []
    for mm in [8,16]:
        zz,kk,pp,cc,hh0 = parameters(mm)
        nn=-(-(mm*mm+5*mm+7)//4)
        ppur,rank,_,_=purity(mm,nn,kk,[pp],[])
        small_family.append({"m":mm,"n":nn,"rank":rank,
                             "actual_profit":frac(ppur-body(mm,nn))})
    files={f:{"sha256":hashlib.sha256(Path(f).read_bytes()).hexdigest(),
              "lines":len(Path(f).read_text().splitlines())}
           for f in ["PAPER.md","THEOREM_MAP.md","check_onset.py"]}
    report={"status":"PASS_AUTHOR_FINITE_CONTROLS", "scope":"finite only; no Lean",
            "versions":{"sympy":sy.__version__,"mpmath":mp.__version__,"digits":mp.mp.dps},
            "files":files,"symbolic_groups":symbolic,"actual_single_head_lower":lower,
            "same_family_above_threshold_controls":upper,"parity_controls":parity,
            "all_finite_head_slot_patterns":patterns,"tiny_tail_relative_controls":tiny,
            "false_all_m_extension":{"m":3,"n":8,"pole":frac(pole),"bulk":frac(qsmall)},
            "small_family_results_retained":small_family}
    Path("author_checks.json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"status":report["status"],"symbolic_groups":len(symbolic),
                      "actual_lower":len(lower),"actual_upper_family":len(upper),
                      "all_slot_patterns":len(patterns),"tiny_tail":len(tiny),
                      "small_m_false_extension_rejected":True}))


if __name__ == "__main__":
    main()
