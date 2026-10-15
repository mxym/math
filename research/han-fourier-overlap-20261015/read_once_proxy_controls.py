"""Exact integer controls for the all-coordinate proxy obstruction.

No transcendental global bound is inferred. Independent physical edge counts
and integer Fourier numerators verify influences and proxy ratios at depth <=4.
"""
import datetime, fractions, json, pathlib
import numpy as np
from adaptive_split_probe import fwht_rows, metrics

F=fractions.Fraction

def gate(g,h,kind):
    return (g+h+g*h-1)//2 if kind=='AND' else (g+h-g*h+1)//2

def main():
    folder=pathlib.Path(__file__).parent
    row=np.array([1,-1],dtype=np.int64)
    p=F(1,2); cumulative=F(0); alpha=F(1); out=[]; gates=[]
    for depth in range(5):
        n=1<<depth; N=1<<n; mu=2*p-1
        R=2*cumulative+4*abs(mu)
        w=fwht_rows(row)
        assert sum(int(x)**2 for x in w)==N*N
        assert F(int(row.sum()),N)==mu
        fullmetrics=metrics(row[None,:],n)
        for i in range(n):
            lo=np.array([s for s in range(N) if not(s>>i&1)])
            a=w[lo]; b=w[lo|(1<<i)]
            inf_num=sum(int(x)**2 for x in b)
            L_num=4*sum(abs(int(x)*int(y)) for x,y in zip(a,b))
            physical_num=int(np.count_nonzero(row!=row[np.arange(N)^(1<<i)]))
            assert F(inf_num,N*N)==F(physical_num,N)==alpha
            assert F(L_num,inf_num)==R
        assert R>=F(3*depth,2)
        out.append({'depth':depth,'input_bits':n,'complete_truth_table_entries':N,'all_coordinates_checked':n,'gates_bottom_to_top':gates.copy(),'mean':str(mu),'per_coordinate_influence':str(alpha),'per_coordinate_L1_over_I':str(R),'Q_over_I_float':float(fullmetrics['Q'][0,0]/float(alpha)),'Delta_over_I_float':float(fullmetrics['Delta'][0,0]/float(alpha)),'H_over_I_float':float(fullmetrics['H'][0]/(n*float(alpha)))})
        cumulative+=1-mu*mu
        kind='OR' if p<=F(1,2) else 'AND'; gates.append(kind)
        beta=(1-p) if kind=='OR' else p
        alpha*=beta
        p=2*p-p*p if kind=='OR' else p*p
        if depth<4:
            row=gate(row[:,None],row[None,:],kind).reshape(-1)
    result={'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Exact all-coordinate integer Walsh/physical-edge checks for one explicitly defined formula at each depth 0..4; not all functions. Entropies are floating controls only.','results':out}
    (folder/'READ_ONCE_PROXY_CONTROLS.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    for r in out: print(r)

if __name__=='__main__': main()
