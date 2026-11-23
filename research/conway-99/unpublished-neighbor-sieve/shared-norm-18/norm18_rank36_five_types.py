"""Final all-neutral size-four comparison at rank36, original Sidon+native angular."""
from original_site_populations import calc
def check():
    o,w,c,g,u,ub,red=calc(36,[],export=True)
    B=2322466100694;T=72271791541192488
    z=B*2402*u[0,18]-T*o
    for k,v in {16:11124153418656168,127:32926411210284,337:556342217794956,
                228:782710109811936,125:15858760034304,230:139186992413592}.items():
        z+=v*u[divmod(k,100)]
    z-=1104785209930068*u[1,21]+2233765080348552*u[2,26]+579103247177532*w((4,44))
    z+=14291931641148*g((0,14))  # actual zero by the rank-36 Fano exclusion
    Y1=c((0,14));Y2=c((0,28))+2*c((3,39));M0=c((2,22))
    # Existing rank36_four_hit_sets.engine() row ('Ct',34)
    z-=1174436742318*(9*Y2+18*Y1-(369+10*34)*M0+(5*34**2-4158)*o)
    for k,v in [('mark((2, 36), -2)',8817165539140),('mark((3, 53), 1)',57357442842),
        ('mark((3, 53), -2)',134855243817),("nonneg('W', (-4, 44, 2))",2632688868036150),
        ("nonneg('W', (-3, 33, 0))",361524194141958),("nonneg('W', (-3, 35, 1))",1016557185864726),
        ("nonneg('C', (-4, 46, -1))",1072378728084510),("nonneg('C', (0, 14, -1))",24567186240730980)]:z-=v*ub[k]
    assert not any(red(z))
    assert 2*((T+2*B-1)//(2*B))==31120>30556>29842
    print('Rank 36: actual oriented N18 >=31120 vs <=29842; last size-four face excluded.')
if __name__=='__main__':check()
