"""Same-graph N18 > 54,476, on a rank-36 seven-type face."""
from original_site_populations import calc

def check():
    o,w,c,g,u,ub,red=calc(36,[],export=True);B=19304874;L=16856484174
    z=2402*B*u[0,18]-(54476*B+L)*o
    for k,v in {26:2527086552,121:17127069474,16:5296496472,337:4024298790,
                230:5573437464}.items():z+=v*u[divmod(k,100)]
    for k,v in {22:8567861940,24:1497212238,226:3877173888,228:12540234294,
                333:900058224,335:3842556264}.items():z-=v*w(divmod(k,100))
    z-=563588466*(w((1,23))-99*o-7*w((0,14)))+6685098*g((0,14))+25013152206*c((0,14))
    for k,v in [('compat(-1, 23, -1)',41679568854),('mark((2, 36), -2)',57672020),
                ("nonneg('C', (-4, 46, -1))",4853100483),
                ("nonneg('C', (-4, 46, 1))",285476499)]:z-=v*ub[k]
    assert not any(red(z))
    print('Required N18 on seven-type face >=',54476+2*((L+2*B-1)//(2*B)))
if __name__=='__main__':check()
