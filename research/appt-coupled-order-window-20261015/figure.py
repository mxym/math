"""Illustrate K's limiting affine law, not exact finite-dimensional phases."""
from pathlib import Path
import json,hashlib
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.colors import ListedColormap

here=Path(__file__).resolve().parent
source=here/'control-runs'/'20261015T073120.266026Z'/'RESULT.json'
constants=json.loads(source.read_text())['groups']['transition_constants']
alpha=float(constants['alpha0']);z={s:float(x) for s,x in constants['z'].items()}
A={s:float(x) for s,x in constants['A'].items()}
slopes={s:float(x) for s,x in constants['slopes'].items()}
uc=float(constants['frontier_u_crossing']);ac=float(constants['frontier_a_crossing'])
u=np.linspace(-4,10,600);a=np.linspace(-.5,2,400);U,Y=np.meshgrid(u,a)
lp=alpha*z['+']*(A['+']+slopes['+']*U-Y)
lm=alpha*z['-']*(A['-']+slopes['-']*U-Y)
region=np.argmax(np.stack([np.zeros_like(U),lp,lm]),axis=0)
colors=['#e8ebef','#6da8d5','#efb16e']
fig,(left,right)=plt.subplots(1,2,figsize=(11.6,4.4),constrained_layout=True)
left.pcolormesh(u,a,region,cmap=ListedColormap(colors),vmin=-.5,vmax=2.5,shading='auto',rasterized=True)
frontier=np.maximum(A['+']+slopes['+']*u,A['-']+slopes['-']*u)
left.plot(u,frontier,color='#30343b',linewidth=1.6)
left.contour(U,Y,lp-lm,levels=[0],colors=['#666a70'],linestyles='--',linewidths=1)
left.plot([uc],[ac],'o',color='#30343b',markersize=4)
left.annotate('frontier intersection',xy=(uc,ac),xytext=(-.5,1.45),
              arrowprops={'arrowstyle':'->','color':'#30343b'},fontsize=9)
left.text(-3,1.75,'bulk',fontsize=11)
left.text(-3,-.15,'negative anomaly',fontsize=10)
left.text(7.6,.25,'positive anomaly',fontsize=9.5,ha='center')
left.set(xlim=(-4,10),ylim=(-.5,2),xlabel=r'order displacement $u=m(\alpha-\alpha_0)$',
         ylabel=r'dimension displacement $a=(n-d_0m^2)/m$',title='Limiting maximizing family')
slice_a=1.05
P=alpha*z['+']*(A['+']+slopes['+']*u-slice_a)
M=alpha*z['-']*(A['-']+slopes['-']*u-slice_a)
right.plot(u,P,color='#397cae',linestyle='--',label='positive branch')
right.plot(u,M,color='#ba742c',linestyle='--',label='negative branch')
right.axhline(0,color='#9ca3ad',linewidth=1,label='bulk')
right.plot(u,np.maximum.reduce([np.zeros_like(u),P,M]),color='#20242a',linewidth=2.2,label='actual limiting maximum')
right.set(xlim=(-4,10),xlabel=r'order displacement $u$',
          ylabel=r'limiting $mD(E_\alpha-G_\alpha)$',title=r'Entropy correction at $a=1.05$')
right.grid(alpha=.16);right.legend(frameon=False,fontsize=8,loc='upper center')
fig.suptitle('Coupled APPT order/dimension transition',fontsize=13)
fig.text(.5,-.025,'Numerical constants illustrate the proved limiting law; finite-dimensional tie zones require the exact formula.',
         ha='center',fontsize=8,color='#555b64')
dest=here/'figures';dest.mkdir(exist_ok=True)
fig.savefig(dest/'coupled-transition.png',dpi=180,bbox_inches='tight')
fig.savefig(dest/'coupled-transition.svg',bbox_inches='tight')
(dest/'PROVENANCE.json').write_text(json.dumps({'source_control':str(source.relative_to(here)),
 'source_control_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
 'constants':constants,'scope':'limiting-law numerical illustration; not an exact finite-phase or rigorous-interval certificate',
 'files':{n:hashlib.sha256((dest/n).read_bytes()).hexdigest() for n in ['coupled-transition.png','coupled-transition.svg']}},indent=2)+'\n')
print(json.dumps({'figure':str(dest/'coupled-transition.png'),'scope':'limiting law illustration only'}))
