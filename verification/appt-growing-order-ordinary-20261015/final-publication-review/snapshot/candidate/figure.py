"""Plot P2's proved limiting law; no finite-dimensional maximizer data."""
from pathlib import Path
import hashlib,json
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

here=Path(__file__).resolve().parent
c=np.linspace(.08,6,900)
head=np.log(3)-1/c
fig,ax=plt.subplots(figsize=(8.2,4.5),constrained_layout=True)
for m,color in [(2,'#397cae'),(3,'#c17b32'),(5,'#4f9870')]:
    bulk=np.log((m+1)/(m-1))
    ax.plot(c,np.maximum(bulk,head),color=color,linewidth=2,label=f'fixed m = {m}')
ax.plot(c,np.maximum(0,head),color='#25282d',linewidth=2.3,label=r'$m\to\infty$')
ax.set(xlim=(0,6),ylim=(-.035,1.17),xlabel=r'logarithmic order ratio $c=\alpha/\log D$',
       ylabel=r'limiting actual entropy deficit $E_\alpha$',
       title='Growing-order APPT entropy across local dimensions')
ax.grid(alpha=.16)
ax.legend(frameon=False,loc='lower right')
ax.annotate('common head branch',xy=(4.5,np.log(3)-1/4.5),xytext=(3.2,.57),
            arrowprops={'arrowstyle':'->','color':'#555b64'},fontsize=9)
fig.text(.5,-.025,r'Limit requires $D\to\infty$ and $\alpha\to\infty$; curves are not exact finite-dimensional extrema.',
         ha='center',fontsize=8,color='#555b64')
dest=here/'figures';dest.mkdir(exist_ok=True)
path=dest/'growing-order-transition.png'
fig.savefig(path,dpi=180,bbox_inches='tight')
(dest/'PROVENANCE.json').write_text(json.dumps({'formula':'max(log((m+1)/(m-1)),log(3)-1/c); joint m->infinity replaces bulk by zero',
  'parameters':{'c_min':.08,'c_max':6,'samples':900,'fixed_m':[2,3,5]},
  'scope':'illustration of proved growing-total-dimension/growing-order limit, not a finite quantum optimization certificate',
  'files':{path.name:hashlib.sha256(path.read_bytes()).hexdigest()}},indent=2)+'\n')
print(json.dumps({'figure':str(path),'scope':'limiting formula only'}))
