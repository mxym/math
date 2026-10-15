from pathlib import Path
import subprocess,json
root=Path('/home/mxym/math-appt-multiscale-20261013');stage=Path(__file__).resolve().parent
receipt=json.loads((stage/'PUSH_RECEIPT.json').read_text())
def git(*a):return subprocess.check_output(['git','-C',str(root),*a])
head=git('rev-parse','HEAD').decode().strip();old=git('rev-parse','origin/main').decode().strip()
if head!=receipt['source_commit'] or old!=receipt['previous_main'] or git('status','--porcelain').strip():raise RuntimeError('Root/ref state changed')
subprocess.run(['git','-C',str(root),'merge-base','--is-ancestor',old,head],check=True)
subprocess.run(['git','-C',str(root),'update-ref','refs/remotes/origin/main',head,old],check=True)
print(json.dumps({'root':head,'origin_main':git('rev-parse','origin/main').decode().strip(),'clean':True}))
