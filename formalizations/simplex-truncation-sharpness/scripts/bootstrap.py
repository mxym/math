#!/usr/bin/env python3
"""Run the frozen official bootstrap in a disposable copy, then independent replay.
Network/downloads are performed only by the preserved project/bootstrap script.
The sealed public tree is not used for cache, log or owned output storage.
"""
import argparse,os,shutil,subprocess,sys
from pathlib import Path
sys.dont_write_bytecode=True
from release_integrity import validated_snapshot,require,ReleaseIntegrityError
ROOT=Path(__file__).resolve().parents[1]
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--work',required=True,type=Path);ap.add_argument('--lean-bin',type=Path);a=ap.parse_args()
 snap=validated_snapshot(ROOT);require(not a.work.is_symlink(),'work must not be a symlink');work=a.work.resolve();require(not work.exists() and not work.is_relative_to(ROOT),'choose a fresh work directory outside release')
 work.mkdir(parents=True);project=work/'project';project.mkdir()
 for n,data in snap.items():
  if n.startswith('project/'):
   p=project/n[len('project/'):];p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
 env=os.environ.copy()
 if a.lean_bin:env['ENTRY005_LEAN_BIN']=str(a.lean_bin.resolve())
 subprocess.run(['bash',str(project/'scripts/bootstrap.sh')],check=True,env=env)
 lean=Path(env['ENTRY005_LEAN_BIN']).resolve() if env.get('ENTRY005_LEAN_BIN') else project/'.toolchain/lean-4.34.1-linux/bin'
 subprocess.run([sys.executable,'-B',str(ROOT/'scripts/verify.py'),'--lean-bin',str(lean),'--dependency-project',str(project/'formal'),'--output',str(work/'independent-replay')],check=True,env=env)
 require(validated_snapshot(ROOT)==snap,'release changed during bootstrap');print('SHARPNESS_BOOTSTRAP_AND_REPLAY_PASS')
if __name__=='__main__':
 try:main()
 except (ReleaseIntegrityError,OSError,subprocess.CalledProcessError) as e:print(str(e),file=sys.stderr);sys.exit(1)
