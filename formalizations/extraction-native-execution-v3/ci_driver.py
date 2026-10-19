"""Hosted producer for this new scope and prefix only."""
import argparse,os,subprocess
import common as c
import runtime,reproduce

def identity():
    workflow='.github/workflows/extraction-native-execution-v3.yml'
    if os.environ.get('GITHUB_REPOSITORY')!='mxym/math'or os.environ.get('GITHUB_WORKFLOW_SHA')!=os.environ.get('GITHUB_SHA')or not os.environ.get('GITHUB_WORKFLOW_REF','').startswith('mxym/math/'+workflow+'@refs/'):raise ValueError('Wrong actual independent workflow identity')
    reproduce.checkout(os.environ['GITHUB_SHA']);c.binding()

def main():
    p=argparse.ArgumentParser();p.add_argument('command',choices=['environment','bootstrap','run']);a=p.parse_args()
    rt=runtime.configure(True,False);identity();env=rt['env']
    if a.command=='environment':
        with open(os.environ['GITHUB_ENV'],'a')as f:
            for key in ['TMPDIR','XDG_CACHE_HOME','MATHLIB_CACHE_DIR','ELAN_HOME']:
                if '\n'in env[key]:raise ValueError('Unsafe runtime path')
                f.write(key+'='+env[key]+'\n')
            f.write('NATIVE_EXECUTION_V3_EVIDENCE='+str(rt['output'])+'\n')
        print('NATIVE_EXECUTION_EXCLUSIVE_CI_STORAGE_PASS');return
    if a.command=='bootstrap':
        policy=c.readj(c.ROOT/'CI_POLICY.json');installer=Path(env['TMPDIR'])/'elan-init.sh'
        subprocess.run(['curl','--fail','--location','--retry','3',policy['elan_init_url'],'--output',str(installer)],check=True,env=env)
        subprocess.run(['sh',str(installer),'-y','--no-modify-path','--default-toolchain','none'],cwd=c.ROOT,env=env,check=True)
        subprocess.run([env['ELAN_HOME']+'/bin/elan','toolchain','install','leanprover/lean4:v4.34.1'],cwd=c.ROOT,env=env,check=True)
        runtime.configure(True);subprocess.run(['lake','exe','cache','get'],cwd=c.ROOT,env=env,check=True)
        runtime.dependencies(rt);identity();print('NATIVE_EXECUTION_PINNED_CI_BOOTSTRAP_PASS');return
    subprocess.run(['python3','selftest.py'],cwd=c.ROOT,env=env,check=True)
    reproduce.run(True)

if __name__=='__main__':
    from pathlib import Path
    main()
