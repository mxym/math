"""Explicit D-backed local or exclusive hosted Linux runtime; 4000 MB Lean cap."""
from pathlib import Path
import os,platform,re,shutil,subprocess,sys
import common as c

def hosted_base():
    expected={'GITHUB_ACTIONS':'true','CI':'true','RUNNER_OS':'Linux','RUNNER_ARCH':'X64','RUNNER_ENVIRONMENT':'github-hosted'}
    if any(os.environ.get(k)!=v for k,v in expected.items())or sys.platform!='linux'or 'microsoft'in platform.release().lower():raise ValueError('Explicit hosted Linux context required')
    if Path(os.environ['GITHUB_WORKSPACE']).resolve()!=c.REPO.resolve()or not c.REPO.resolve().is_relative_to(Path('/home/runner/work')):raise ValueError('Wrong hosted checkout')
    tmp=Path(os.environ['RUNNER_TEMP'])
    if tmp.is_symlink()or tmp.resolve()!=Path('/home/runner/work/_temp'):raise ValueError('Wrong hosted temporary directory')
    for k,pat in [('GITHUB_SHA','[a-f0-9]{40}'),('GITHUB_RUN_ID','[0-9]+'),('GITHUB_RUN_ATTEMPT','[0-9]+')]:
        if not re.fullmatch(pat,os.environ.get(k,'')):raise ValueError('Invalid immutable CI identity')
    if c.git('rev-parse','HEAD').decode().strip()!=os.environ['GITHUB_SHA']:raise ValueError('Wrong event checkout')
    return tmp/('extraction-native-execution-v3-'+os.environ['GITHUB_RUN_ID']+'-'+os.environ['GITHUB_RUN_ATTEMPT'])

def configure(hosted=False,tools=True):
    env=dict(os.environ)
    for key in ['LEAN_PATH','LEAN_SRC_PATH','LEAN','LEAN_SYSROOT','LAKE_OVERRIDE_LEAN','LAKE_HOME','LAKE_CONFIG','LAKE_CACHE_KEY','LAKE_PKG_URL_MAP','LEAN_CC','LEAN_AR']:env.pop(key,None)
    env['LEAN_NUM_THREADS']='1';env['LAKE_NO_CACHE']='true';env['LAKE_ARTIFACT_CACHE']='false'
    if hosted:
        base=hosted_base();base.mkdir(parents=True,exist_ok=True)
        for key,sub in [('TMPDIR','tmp'),('XDG_CACHE_HOME','xdg'),('MATHLIB_CACHE_DIR','downloads'),('ELAN_HOME','elan')]:
            p=base/sub
            if p.is_symlink():raise ValueError('Symlinked runtime directory')
            p.mkdir(exist_ok=True);env[key]=str(p)
        env['PATH']=env['ELAN_HOME']+'/bin:'+env.get('PATH','')
        lock=base/'build.lock';out=base/'evidence';guard='GITHUB_HOSTED_LINUX_VERIFIED'
    else:
        sys.path.insert(0,'/mnt/d/math/tmp/extraction-full-lean-20261016')
        from ensure_d_storage import configure_env
        env=configure_env(env);env['LEAN_NUM_THREADS']='1'
        if not c.REPO.resolve().is_relative_to(Path('/mnt/lean-research-d/worktrees')):raise ValueError('Worktree outside verified D mount')
        env['PATH']='/mnt/lean-research-d/toolchains/elan-home/toolchains/leanprover--lean4---v4.34.1/bin:'+env.get('PATH','')
        lock=Path('/mnt/lean-research-d/tmp/extraction-shared-build.lock');out=c.ROOT/'verification';guard='D_BACKED_STORAGE_VERIFIED'
    mem=int(next(x.split()[1]for x in Path('/proc/meminfo').read_text().splitlines()if x.startswith('MemAvailable:')))//1024
    if mem<4500 or shutil.disk_usage(c.ROOT).free<2*1024**3:raise ValueError('Need 4500 MB available memory and 2 GiB D/hosted disk')
    actual={}
    if tools:
        for tool,want in c.readj(c.ROOT/'CI_POLICY.json')['binary_sha256'].items():
            found=subprocess.check_output([env['ELAN_HOME']+'/bin/elan','which',tool],cwd=c.ROOT,env=env,text=True).strip()if hosted else shutil.which(tool,path=env['PATH'])
            if not found:raise ValueError('Missing tool '+tool)
            p=Path(found).resolve()
            if c.sha(p)!=want or not p.is_relative_to(Path(env['ELAN_HOME']).resolve()if hosted else Path('/mnt/lean-research-d/toolchains')):raise ValueError('Wrong pinned executable '+tool)
            actual[tool]={'path':str(p),'sha256':want}
    sdk={}
    if tools:
        toolroot=Path(actual['lean']['path']).parent.parent
        for name,want in c.readj(c.ROOT/'SDK_INPUTS.json').items():
            if c.sha(toolroot/name)!=want:raise ValueError('Pinned native SDK input differs '+name)
            sdk[name]=want
    return {'env':env,'output':out,'lock':lock,'guard':guard,'memory_mb':4000,'actual_executables':actual,'sdk_inputs':sdk}

def dependencies(rt,provision=False):
    entries=c.readj(c.ROOT/'lake-manifest.json')['packages']
    if (c.ROOT/'lean-toolchain').read_text().strip()!='leanprover/lean4:v4.34.1'or [x.get('rev')for x in entries if x['name']=='mathlib']!=[c.PIN]:raise ValueError('Wrong source toolchain/Mathlib pin')
    if provision and rt['guard']=='D_BACKED_STORAGE_VERIFIED':
        shared=Path('/mnt/lean-research-d/cache/mathlib-d13f23b7-extended')
        for pkg in c.package_roots():
            dest=pkg/'.lake/packages';dest.mkdir(parents=True,exist_ok=True)
            for x in entries:
                if x['type']!='git':continue
                target=shared if x['name']=='mathlib'else shared/'.lake/packages'/x['name'];p=dest/x['name']
                if not p.exists():p.symlink_to(target,target_is_directory=True)
                if p.resolve()!=target.resolve():raise ValueError('Refusing active or different dependency link '+str(p))
    result={}
    for x in entries:
        if x['type']!='git':continue
        p=c.ROOT/'.lake/packages'/x['name']
        rev=subprocess.check_output(['git','-C',str(p),'rev-parse','HEAD'],text=True).strip()
        dirty=subprocess.check_output(['git','-C',str(p),'status','--porcelain=v1','--untracked-files=all'],text=True).strip()
        if rev!=x['rev']or dirty:raise ValueError('Dirty or wrong actual dependency '+x['name'])
        result[x['name']]={'rev':rev,'path':str(p.resolve())}
    sentinel=c.REPO/'formalizations/extraction-connections/STANDARD_CACHE.json'
    for n,want in c.readj(sentinel).items():
        p=c.ROOT/'.lake/packages/mathlib/.lake/build'/n
        if p.exists()and c.sha(p)!=want:raise ValueError('Nonstandard shared Mathlib artifact '+n)
    return result
