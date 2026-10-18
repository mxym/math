"""D-guarded local runtime; explicit fail-closed hosted-GitHub-only alternative."""
from pathlib import Path
import hashlib,json,os,platform,re,shutil,subprocess,sys
ROOT=Path(__file__).resolve().parent
REPO=ROOT.parent.parent

def digest(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def hosted_context():
    required={'GITHUB_ACTIONS':'true','CI':'true','RUNNER_OS':'Linux','RUNNER_ARCH':'X64','RUNNER_ENVIRONMENT':'github-hosted'}
    if any(os.environ.get(k)!=v for k,v in required.items()):raise RuntimeError('GitHub CI mode requires the explicit hosted Linux/X64 runner context')
    if sys.platform!='linux' or 'microsoft' in platform.release().lower() or Path('/proc/sys/fs/binfmt_misc/WSLInterop').exists():
        raise RuntimeError('GitHub CI mode is forbidden on local Windows/WSL')
    workspace=Path(os.environ['GITHUB_WORKSPACE']);temporary=Path(os.environ['RUNNER_TEMP'])
    if workspace.resolve()!=REPO.resolve() or not workspace.resolve().is_relative_to(Path('/home/runner/work')):
        raise RuntimeError('Unexpected hosted workspace')
    if temporary.is_symlink() or temporary.resolve()!=Path('/home/runner/work/_temp'):
        raise RuntimeError('Unexpected hosted runner temporary directory')
    for key in ['GITHUB_SHA','GITHUB_RUN_ID','GITHUB_RUN_ATTEMPT']:
        if not re.fullmatch(r'[a-f0-9]{40}' if key=='GITHUB_SHA' else r'[0-9]+',os.environ.get(key,'')):
            raise RuntimeError('Missing/invalid GitHub immutable run context '+key)
    head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=REPO,text=True).strip()
    if head!=os.environ['GITHUB_SHA']:raise RuntimeError('Checkout is not the exact event SHA')
    base=temporary/('extraction-raw-resource-'+os.environ['GITHUB_RUN_ID']+'-'+os.environ['GITHUB_RUN_ATTEMPT'])
    if base.is_symlink() or not base.resolve().is_relative_to(temporary.resolve()):raise RuntimeError('Unsafe CI output root')
    return base

def configure(github_actions=False):
    env=dict(os.environ)
    if not github_actions:
        sys.path.insert(0,'/mnt/d/math/tmp/extraction-full-lean-20261016')
        from ensure_d_storage import configure_env
        env=configure_env(env)
        env['PATH']='/root/.elan/toolchains/leanprover--lean4---v4.34.1/bin:'+env.get('PATH','')
        policy=json.loads((ROOT/'CI_EXECUTION_POLICY.json').read_text());executables={}
        for tool,expected in policy['binary_sha256'].items():
            found=shutil.which(tool,path=env['PATH'])
            if not found:raise RuntimeError('Missing actual local executable '+tool)
            actual=Path(found).resolve()
            if not actual.is_relative_to(Path('/mnt/lean-research-d/toolchains'))or digest(actual)!=expected:raise RuntimeError('Actual local executable is not the checked D-backed binary '+tool)
            executables[tool]=dict(path=str(actual),sha256=expected)
        available=int(next(l.split()[1]for l in Path('/proc/meminfo').read_text().splitlines()if l.startswith('MemAvailable:')))//1024
        disk_free=shutil.disk_usage(ROOT).free
        if available<7000:raise RuntimeError('Less than 7GB available for the added proof closure')
        if disk_free<3*1024**3:raise RuntimeError('Less than 3GiB free on verified D backing')
        return dict(env=env,lock=Path('/mnt/lean-research-d/tmp/extraction-shared-build.lock'),output=ROOT/'verification',memory_mb=min(11000,available-1024),guard='D_BACKED_STORAGE_VERIFIED',available_memory_mb=available,available_disk_bytes=disk_free,actual_executables=executables)
    base=hosted_context();base.mkdir(parents=True,exist_ok=True)
    for key,sub in [('TMPDIR','tmp'),('MATHLIB_CACHE_DIR','mathlib-downloads'),('XDG_CACHE_HOME','xdg'),('ELAN_HOME','elan')]:
        p=base/sub
        if p.is_symlink():raise RuntimeError('Symlinked CI runtime directory')
        p.mkdir(exist_ok=True);env[key]=str(p)
    env['PATH']=env['ELAN_HOME']+'/bin:'+env.get('PATH','')
    available=int(next(l.split()[1] for l in Path('/proc/meminfo').read_text().splitlines() if l.startswith('MemAvailable:')))//1024
    memory=min(11000,available-1024)
    if memory<5000:raise RuntimeError('Less than 5GB available for the selected kernel closure')
    disk_free=shutil.disk_usage(base).free
    if disk_free<3*1024**3:raise RuntimeError('Less than 3GiB free for fresh selected-package outputs/evidence')
    return dict(env=env,lock=base/'build.lock',output=base/'evidence',memory_mb=memory,guard='GITHUB_HOSTED_LINUX_RUNNER_VERIFIED',available_memory_mb=available,available_disk_bytes=disk_free)

def check_ci_binaries():
    runtime=configure(True);policy=json.loads((ROOT/'CI_EXECUTION_POLICY.json').read_text());records={}
    for tool,expected in policy['binary_sha256'].items():
        actual=Path(subprocess.check_output(['elan','which',tool],cwd=ROOT,env=runtime['env'],text=True).strip()).resolve()
        if not actual.is_relative_to(Path(runtime['env']['ELAN_HOME']).resolve()):raise RuntimeError('Toolchain outside exclusive runner directory')
        value=digest(actual)
        if value!=expected:raise RuntimeError('Unexpected official Linux toolchain binary '+tool)
        records[tool]=dict(path=str(actual),sha256=value)
    return records
