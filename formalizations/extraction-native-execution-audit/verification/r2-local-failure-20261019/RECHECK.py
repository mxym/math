"""Read-only preservation check for failed r2 run; never invokes Lean."""
from pathlib import Path
import argparse,sys
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT))
import common as c

def main():
    p=argparse.ArgumentParser();p.add_argument('--check-owned-cache',action='store_true');a=p.parse_args()
    c.binding()
    assert c.sha(ROOT/'SOURCE_HASHES.json')=='ab343fd0c5357ffa26a594a539ab006bf039d8b60eefb55e86b3b24e5711d569'
    assert c.sha(ROOT/'BINDING.json')=='63dafcb61adc865b35c061b0d16e7c6798e81f61c63ad5ac092ff07127d82d1d'
    actual={}
    for file in sorted(HERE.rglob('*')):
        if file.is_symlink():raise ValueError('Symlinked failed-run evidence')
        if file.is_file()and file!=HERE/'PARTIAL_EVIDENCE_HASHES.json':actual[file.relative_to(HERE).as_posix()]=c.sha(file)
    assert actual==c.readj(HERE/'PARTIAL_EVIDENCE_HASHES.json')
    report=c.readj(HERE/'REPORT.json');stages=c.readj(HERE/'STAGES.json')
    assert report['status']=='R2_FULL_FRESH_BUILD_PASS_TYPES_M4000_LIMIT_FAIL_NOT_KERNEL_VERIFICATION'
    assert [(r['stage'],r['exit_code'])for r in stages]==[('toolchain',0),('build',0),('types',134)]
    assert stages[-1]['command']==['lake','env','lean','-j1','-M4000','@EVIDENCE@/CheckInvocation.lean']
    for row in stages:assert row['sha256']==c.sha(c.path_at(HERE,row['log']))
    assert c.readj(HERE/'PRE_AUDIT.json')==c.readj(HERE/'POST_FAILURE_SNAPSHOT.json')
    assert 'Build completed successfully (4125 jobs).'in(HERE/'build.log').read_text()
    text=(HERE/'types.log').read_text()
    assert 'lean::memory_exception'in text and 'interpreter'in text and 'DECLARATION_KIND_CHECK_PASS'not in text
    assert report['model_exports']==0 and report['positive_kernel_started']is False and report['strict_controls_started']is False
    assert report['automatic_memory_increase']is False
    owned=c.readj(HERE/'OWNED_OLEANS.json');assert set(owned)==c.expected_owned_outputs()and len(owned)==430
    if a.check_owned_cache:
        original_repo=Path(report['original_run_directory']).parents[3]
        assert original_repo.is_relative_to(Path('/mnt/lean-research-d/worktrees'))
        for name,want in owned.items():assert c.sha(c.path_at(original_repo,name))==want
    print({'status':'FAILED_R2_RUN_PRESERVATION_PASS_NOT_KERNEL_VERIFICATION','full_fresh_build':'PASS','types':'M4000_MEMORY_LIMIT_FAIL','positive_kernel_run':False,'owned_modules':430,'owned_cache_bytes_checked':a.check_owned_cache,'source_inputs':531})

if __name__=='__main__':main()
