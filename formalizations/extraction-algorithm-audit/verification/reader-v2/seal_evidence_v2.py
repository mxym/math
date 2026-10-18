#!/usr/bin/env python3
"""Seal complete local raw evidence; archive verification never extracts paths."""
from pathlib import Path
import argparse,gzip,hashlib,io,json,tarfile,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
import reproduce as a
from verify_local_v2 import verify

def verify_archive(path,manifest_sha256):
    with tarfile.open(path,'r:gz')as tf:
        members=tf.getmembers();names=[m.name for m in members]
        if len(names)!=len(set(names))or any(not m.isfile()or Path(m.name).is_absolute()or '..'in Path(m.name).parts for m in members):raise RuntimeError('Unsafe/duplicate archive entry')
        raw=tf.extractfile('EVIDENCE_HASHES.json').read()
        if hashlib.sha256(raw).hexdigest()!=manifest_sha256:raise RuntimeError('Evidence manifest digest mismatch')
        hashes=json.loads(raw)
        if set(names)!=set(hashes)|{'EVIDENCE_HASHES.json'}:raise RuntimeError('Missing/extra archive entries')
        for name,digest in hashes.items():
            if hashlib.sha256(tf.extractfile(name).read()).hexdigest()!=digest:raise RuntimeError('Archive byte mismatch '+name)
        return dict(status='EVERY_ARCHIVED_EVIDENCE_BYTE_VERIFIED',files=len(names),manifest_sha256=manifest_sha256,archive_sha256=a.sha(Path(path)))

def seal(directory):
    out=Path(directory).resolve();checked=verify(out)
    (out/'FINAL_LOCAL_REPORT.md').write_text('# Local independent algorithm audit\n\nPASS: fresh selected-package build, all selected Lean kinds/types/axioms, bounded syntax execution, the whole actual new-root dependency closure at trust0 and every strict same-type forged-proof control.\n\n'+json.dumps(checked,indent=2)+'\n\nThis result applies only to the exact bound source, model and manuscript inputs. The old518/175/84 completion root list is unchanged; imported declarations are replayed here only as dependencies of the new roots. Foundational axioms are limited to propext, Classical.choice and Quot.sound.\n\nThe scope establishes a concrete finite compiler with fixed-library offline data and correct numerical providers, actual word length/error/fidelity, arithmetic-expression counts and the stated integer/descriptor size budgets. It does not establish a uniform efficient offline-net algorithm, full recursive polynomial operand bound, provider/primitive/structural bit-cost implementation or whole-program polynomial Turing time. Small bytecode checks do not constitute a speed theorem. Hosted CI and its independently downloaded artifacts are separate evidence. Internal AI review is not external human peer review.\n')
    hashes={p.relative_to(out).as_posix():a.sha(p)for p in sorted(out.rglob('*'))if p.is_file()and p.name!='EVIDENCE_HASHES.json'}
    a.dump(out/'EVIDENCE_HASHES.json',hashes);digest=a.sha(out/'EVIDENCE_HASHES.json')
    archive=out.parent/(out.name+'-full-evidence.tar.gz')
    if archive.exists():raise RuntimeError('Refusing to overwrite sealed archive')
    with archive.open('wb')as raw:
        with gzip.GzipFile(fileobj=raw,mode='wb',mtime=0)as gz:
            with tarfile.open(fileobj=gz,mode='w')as tf:
                for p in sorted(out.rglob('*')):
                    if p.is_file():tf.add(p,arcname=p.relative_to(out).as_posix(),recursive=False)
    validation=verify_archive(archive,digest)
    record=dict(status='LOCAL_FULL_SCOPE_PASS_EVIDENCE_SEALED',mathematical_source_head=checked['source_head'],source_manifest_sha256=a.sha(a.ROOT/'SOURCE_HASHES.json'),summary_path='verification/'+out.name+'/SUMMARY.json',summary_sha256=checked['summary_sha256'],evidence_manifest_sha256=digest,archive=archive.name,archive_sha256=validation['archive_sha256'],archive_bytes=archive.stat().st_size,archived_files=validation['files'],trust0_log_sha256=a.sha(out/'trust0-replay.log'),kernel_declarations=checked['kernel_declarations'],theorems=checked['theorems'],model_definitions=checked['models'],same_type_controls=checked['controls'],hosted_CI_status='SEPARATE_NOT_CLAIMED_BY_LOCAL_SEAL')
    record['postrun_reader_revision']='verification/reader-v2/verify_local_v2.py'
    record['reader_execution_manifest_sha256']=a.sha(Path(__file__).resolve().parent/'EXECUTION_HASHES.json')
    record['frozen_reader_v1_empty_list_format_failure_preserved']=True
    a.dump(out.parent/'SEALED_LOCAL_EVIDENCE.json',record);return record

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('directory',nargs='?');ap.add_argument('--verify-archive');ap.add_argument('--manifest-sha');args=ap.parse_args()
    if args.verify_archive:
        if not args.manifest_sha:raise RuntimeError('Archive check needs expected evidence manifest digest')
        print(json.dumps(verify_archive(args.verify_archive,args.manifest_sha),indent=2))
    else:
        if not args.directory:raise RuntimeError('Missing raw evidence directory')
        print(json.dumps(seal(args.directory),indent=2))
