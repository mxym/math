#!/usr/bin/env python3
"""Runtime-artifact bindings and deterministic output seal; not a proof checker.
An externally authenticated manifest digest is needed against coordinated rewrites.
"""
from pathlib import Path
import hashlib,json,os,stat
from release_integrity import require,json_value,canonical_path,DIGEST
SUFFIXES=('.olean','.olean.private','.olean.server','.ilean','.ir','.ir.sig')
MANIFEST='OUTPUT_MANIFEST.json'
TERMINAL_RECORDS={'RUNS.json','BUILD_LEDGER.json','HELPER_LEDGER.json','SELECTED_OFFICIAL.json','FINAL_VERIFICATION.json','RUNTIME_INPUTS.json','RESULT_BINDINGS.json','PREFLIGHT.json','BUILD_PASS.json','checks/stock-standard-axioms.json','checks/literal-standard-axioms.json','checks/combined-owned-inventory.json','checks/combined-owned-closure.json','checks/literal-main-empty-kernel.json','checks/literal-main-empty-kernel.json.closure.json'}
def release_identity(release):
    return {n:sha(Path(release)/n) for n in ['SOURCE_MANIFEST.json','SHA256SUMS']}


def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def load(path):return json_value(path.read_bytes(),str(path))
def artifact_hashes(output):
    result={}
    for suffix in SUFFIXES:
        p=output.with_suffix(suffix)
        if p.exists() or p.is_symlink():
            require(p.is_file() and not p.is_symlink(),'fresh artifact must be a regular file: '+str(p))
            result[suffix]=sha(p)
    require('.olean' in result,'fresh main olean missing: '+str(output))
    return result

def relative_file(root,name):
    canonical_path(name);p=root/name
    require(p.is_file() and not p.is_symlink(),'run record needs regular file: '+name)
    require(all(not q.is_symlink() for q in p.parents if q.is_relative_to(root)),'run record has linked parent: '+name)
    return p

def verify_bindings(root,release):
    """Check stored source/output/log references, without certifying execution truth."""
    root=Path(root);release=Path(release)
    builds=load(relative_file(root,'BUILD_LEDGER.json'));helpers=load(relative_file(root,'HELPER_LEDGER.json'));runs=load(relative_file(root,'RUNS.json'))
    require(type(builds) is dict and type(helpers) is dict and type(runs) is list,'invalid output ledger schemas')
    for label,ledger in [('build',builds),('helper',helpers)]:
        for n,row in ledger.items():
            require(type(row) is dict and type(row.get('artifacts')) is dict,'missing '+label+' artifact map: '+n)
            out=relative_file(root,row['output']);require(out.suffix=='.olean','output must name main olean')
            require(artifact_hashes(out)==row['artifacts'],'fresh artifact or sidecar differs: '+n)
            require(row.get('output_sha256')==row['artifacts'].get('.olean'),'main artifact digest linkage differs: '+n)
            if label=='helper':
                require(n in {'AuditCore','EmptyKernelReplay','StockAxiomSnapshot'},'unknown audit helper')
                require(row['source_sha256']==sha(release/'audit/checks'/(n+'.lean')),'audit helper source differs: '+n)
    require(set(helpers)=={'AuditCore','EmptyKernelReplay','StockAxiomSnapshot'},'audit helper ledger incomplete')
    seen=set()
    for row in runs:
        require(type(row) is dict and row.get('log') not in seen,'duplicate/malformed run log record')
        seen.add(row['log']);p=relative_file(root,row['log']);require(sha(p)==row['log_sha256'],'run log digest differs: '+row['log'])
    for ledger in [builds,helpers]:
        for n,row in ledger.items():
            matches=[r for r in runs if r.get('log')==row.get('log')]
            require(len(matches)==1 and matches[0]['exit_code']==0 and matches[0]['log_sha256']==row['log_sha256'],'build/helper run linkage differs: '+n)
    selected=load(relative_file(root,'SELECTED_OFFICIAL.json'))
    require(type(selected) is dict,'official selection schema differs')
    for n,row in selected.items():
        rel=Path(n.replace('.','/'))
        for suffix,h in row['artifacts'].items():
            require(suffix in SUFFIXES,'unknown official artifact suffix')
            p=root/'official'/rel.with_suffix(suffix);target=Path(row['root'])/rel.with_suffix(suffix)
            require(p.is_symlink() and p.resolve()==target.resolve() and p.is_file() and sha(p)==h,'selected official binding differs: '+n+suffix)
    result_bindings=load(relative_file(root,'RESULT_BINDINGS.json'))
    require(type(result_bindings) is dict,'result binding schema differs')
    expected_results={n for n in TERMINAL_RECORDS if n.startswith('checks/')}
    require(expected_results<=set(result_bindings),'terminal mathematical result binding incomplete')
    for name,h in result_bindings.items():require(sha(relative_file(root,name))==h,'stored result/closure changed: '+name)
    return {'built_modules':len(builds),'audit_helpers':len(helpers),'run_logs':len(runs),'official_cached_modules':len(selected)}

def snapshot(root):
    root=Path(root);require(root.is_dir() and not root.is_symlink(),'output root must be regular directory');result={}
    def walk(directory):
        for p in sorted(directory.iterdir()):
            name=canonical_path(p.relative_to(root).as_posix())
            if name==MANIFEST:continue
            mode=p.lstat().st_mode
            if stat.S_ISDIR(mode):walk(p)
            elif stat.S_ISREG(mode):result[name]={'kind':'file','size':p.stat().st_size,'sha256':sha(p)}
            elif stat.S_ISLNK(mode):
                require(name.startswith('official/') and p.is_file(),'only file-level official cache links permitted')
                result[name]={'kind':'official_cache_link','target':os.readlink(p),'size':p.stat().st_size,'sha256':sha(p)}
            else:require(False,'nonregular run artifact: '+name)
    walk(root);return dict(sorted(result.items()))

def seal_outputs(root,release):
    root=Path(root);p=root/MANIFEST;require(not p.exists() and not p.is_symlink(),'refusing to reseal outputs')
    bindings=verify_bindings(root,release);files=snapshot(root)
    result={'format':1,'scope':'Run artifact integrity and recorded bindings only; this manifest is not a new proof check or execution attestation','release_identity':release_identity(release),'binding_counts':bindings,'files':files}
    with p.open('x') as f:json.dump(result,f,indent=2);f.write('\n')
    verify_outputs(root,release)
    return sha(p)

def verify_outputs(root,release,expected_sha256=None):
    root=Path(root);p=relative_file(root,MANIFEST)
    if expected_sha256 is not None:require(DIGEST.fullmatch(expected_sha256) is not None and sha(p)==expected_sha256,'externally supplied output manifest hash differs')
    record=load(p);require(type(record) is dict and set(record)=={'format','scope','release_identity','binding_counts','files'} and type(record['format']) is int and record['format']==1,'output manifest schema differs')
    require(record['release_identity']==release_identity(release),'run was sealed against a different release')
    require(record['files']==snapshot(root),'output file inventory, content, or linked cache changed')
    require(record['binding_counts']==verify_bindings(root,release),'output binding counts differ')
    require(TERMINAL_RECORDS<=set(record['files']),'required terminal output records missing')
    return {'status':'RUN_OUTPUT_INTEGRITY_PASS','manifest_sha256':sha(p),'files':len(record['files']),'binding_counts':record['binding_counts'],'proof_rechecked':False}
