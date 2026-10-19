"""Read-only source/log analysis. No Lean, build, or author-cache access."""
from pathlib import Path
import hashlib, json, re

ROOT = Path(__file__).resolve().parent
MANIFEST = json.loads((ROOT / 'GIT_SNAPSHOT_MANIFEST.json').read_text())
ALLOW = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def dump(name, obj):
    (ROOT / name).write_text(json.dumps(obj, indent=2, sort_keys=True) + '\n')


def source(key, path):
    return ROOT / MANIFEST[key]['files'][path]['snapshot']


def axioms(text):
    result = {}
    pattern = r"'([^']+)'\s+(?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])"
    for match in re.finditer(pattern, text):
        name = match[1]
        if name in result:
            raise ValueError('Duplicate axiom observation: ' + name)
        values = [] if match[2] is None else [x.strip() for x in match[2].split(',') if x.strip()]
        if len(values) != len(set(values)) or set(values) - ALLOW:
            raise ValueError('Unexpected axiom observation: ' + name)
        result[name] = values
    return result


def main():
    machine = 'formalizations/extraction-rational-gate-machine/'
    numeric = 'formalizations/extraction-numerical-synthesis/'
    reviewed = {
        'fifths': [machine + 'RationalGateMachine/' + n + '.lean' for n in
                   ['StateLift', 'BinaryFifths', 'BinaryClock', 'Fifths', 'BinaryFifthsCheck']] +
                  ['formalizations/extraction-rational-gate-provider/RationalGateProvider/' + n + '.lean'
                   for n in ['Fifths', 'SignedFifths']],
        'query': [numeric + 'CircuitNumerical/' + n + '.lean' for n in [
            'NativeQueryReaderEmbedding', 'NativeQueryParserEmbedding', 'NativeQueryController',
            'NativeQueryClearRuns', 'NativeQueryRuns', 'NativeQuerySemantics', 'NativeQueryReuse',
            'NativeQueryCheck', 'PacketFieldParser', 'PacketFieldRoundtrip', 'PacketFraming',
            'TM2Subroutine', 'TM2SubroutineSplice', 'TM2ConfigurationMap', 'TM2ExtraStack',
            'PacketMasterEmbedding', 'PacketMasterClone', 'PacketMasterReader',
            'PacketQuerySetup', 'PacketQueryRuns', 'PacketRecordController', 'PacketRecordRuns',
            'PacketQuerySemantics', 'PacketRecordSemantics', 'PacketMasterSemantics',
            'BinaryIndexedLookup', 'FiniteBinaryCounter', 'FiniteBinaryCounterTerminal',
            'PacketCounterOperational']]
    }
    dump('ACTUALLY_READ_SOURCE_FILES.json', {
        key: {'commit': MANIFEST[key]['commit'], 'files': {n: MANIFEST[key]['files'][n]
              for n in names},
              'scope': 'Full listed files read. Other snapshotted dependencies are byte-bound archival context, not all independently source-reviewed.'}
        for key, names in reviewed.items()
    })
    plans = {
        'fifths': (machine, 'BINARY_FIFTHS_ROOTS.txt', 'BINARY_FIFTHS_MODELS.txt',
                   'RationalGateMachine/BinaryFifthsCheck.lean',
                   '20261019T000758259036Z-root-owned-RationalGateMachine.BinaryFifthsCheck.log',
                   machine + 'verification/binary-input-fifths-standard-reader-v2-20261019/REPORT.json', 26, 11),
        'query': (numeric, 'NATIVE_QUERY_ROOTS.txt', 'NATIVE_QUERY_MODELS.txt',
                  'CircuitNumerical/NativeQueryCheck.lean',
                  '20261019T002525789091Z-owned-check-CircuitNumerical.NativeQueryCheck.log',
                  numeric + 'verification/native-query-aggregate-20261019/REPORT.json', 58, 40)
    }
    findings = {}
    for key, (base, rootfile, modelfile, checkfile, logfile, reportfile, nr, nm) in plans.items():
        roots = source(key, base + rootfile).read_text().splitlines()
        models = source(key, base + modelfile).read_text().splitlines()
        if len(roots) != nr or len(models) != nm or len(set(roots + models)) != nr + nm:
            raise ValueError('Wrong declared roots/models')
        check = source(key, base + checkfile).read_text()
        checked_names = re.findall(r'^#check\s+(\S+)', check, re.M)
        if checked_names != roots + models:
            raise ValueError('Check order differs from declared roots/models')
        log = (ROOT / 'logs' / logfile).read_text()
        actual_axioms = axioms(log)
        wanted_axioms = roots + models if key == 'fifths' else roots
        if set(actual_axioms) != set(wanted_axioms):
            raise ValueError('Missing/extra actual axiom observations')
        author = json.loads(source(key, reportfile).read_text())
        if actual_axioms != author['axioms' if key == 'fifths' else 'root_axioms']:
            raise ValueError('Actual multiline/empty axiom observations differ from report')
        declarations = {}
        for path in reviewed[key]:
            text = source(key, path).read_text()
            namespace = re.search(r'^namespace\s+(\S+)', text, re.M)
            if namespace is None:
                continue
            for match in re.finditer(r'^(?:noncomputable\s+)?(theorem|def|abbrev|inductive|structure)\s+([\w.\']+)', text, re.M):
                name = namespace[1] + '.' + match[2]
                if name in roots + models:
                    if name in declarations:
                        raise ValueError('Ambiguous declaration source')
                    headers = list(re.finditer(r'^' + re.escape(name) + r'(?=\.\{|\s|:)', log, re.M))
                    if len(headers) != 1:
                        raise ValueError('Missing/duplicate actual type header: ' + name)
                    declarations[name] = {
                        'source_kind': match[1], 'path': path,
                        'source_sha256': MANIFEST[key]['files'][path]['sha256'],
                        'line': text.count('\n', 0, match.start()) + 1,
                        'actual_type_header_observed': True,
                        'kind_checked_in_author_environment': key == 'fifths',
                        'model_core_expr_dump': False,
                    }
        if set(declarations) != set(roots + models):
            raise ValueError('Missing source declarations: ' + str(set(roots + models) - set(declarations)))
        if any(declarations[n]['source_kind'] != 'theorem' for n in roots):
            raise ValueError('Source theorem kind mismatch')
        if any(declarations[n]['source_kind'] not in {'def', 'abbrev', 'inductive', 'structure'} for n in models):
            raise ValueError('Source model kind mismatch')
        if key == 'fifths':
            loops = re.findall(r'for name in \[(.*?)\] do', check, re.S)
            if len(loops) != 2 or re.findall(r'``([\w.]+)', loops[0]) != roots or re.findall(r'``([\w.]+)', loops[1]) != models:
                raise ValueError('Wrong environment kind-check loops')
            if 'some (.thmInfo _)' not in check or 'some (.defnInfo _)' not in check:
                raise ValueError('Missing author environment kind test')
            if log.count('FINITE_TM2_BINARY_FIFTHS_165_ACTUAL_RUNS_PASS') != 1:
                raise ValueError('Missing actual 165-run fixture result')
            for path, row in json.loads(source(key, base + 'BINARY_FIFTHS_SOURCE_BINDING.json').read_text())['critical_sources'].items():
                if MANIFEST[key]['files'][path]['sha256'] != row['sha256']:
                    raise ValueError('Critical source binding differs')
        findings[key] = {'commit': MANIFEST[key]['commit'], 'theorems': roots, 'models': models,
                         'declarations': declarations, 'actual_axioms': actual_axioms,
                         'environment_kind_checks': key == 'fifths', 'independent_kernel': False,
                         'actual_fixture_runs': 165 if key == 'fifths' else None}
        lake = json.loads(source(key, base + 'lake-manifest.json').read_text())
        pin = [p['rev'] for p in lake['packages'] if p['name'] == 'mathlib']
        if pin != ['d13f23b723b8a846827a245b89c10fc7d3f11612']:
            raise ValueError('Wrong mathlib pin')
        if source(key, base + 'lean-toolchain').read_text().strip() != 'leanprover/lean4:v4.34.1':
            raise ValueError('Wrong Lean pin')
    dump('DECLARATIONS_AND_ACTUAL_AXIOMS.json', findings)
    print({'status': 'READ_ONLY_SOURCE_LOG_BINDING_PASS_NOT_KERNEL', 'fifths': [26, 11, 165],
           'query': [58, 40], 'fully_read_source_files': sum(map(len, reviewed.values())),
           'actual_log_files': 6, 'lean_invocations': 0, 'author_cache_reads': 0})


if __name__ == '__main__':
    main()
