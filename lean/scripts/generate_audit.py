#!/usr/bin/env python3
"""Generate literal #print axioms commands for every exported project theorem."""
from pathlib import Path
import json
import re

ROOT = Path(__file__).resolve().parent.parent

def strip_comments(text):
    result = []
    depth = 0
    i = 0
    while i < len(text):
        if text[i:i + 2] == '/-':
            depth += 1
            i += 2
        elif depth and text[i:i + 2] == '-/':
            depth -= 1
            i += 2
        elif not depth and text[i:i + 2] == '--':
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        else:
            result.append(text[i] if not depth or text[i] == '\n' else ' ')
            i += 1
    if depth:
        raise RuntimeError('Unclosed Lean comment')
    return ''.join(result)

paths = [ROOT / 'Mxym.lean'] + sorted((ROOT / 'Mxym').glob('*.lean')) + sorted((ROOT / 'OAI').rglob('*.lean'))
exports = []
for path in paths:
    code = strip_comments(path.read_text())
    forbidden = re.findall(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by)\b', code)
    if forbidden:
        raise RuntimeError(f'Forbidden proof escape in {path}: {forbidden}')
    namespaces = []
    for line in code.splitlines():
        ns = re.match(r'^\s*namespace\s+([\w.]+)', line)
        end = re.match(r'^\s*end\s+([\w.]+)', line)
        theorem = re.match(r'^\s*(?:@\[[^\]]*\]\s*)?(?P<modifiers>(?:(?:private|protected|noncomputable)\s+)*)(?:theorem|lemma)\s+(?P<name>[\w.]+)', line)
        if ns:
            namespaces.append(ns.group(1))
        elif end:
            if namespaces and namespaces[-1] == end.group(1):
                namespaces.pop()
        elif theorem and 'private' not in theorem.group('modifiers').split():
            exports.append({'name': '.'.join(namespaces + [theorem.group('name')]),
                            'source': str(path.relative_to(ROOT))})
if len({e['name'] for e in exports}) != len(exports):
    raise RuntimeError('Duplicate theorem names')
(ROOT / 'Audit.lean').write_text('import Mxym\n\n' + ''.join(
    f"#print axioms {e['name']}\n" for e in exports))
(ROOT / 'Statements.lean').write_text('import Mxym\n\nset_option pp.funBinderTypes true\n\n' + ''.join(f"#check {e['name']}\n" for e in exports))
(ROOT / 'exported-theorems.json').write_text(json.dumps(exports, indent=2) + '\n')
print(f'Generated #print axioms for {len(exports)} exported theorems; no proof escapes in project sources.')
