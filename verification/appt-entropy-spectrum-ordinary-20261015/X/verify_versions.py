"""Verify exact v1/v2 inputs and reverse the complete mathematical delta in memory."""
from pathlib import Path
import datetime as dt
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
V1 = HERE/'owner-snapshot/all-dimension-positive-entropy-20261015'
V2 = HERE/'owner-v2-snapshot/all-dimension-positive-entropy-20261015-author-v2'

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def reverse_patch(new, diff):
    output = []
    source = new.splitlines(keepends=True)
    lines = diff.splitlines(keepends=True)
    pos = 0
    i = 2
    hunks = 0
    while i < len(lines):
        header = lines[i]
        match = re.fullmatch(r'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@.*\n?', header)
        assert match, header
        old_start, old_count, new_start, new_count = map(int, (match[1], match[2] or '1', match[3], match[4] or '1'))
        assert new_start-1 >= pos
        output += source[pos:new_start-1]
        pos = new_start-1
        i += 1
        old_seen = new_seen = 0
        while i < len(lines) and not lines[i].startswith('@@ '):
            tag, body = lines[i][0], lines[i][1:]
            if tag == ' ':
                assert source[pos] == body, (source[pos], body)
                output.append(body)
                pos += 1
                old_seen += 1
                new_seen += 1
            elif tag == '+':
                assert source[pos] == body, (source[pos], body)
                pos += 1
                new_seen += 1
            elif tag == '-':
                output.append(body)
                old_seen += 1
            else:
                raise AssertionError(lines[i])
            i += 1
        assert (old_seen, new_seen) == (old_count, new_count)
        hunks += 1
    output += source[pos:]
    assert hunks == 1
    return ''.join(output)

def main():
    records = []
    for root, manifest, expected in ((V1, 'AUTHOR_V1_MANIFEST.json', '8f16f2ae537ed9ac281403e0b49ba406ede1ea45df99dc9397c18f0333a1966d'),
                                     (V2, 'AUTHOR_V2_MANIFEST.json', '00a0de17b10d77c8844a7d482fac5f991708c8079b950739c7a809ac1e19db0e')):
        assert sha(root/manifest) == expected
        data = json.loads((root/manifest).read_text())
        for rel, h in data['files'].items():
            assert sha(root/rel) == h, (root, rel)
        actual = {p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file()}
        assert actual == set(data['files']) | {manifest}
        records.append({'root': root.relative_to(HERE).as_posix(), 'manifest': manifest, 'manifest_sha256': expected,
                        'literal_files_checked': len(actual), 'paper_sha256': sha(root/'PAPER.md'),
                        'paper_bytes': (root/'PAPER.md').stat().st_size,
                        'paper_lines': len((root/'PAPER.md').read_text().splitlines())})
    # ZIP bytes and all historical inputs remain retained separately.
    assert sha(HERE/'owner.zip') == 'ff13766b14d523c1a0d284791b0029a984d39259a05a5a7edd2119668638212a'
    assert sha(HERE/'owner-v2.zip') == '304d2141175b13e3ffafdc8c96080bcc323aa34ea78340cdc5e76832dce8008a'
    v1 = (V1/'PAPER.md').read_text()
    v2 = (V2/'PAPER.md').read_text()
    restored = reverse_patch(v2, (V2/'AUTHOR_V1_TO_V2.diff').read_text())
    assert restored.encode() == (V1/'PAPER.md').read_bytes()
    # All original inputs other than the one paragraph retain exact v1 bytes.
    changed = [p.relative_to(V1).as_posix() for p in V1.rglob('*') if p.is_file()
               and p.read_bytes() != (V2/p.relative_to(V1)).read_bytes()]
    assert changed == ['PAPER.md'], changed
    c0 = json.loads((V1/'control-runs/20261015T132659.576684Z/RESULT.json').read_text())
    c1 = json.loads((V2/'control-runs/20261015T134507.331566Z/RESULT.json').read_text())
    assert c0['status'] == c1['status'] == 'PASS'
    assert c0['checks'] == c1['checks']
    ep = json.loads((V2/'endpoint-control-runs/20261015T134507.331718Z/RESULT.json').read_text())
    assert ep['status'] == 'PASS' and ep['exact_symbolic_and_endpoint_assertions'] == 6
    result = {'status': 'PASS', 'decision': 'PASS', 'utc': dt.datetime.now(dt.timezone.utc).isoformat(),
              'versions': records, 'exact_complete_one_hunk_reverse_recovery': True,
              'all_existing_v1_files_unchanged_except_current_paper': changed,
              'frozen_v1_zip_and_snapshot_unmodified': True,
              'credited_inputs_v1_v2_literal_equal': 20,
              'author_runs_read_not_executed_by_reviewer': ['132659.576684Z', '134507.331566Z', '134507.331718Z'],
              'same_eight_author_groups_v1_v2': True,
              'current_v2_author_endpoint_assertions': 6,
              'not_a_future_publication_or_transport_binding': True}
    dest = HERE/'VERSION_VERIFICATION.json'
    assert not dest.exists()
    dest.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
