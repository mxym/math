import datetime, hashlib, json, pathlib, zipfile

out=pathlib.Path(__file__).resolve().parent
author=pathlib.Path('/home/mxym/math-breadth-tcs-20261015/research/breadth-tcs-20261015/phase-8-coexistence-orientation')
archive=pathlib.Path('/mnt/d/math/tmp/breadth-tcs-20261015/phase-8-coexistence-orientation/orientation-owner-20261015T140115Z.zip')
digest=lambda b:hashlib.sha256(b).hexdigest()
expected='d3d1a625705c380dea45c5154dcd35b742e9291f178884ecc3837cf343b06996'
assert digest(archive.read_bytes())==expected
entries=[]
with zipfile.ZipFile(archive) as z:
    for item in z.infolist():
        if item.is_dir(): continue
        tag='worktree/research/breadth-tcs-20261015/phase-8-coexistence-orientation/'
        assert item.filename.startswith(tag), item.filename
        rel=item.filename[len(tag):]
        assert '..' not in pathlib.PurePosixPath(rel).parts
        data=z.read(item)
        live=(author/rel).read_bytes()
        assert data==live, rel
        dest=out/'frozen-author'/rel
        dest.parent.mkdir(parents=True,exist_ok=True)
        if dest.exists(): assert dest.read_bytes()==data
        else: dest.write_bytes(data)
        entries.append({'relative_path':rel,'bytes':len(data),'sha256':digest(data),'archive_equals_live':True})
manifest=json.loads((out/'frozen-author/AUTHOR_V1_MANIFEST.json').read_text())
print('MANIFEST_KEYS',list(manifest))
print(json.dumps(manifest,ensure_ascii=False))
assert digest((out/'frozen-author/PAPER.md').read_bytes())=='9fdb0649010809711223abd1f30778652ae9bde0cd1d768b66336c3ed22e5cb1'
assert digest((out/'frozen-author/AUTHOR_V1_MANIFEST.json').read_bytes())=='be554dd0e2ae2ce1d9bf41e55e1a59a729757711c0256ec1ec6ea0b580eabf83'
hn=pathlib.Path('/home/mxym/math-breadth-quantum-20261015/research/breadth-quantum-20261015/phase-5-haldane/CLOCK.json')
record={'time_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'archive':str(archive),'archive_sha256':expected,'all_archive_items_read_and_equal_live':True,'entries':entries,'HN0_clock_sha256':digest(hn.read_bytes()),'review_only':True}
(out/'INPUT_BINDING.json').write_text(json.dumps(record,indent=2)+'\n')
print('BOUND',len(entries),'HN0',record['HN0_clock_sha256'])
