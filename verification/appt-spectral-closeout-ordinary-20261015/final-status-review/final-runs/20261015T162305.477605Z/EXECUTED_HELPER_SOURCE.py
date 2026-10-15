"""Metadata-only review helpers; no mathematical source execution."""
from pathlib import PurePosixPath
from collections import Counter
from urllib.parse import unquote,urlsplit
import difflib,hashlib,posixpath,re,unicodedata

def sha(data):return hashlib.sha256(data).hexdigest()
def exact_hash(data,row):
    assert sha(data)==row['sha256'],('SHA256 mismatch',row['sha256'],sha(data))
    if 'bytes' in row:assert len(data)==row['bytes'],('byte-count mismatch',row['bytes'],len(data))

def links(text):
    # Existing repository uses inline Markdown links; preserve all targets,
    # including URLs and fragments, rather than reducing them to paths.
    return re.findall(r'\]\((<[^>]+>|[^\n]+?)\)',text)

def require_old_text_preserved(old,new,max_inserted_lines=2,allow_phase_row_update=False):
    assert not Counter(links(old))-Counter(links(new)), 'old links removed'
    if allow_phase_row_update:
        marker='appt-linear-phase-diagram-20261015/README.md'
        oldphase=[line for line in old.splitlines(keepends=True) if marker in line]
        newphase=[line for line in new.splitlines(keepends=True) if marker in line]
        assert len(oldphase)==len(newphase)==1,('phase row ambiguity',len(oldphase),len(newphase))
        assert 'appt-coexistence-orientation-20261015/README.md' in newphase[0]
        old=''.join(line for line in old.splitlines(keepends=True) if marker not in line)
        new=''.join(line for line in new.splitlines(keepends=True) if marker not in line)
    a=old.splitlines(keepends=True);b=new.splitlines(keepends=True)
    ops=difflib.SequenceMatcher(a=a,b=b,autojunk=False).get_opcodes()
    inserted=[]
    for tag,al,ar,bl,br in ops:
        assert tag in ('equal','insert'),('existing lines changed',tag,al,ar,bl,br)
        if tag=='insert':inserted.extend(b[bl:br])
    assert len(inserted)==max_inserted_lines,('new row count',len(inserted),max_inserted_lines)
    return inserted

def anchors(text):
    result=set();seen=Counter();fence=None
    for line in text.splitlines():
        code=re.match(r'^\s*(`{3,}|~{3,})',line)
        if code:
            char=code.group(1)[0]
            if fence is None:fence=char
            elif fence==char:fence=None
            continue
        if fence:continue
        for value in re.findall(r'<a\s+(?:[^>]*?\s)?(?:id|name)=["\']([^"\']+)["\']',line,re.I):result.add(value)
        h=re.match(r'^ {0,3}#{1,6}\s+(.+?)\s*#*\s*$',line)
        if h:
            title=h.group(1).strip()
            title=re.sub(r'<[^>]*>','',title)
            title=re.sub(r'\[([^\]]+)\]\([^)]*\)',r'\1',title)
            title=title.replace('`','').lower()
            slug=''.join(ch for ch in title if ch in '-_ ' or not unicodedata.category(ch).startswith(('P','S','C'))).replace(' ','-')
            n=seen[slug];seen[slug]+=1
            result.add(slug if n==0 else slug+'-'+str(n))
    return result

def local_target(source,target):
    value=target.strip('<>')
    if re.match(r'^(?:[a-zA-Z][a-zA-Z0-9+.-]*:|//)',value):return None
    path,sep,fragment=value.partition('#')
    path=unquote(path.split('?',1)[0])
    resolved=posixpath.normpath(posixpath.join(posixpath.dirname(source),path)) if path else source
    assert not resolved.startswith(('/','../')),('outside repository',source,target,resolved)
    return resolved,unquote(fragment) if sep else ''

def require_anchor(text,fragment):
    assert fragment in anchors(text),('missing anchor',fragment,sorted(anchors(text)))

def reject_scope_label(scope,label):
    # Diagnostic consistency rules for labels, not new theorem statements.
    l=label.lower()
    if scope=='S8':assert not any(s in l for s in ['physical all c limits','physical c->infinity','physical c->0','physical r->infinity'])
    if scope=='S9':assert not any(s in l for s in ['fixed-m extension','all-dimension extension'])
    if scope=='Rglob' and 'benchmark' in l:assert 'joint d' in l or 'd->infinity' in l
