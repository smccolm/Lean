from pathlib import Path
import re,json,hashlib
p=Path(__file__).parent
old=p/'SourceOriginalPrimitiveTateImageGlobalOwnership8133'
assert old.with_suffix('.exit').read_text().strip()=='1'
t=old.with_suffix('.log').read_text(encoding='utf-16')
assert 'unexpected identifier after decimal point' in t
log=p/'SourceOriginalPrimitiveTateImageOwnership8133.log'
names=re.findall(r'^OWNER \S+: (\S+)$',log.read_text(encoding='utf-16'),re.M)
assert len(names)==len(set(names))==140
def expr(n):
    s='Name.anonymous'
    for part in n.split('.'):
        s=('(Name.num '+s+' '+part+')') if part.isdigit() else '(Name.str '+s+' '+json.dumps(part)+')'
    return s
s=old.with_suffix('.lean').read_text(encoding='utf-8')
s=re.sub(r'  let names : Array Name := #[^\n]+',lambda _: '  let names : Array Name := #['+', '.join(map(expr,names))+']',s)
f=p/'SourceOriginalPrimitiveTateImageGlobalOwnership8133b.lean'
assert not f.exists()
f.write_text(s,encoding='utf-8')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
f=p/'source-original-primitive-tate-image-global-ownership-successor-8133b.json'
assert not f.exists()
f.write_text(json.dumps(dict(reason='Fresh audit renders numeric private-name components with Name.num instead of invalid identifier quotation. No project proof or used audit is changed. Every one of the same 140 focused theorem names is checked in the full import environment.',previousSourceSha256=sha(old.with_suffix('.lean')),previousLogSha256=sha(old.with_suffix('.log')),successorSourceSha256=sha(p/'SourceOriginalPrimitiveTateImageGlobalOwnership8133b.lean')),indent=2)+'\n',encoding='utf-8')
r=p/'record_source_original_primitive_tate_image_8133b.py'
assert not r.exists()
s=(p/'record_source_original_primitive_tate_image_8133.py').read_text(encoding='utf-8').replace("globalLog = p / 'SourceOriginalPrimitiveTateImageGlobalOwnership8133.log'", "globalLog = p / 'SourceOriginalPrimitiveTateImageGlobalOwnership8133b.log'")
compile(s,str(r),'exec')
r.write_text(s,encoding='utf-8')
