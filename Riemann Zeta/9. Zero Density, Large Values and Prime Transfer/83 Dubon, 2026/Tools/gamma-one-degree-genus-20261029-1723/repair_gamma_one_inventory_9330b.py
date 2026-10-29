from pathlib import Path
import collections, hashlib, json

p = Path(__file__).parent
r = Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
path = r / 'Tools/scaffold.json'
before = path.read_bytes()
c = json.loads(before)
groups = collections.defaultdict(list)
for x in c['files']:
    groups[x['path']].append(x)
duplicates = {k: v for k, v in groups.items() if len(v) > 1}
assert duplicates
for k, v in duplicates.items():
    assert k.startswith('Tools/gamma-one-degree-genus-20261029-1723/')
    assert all(x == v[0] for x in v)
    assert (r / k).is_file()
archive = r / 'Tools/gamma-one-degree-genus-20261029-1723'
saved = archive / 'scaffold-before-inventory-repair-9330b.json'
assert not saved.exists()
saved.write_bytes(before)
c['files'] = [v[0] for v in groups.values()]
note = archive / 'inventory-repair-9330b.json'
assert not note.exists()
sha = lambda b: hashlib.sha256(b).hexdigest().upper()
note.write_text(json.dumps(dict(
    reason='The strict paper runner rejected duplicate identical retained-file classifications. The promotion archived both a failed Lean source and its preserved .lean.txt evidence to the same inert target and registered that unchanged target twice. Retain every artifact and exactly one identical classification; no source, audit, runner or verification requirement is altered.',
    originalScaffoldSha256=sha(before),
    previousPaperExit=1,
    previousPaperConsoleSha256=sha((p/'paper-verification-9330-console.log').read_bytes()),
    duplicates=[dict(path=k, occurrences=len(v), entry=v[0], sha256=sha((r/k).read_bytes())) for k,v in duplicates.items()],
    retainedDistinctPaths=len(groups),
    removedFiles=[], proofSourceChanges=[], acceptance='16/20; DUB-17--20 OPEN'
), indent=2)+'\n', encoding='utf-8')
for f in [saved, note]:
    c['files'].append(dict(path=f.relative_to(r).as_posix(),role='Tools'))
assert len(c['files']) == len({x['path'] for x in c['files']})
path.write_text(json.dumps(c, indent=2, ensure_ascii=False)+'\n', encoding='utf-8')

# Preserve the failed 9330 evidence and repeat the full sequential verification.
v = (p/'verify_gamma_one_degree_genus_9330.ps1').read_text()
start = v.index("Set-Location -LiteralPath $taskRepo\n")
head = v[:v.index('# Preserve independently')]
v = head + v[start:]
v = v.replace('root-verification-9330-console','root-verification-9330b-console')
v = v.replace('paper-verification-9330-console','paper-verification-9330b-console')
v = v.replace('record_source_gamma_one_degree_genus_9330.py','record_source_gamma_one_degree_genus_9330b.py')
target = p/'verify_gamma_one_degree_genus_9330b.ps1'
assert not target.exists()
target.write_text(v, encoding='utf-8')
rec = (p/'record_source_gamma_one_degree_genus_9330.py').read_text()
rec = rec.replace('root-verification-9330-console','root-verification-9330b-console')
rec = rec.replace('paper-verification-9330-console','paper-verification-9330b-console')
target = p/'record_source_gamma_one_degree_genus_9330b.py'
assert not target.exists()
target.write_text(rec, encoding='utf-8')
arc = (p/'archive_gamma_one_degree_genus_canonical_9330.py').read_text()
arc = arc.replace('root-verification-9330-console','root-verification-9330b-console')
arc = arc.replace('paper-verification-9330-console','paper-verification-9330b-console')
target = p/'archive_gamma_one_degree_genus_canonical_9330b.py'
assert not target.exists()
target.write_text(arc, encoding='utf-8')
print(json.dumps(dict(duplicatePaths=len(duplicates), classificationsRemoved=sum(len(v)-1 for v in duplicates.values()), artifactsRemoved=0, next='verify_gamma_one_degree_genus_9330b.ps1')))
