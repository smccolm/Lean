from pathlib import Path
from datetime import datetime, timezone
import hashlib, json

s = Path(__file__).parent
p = Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
a = p/'Tools/gamma-one-finite-charts-divisors-20261027-740'
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
original = a/'reuse-head-refresh-741/Dubon Reuse Refresh 2026-10-27.md'
snapshot = original.with_name(original.name+'.txt')
assert sha(original) == sha(p/original.name) == '0492A53D656A52E89B93B5EB506066901BAB9507AF71E81608B394B1A338C34D'
assert not snapshot.exists()
oldmanifest = a/'archive-manifest.json'
manifest = a/'archive-manifest-8586b.json'
repairpath = a/'archive-packaging-repair-8586b.json'
assert not manifest.exists() and not repairpath.exists()
cpath = p/'Tools/scaffold.json'
c = json.loads(cpath.read_text(encoding='utf-8'))
oldrel, newrel = (f.relative_to(p).as_posix() for f in [original, snapshot])
assert sum(x['path']==oldrel for x in c['files'])==1
assert not any(x['path']==newrel for x in c['files'])
m = json.loads(oldmanifest.read_text(encoding='utf-8'))
assert sum(x['path']==oldrel for x in m['files'])==1
for row in m['files']:
    assert sha(p/row['path'])==row['sha256'], row['path']
    if row['path']==oldrel: row['path']=newrel
metadata = [p/'Tools/lean-reuse-audit-20261015.json',p/'Tools/lean-reuse-audit-20261020.json',p/'Tools/source-gamma-one-finite-charts-divisors.json']
updates=[]
for f in metadata:
    d=json.loads(f.read_text(encoding='utf-8'))
    k=d['appliedSourceGammaOneFiniteChartsDivisors'] if f.name.endswith('20261015.json') else d
    assert k['proofEvidenceArchive']['sha256']==sha(oldmanifest)
    assert 'receipt8586' not in k
    updates.append((f,d,k))
repair=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),
    reason='The byte-identical research snapshot retains links relative to the paper root. Its archival copy must be plain text; the public root Markdown report remains unchanged with working links.',
    failure=dict(sessionExit=1,stage='Paper inventory, before Lean compilation',
        console=str(s/'paper-verification-8586-console.log'),consoleSha256=sha(s/'paper-verification-8586-console.log'),
        exitFileAbsentReason='PowerShell stopped on native stderr before writing the exit file.'),
    predecessorManifest=dict(path=oldmanifest.relative_to(p).as_posix(),sha256=sha(oldmanifest)),
    relocation=dict(oldPath=oldrel,newPath=newrel,unchangedSha256=sha(original)),
    sourceProofChanges=False,verification='Fresh sequential foundation/paper successor required; no failed run is relabeled.')
snapshot.write_bytes(original.read_bytes())
assert sha(snapshot)==sha(original)
original.unlink()
manifest.write_text(json.dumps(m,indent=2)+'\n',encoding='utf-8')
repairpath.write_text(json.dumps(repair,indent=2)+'\n',encoding='utf-8')
for row in c['files']:
    if row['path']==oldrel:row['path']=newrel
for f in [manifest,repairpath]:c['files'].append(dict(path=f.relative_to(p).as_posix(),role='Tools'))
for f,d,k in updates:
    k['archivePackagingRepair8586b']=dict(path=repairpath.relative_to(p).as_posix(),sha256=sha(repairpath))
    k['proofEvidenceArchive']=dict(k['proofEvidenceArchive'],manifest=manifest.relative_to(p).as_posix(),sha256=sha(manifest))
    f.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
cpath.write_text(json.dumps(c,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')

# Fresh canonical recorder; retain the successful focused receipt without rerunning it.
f=s/'record_source_gamma_one_finite_charts_divisors_8586b.py'
assert not f.exists()
t=(s/'record_source_gamma_one_finite_charts_divisors_8586.py').read_text(encoding='utf-8')
for old,new in [('root-verification-8586-console','root-verification-8586b-console'),('paper-verification-8586-console','paper-verification-8586b-console'),('SourceGammaOneFiniteChartsDivisorsGlobalOwnership8586','SourceGammaOneFiniteChartsDivisorsGlobalOwnership8586b')]:t=t.replace(old,new)
f.write_text(t,encoding='utf-8')
f=s/'prepare_gamma_one_finite_charts_divisors_global_ownership_8586b.py'
assert not f.exists()
t=(s/'prepare_gamma_one_finite_charts_divisors_global_ownership_8586.py').read_text(encoding='utf-8').replace('GlobalOwnership8586','GlobalOwnership8586b')
f.write_text(t,encoding='utf-8')
f=s/'verify_gamma_one_finite_charts_divisors_8586b.ps1'
assert not f.exists()
t=(s/'verify_gamma_one_finite_charts_divisors_8586.ps1').read_text(encoding='utf-8')
start=t.index('# Preserve independently executed scratch ownership logs;')
end=t.index('Set-Location -LiteralPath $taskRepo',start)
t=t[:start]+"# Focused checks already passed; preserved immutable receipt is checked by the recorder.\n"+t[end:]
for old,new in [('root-verification-8586-console','root-verification-8586b-console'),('paper-verification-8586-console','paper-verification-8586b-console'),('GlobalOwnership8586','GlobalOwnership8586b'),('global_ownership_8586.py','global_ownership_8586b.py'),('record_source_gamma_one_finite_charts_divisors_8586.py','record_source_gamma_one_finite_charts_divisors_8586b.py')]:t=t.replace(old,new)
t=t.replace('cmd /c run_',"$ErrorActionPreference='Continue'\ncmd /c run_").replace('$taskExit=$LASTEXITCODE',"$taskExit=$LASTEXITCODE\n$ErrorActionPreference='Stop'")
f.write_text(t,encoding='utf-8')
print(json.dumps(repair))
