from pathlib import Path
import datetime, hashlib, json

p = Path(__file__).parent
paper = Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
data = json.loads((paper / 'Tools/source-gamma-one-rational-fourier.json').read_text(encoding='utf-8'))
names = json.loads((p / 'source-gamma-one-rational-fourier-scratch-ownership-8493.json').read_text())
assert len(names) == len(data['scratchCertificates']) == 3
assert sum(len(c['modules']) for c in data['scratchCertificates']) == 22
assert sum(c['exhaustiveTheorems'] for c in data['scratchCertificates']) == 89
old = p / 'compare_gamma_one_rational_fourier_ownership_8493.py'
body = old.read_text(encoding='utf-8')
assert body.count('assert len(names)==len(certs)==7') == 1
body = body.replace('assert len(names)==len(certs)==7',
    'assert len(names)==len(certs)==3\nassert len(allmods)==len(set(allmods))==22')
new = p / 'compare_gamma_one_rational_fourier_ownership_8493b.py'
with new.open('x', encoding='utf-8', newline='\n') as f: f.write(body)
compile(body, str(new), 'exec')
oldv = p / 'verify_gamma_one_rational_fourier_8493.ps1'
v = oldv.read_text(encoding='utf-8')
assert v.count('compare_gamma_one_rational_fourier_ownership_8493.py') == 1
v = v.replace('compare_gamma_one_rational_fourier_ownership_8493.py',
              'compare_gamma_one_rational_fourier_ownership_8493b.py')
newv = p / 'verify_gamma_one_rational_fourier_8493b.ps1'
with newv.open('x', encoding='utf-8', newline='\n') as f: f.write(v)
record = dict(recordedUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    failure='Original ownership-comparison wrapper stopped at assert len(names)==len(certs)==7. Seven was the previous promotion batch size; this batch has exactly three frozen scopes. Failure occurred before any comparison receipt, foundation run or paper run.',
    preserved=[dict(path=str(f), sha256=sha(f)) for f in [old, oldv]],
    successors=[dict(path=str(f), sha256=sha(f)) for f in [new, newv]],
    correction='Require exactly three scopes and exactly 22 distinct modules. All 89 exhaustive scratch checks, exact theorem-name comparison, source-body equality, ownership checks, diagnostic checks and every other verification condition remain required.',
    evidence='Aggregate, focused axiom/linter audit, all three proof-VALUE audits, focused production ownership and all three scratch ownership audits already passed. Existing audit logs are reused without rerunning or editing them.',
    status='Fresh wrapper prepared; mathematical source and proof audits unchanged. Sequential foundation/paper verification pending.')
with (p / 'gamma-one-rational-fourier-verification-wrapper-review-8493b.json').open('x', encoding='utf-8', newline='\n') as f:
    json.dump(record, f, indent=2); f.write('\n')
print(json.dumps(dict(scopes=3, modules=22, exhaustiveScratchChecks=89, successor=str(newv))))
