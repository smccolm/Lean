from pathlib import Path
import json, re, hashlib
s = Path(__file__).parent
c = json.loads((s / 'source-projective-linear-preparation-2311.json').read_text())
for f in c['files'][15:]:
 assert (s / (f['module'] + '-2311.exit')).read_text().strip() == '0'
 assert (s / (f['module'] + '-2311.log')).stat().st_size == 0
 t = (s / (f['module'] + '.lean')).read_text('utf-8')
 assert hashlib.sha256(t.encode()).hexdigest().upper() == f['canonicalSha256']
 ns = re.search(r'(?m)^namespace (\S+)', t).group(1)
 for kind, name in re.findall(r'(?m)^(theorem|def) (\S+)', t):
  q = ns + '.' + name
  assert q not in c['queries']
  c['queries'].append(q)
  c['theorems' if kind == 'theorem' else 'constructions'].append(q)
out = s / 'source-projective-linear-audit-config-2313.json'
assert not out.exists()
out.write_text(json.dumps(c, indent=2) + '\n', encoding='utf-8')
arr = lambda xs: '#[' + ', '.join('`' + n for n in xs) + ']'
t = (s / 'SourceProjectiveClassificationAudit2.lean').read_text('utf-8')
t = t.replace('import SourceGammaOneProjectiveResidual', 'import SourceGammaOneProjectiveLinearResidual')
t = re.sub(r'^#print axioms .+\n', '', t, flags=re.M)
t = t.replace('open Lean\n', 'open Lean\n\n' + '\n'.join('#print axioms ' + n for n in c['queries']) + '\n', 1)
t = re.sub(r'let modules : Array Name := #\[.*\]', 'let modules : Array Name := ' + arr(c['modules']), t)
t = re.sub(r'^#lint in .+\n', '', t, flags=re.M)
t += '\n'.join('#lint in ' + n for n in c['modules']) + '\n'
t = t.replace('SOURCE PROJECTIVE CLASSIFICATION AXIOM AUDIT PASS', 'SOURCE PROJECTIVE LINEAR AXIOM AUDIT PASS')
t = t.replace('The original-form consumer proves the projective classification alternatives.', 'The original-form consumer proves the full projective classification, explicit matrix conjugacy and small-image-or-linear-subfield bounds.')
(s / 'SourceProjectiveLinearAudit1.lean').write_text(t, encoding='utf-8')
t = (s / 'SourceProjectiveClassificationDependencyAudit2.lean').read_text('utf-8')
t = t.replace('import SourceGammaOneProjectiveResidual', 'import SourceGammaOneProjectiveLinearResidual')
for key, values in [('roots', c['roots']), ('localModules', c['modules']), ('required', c['proofEdges'])]:
 t = re.sub('let ' + key + r' : Array Name := #\[.*\]', 'let ' + key + ' : Array Name := ' + arr(values), t)
t = t.replace('SOURCE PROJECTIVE CLASSIFICATION VALUE AUDIT PASS', 'SOURCE PROJECTIVE LINEAR VALUE AUDIT PASS')
t = t.replace('The actual original arithmetic residual action and both classification branches are consumed.', 'The actual original arithmetic residual action, both classification branches, explicit matrix conjugacy and native perfect-SL2 lifting are consumed.')
(s / 'SourceProjectiveLinearDependencyAudit1.lean').write_text(t, encoding='utf-8')
print(json.dumps(dict(modules=len(c['modules']), queries=len(c['queries']),
 theorems=len(c['theorems']), constructions=len(c['constructions']),
 requiredProofEdges=len(c['proofEdges']), ownershipReconciliation='pending exact environment enumeration')))
