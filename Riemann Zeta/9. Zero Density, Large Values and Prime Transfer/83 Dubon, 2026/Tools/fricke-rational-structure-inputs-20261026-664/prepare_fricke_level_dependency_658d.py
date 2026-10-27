from pathlib import Path
import json,re,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
c=json.loads((p/'source-fricke-level-field-7c-audit-config.json').read_text())
n='Dubon2026.SourceFricke.levelFieldRingSMul'
c['proofEdges'].remove(n);c['separatelyAxiomChecked'].append(n)
c['separateReason']+=' The native algebra scalar-multiplication selection alias reduces during elaboration and is absent as a named constant from the terminal proof values; its axiom check remains in Audit7c.'
f=p/'source-fricke-level-field-7d-audit-config.json';assert not f.exists();f.write_text(json.dumps(c,indent=2)+'\n')
s=(p/'SourceFrickeLevelFieldDependencyAudit7c.lean').read_text(encoding='utf-8')
s=re.sub(r'let required : Array Name := #\[[^\n]*',lambda _:'let required : Array Name := #['+', '.join('`'+n for n in c['proofEdges'])+']',s)
f=p/'SourceFrickeLevelFieldDependencyAudit7d.lean';assert not f.exists();f.write_text(s,encoding='utf-8')
route=json.loads((p/'fricke-level-field-route-658.json').read_text())
route['auditSuccessor']='Full exhaustive audit and all seven 16-linter scopes passed in Audit7c. DependencyAudit7c found only the native scalar selection alias absent from values; 7d retains its explicit axiom query and no longer claims named use. No audited mathematical source is changed.'
route['sourceSuccessor']='V3 preserves all mathematical conclusions. Successors correct the finite-enumeration name, remove unused nonzero constraints from the fraction-ring type and purely native scalar/j embeddings, and classify proposition-valued instances as theorems. API/instance-search failures and preceding audit evidence are retained.'
f=p/'fricke-level-field-route-658d.json';assert not f.exists();f.write_text(json.dumps(route,indent=2)+'\n')
print(json.dumps(dict(proofEdges=len(c['proofEdges']),separatelyAxiomChecked=c['separatelyAxiomChecked'])))
