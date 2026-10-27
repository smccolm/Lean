from pathlib import Path
import json
p=Path(r'E:\Lean\.tmp\dubon83')
c=json.loads((p/'source-transcendental-constant-integral-span-7-audit-config.json').read_text())
for m in c['modules']:
 f=p/(m+'V2.lean');assert not f.exists()
 s=(p/(m+'.lean')).read_text(encoding='utf-8')
 for n in c['modules']:s=s.replace('import '+n+'\n','import '+n+'V2\n')
 s=s.replace('algebraTRng_KFldT','algebraTRngKFldT').replace('commRing_RFa','commRingRFa')
 f.write_text(s,encoding='utf-8')
# Preserve failed audit, mathematical sources, config and logs as immutable originals.
s=(p/'prepare_transcendental_constant_integral_span_audit_667d.py').read_text(encoding='utf-8')
for m in c['modules']:s=s.replace("'"+m+"'","'"+m+"V2'")
s=s.replace('source-transcendental-constant-integral-span-7-', 'source-transcendental-constant-integral-span-7e-')
s=s.replace('IntegralSpanAudit7','IntegralSpanAudit7e').replace('IntegralSpanDependencyAudit7','IntegralSpanDependencyAudit7e')
s=s.replace('transcendental-constant-integral-span-route-667d.json','transcendental-constant-integral-span-route-667e.json')
s=s.replace("route['predecessorRouteSha256']=", "route['firstAuditFailure']='The original full audit proved the axiom checks but reported two definition-naming linter errors. Original mathematical sources and audit evidence are immutable; fresh V2 modules rename only the two construction identifiers, with identical mathematical statements. No linter is suppressed.'\nroute['predecessorRouteSha256']=")
f=p/'prepare_transcendental_constant_integral_span_audit_667e.py';assert not f.exists();f.write_text(s,encoding='utf-8')
print('Created seven fresh V2 modules for naming-linter repairs; failed audited originals preserved.')