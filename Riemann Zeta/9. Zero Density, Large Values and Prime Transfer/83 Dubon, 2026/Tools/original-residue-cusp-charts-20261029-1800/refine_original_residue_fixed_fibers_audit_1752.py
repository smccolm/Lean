from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re
p=Path(__file__).parent
cfg=json.loads((p/'original-residue-fixed-fibers-preflight-config-1749.json').read_text())
assert len(cfg['proofEdges'])==22 and len(cfg['roots'])==2
cfg['roots']+=cfg['constructions']
arr=lambda xs:'#['+', '.join('`'+x for x in xs)+']'
def write(n,t):
 f=p/n;assert not f.exists();f.write_text(t,encoding='utf-8')
write('original-residue-fixed-fibers-preflight-config-1752.json',json.dumps(cfg,indent=2)+'\n')
for old,new in [('SourceOriginalResidueFixedFibersPreflight1749','SourceOriginalResidueFixedFibersPreflight1752'),('SourceOriginalResidueFixedFibersValuePreflight1749','SourceOriginalResidueFixedFibersValuePreflight1752')]:
 s=(p/(old+'.lean')).read_text(encoding='utf-8')
 s=re.sub(r'let roots : Array Name := #\[[^\n]*\]','let roots : Array Name := '+arr(cfg['roots']),s)
 s=s.replace('closures of the actual original residue fixed-field identity','closures of the actual residue action construction, original residue fixed-field identity')
 write(new+'.lean',s)
s=(p/'audit_original_residue_fixed_fibers_preflight_1749.ps1').read_text().replace('Preflight1749','Preflight1752')
write('audit_original_residue_fixed_fibers_preflight_1752.ps1',s)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
write('original-residue-fixed-fibers-audit-refinement-1752.json',json.dumps(dict(
 recordedUTC=datetime.now(timezone.utc).isoformat(),
 reason='The two consumer proofs reduce the canonical residue action definition during elaboration; its name occurs in their types but not their values. The construction is itself a required audited deliverable, so add its value as an explicit root. Retain every one of the 22 required value checks and all public, private/generated, axiom and linter checks. No mathematical source changes. The claim is the value closure of both consumers and the actual action construction, not that a definitional name survives reduction inside a consumer proof.',
 failedValueAudit=str(p/'SourceOriginalResidueFixedFibersValuePreflight1749.log'),
 failedValueAuditSha256=sha(p/'SourceOriginalResidueFixedFibersValuePreflight1749.log'),
 oldRoots=cfg['roots'][:2],addedRoots=cfg['roots'][2:],removedChecks=[],proofChanges=[]
),indent=2)+'\n')
print('Prepared fresh 1752 audits: 3 value roots, all 22 required edges retained')
