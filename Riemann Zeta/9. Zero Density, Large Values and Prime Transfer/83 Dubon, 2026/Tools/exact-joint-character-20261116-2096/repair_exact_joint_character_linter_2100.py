from pathlib import Path
from datetime import datetime, timezone
import json, re, hashlib, ast
p=Path(__file__).parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
old='binaryExactJointOperatorRing_ring'
new='instRingBinaryExactJointOperatorRing'
f=p/'SourceGammaOneExactJointRing.lean'
failed=p/'SourceGammaOneExactJointRing2095Failed.lean.txt'
assert not failed.exists()
t=f.read_text(encoding='utf-8');assert t.count(old)==1
failed.write_bytes(f.read_bytes())
f.write_text(t.replace(old,new),encoding='utf-8')
v=p/'SourceGammaOneExactJointRing2090b.lean';assert not v.exists()
v.write_text((p/'SourceGammaOneExactJointRing2090a.lean').read_text(encoding='utf-8').replace(old,new),encoding='utf-8')
cfg=json.loads((p/'source-gammaone-exact-joint-character-1-audit-config.json').read_text(encoding='utf-8'))
for key in ['constructions','queries','proofEdges']:
 cfg[key]=[x.replace(old,new) for x in cfg[key]]
rebuild=['SourceGammaOneExactJointRing','SourceGammaOneExactJointSquare','SourceGammaOneExactJointFinite','SourceGammaOneExactJointCharacter','SourceGammaOneGeometricExactJointCharacter']
for m in rebuild:cfg['compileEvidence'][m]=m+'-2100'
def output(name,t):
 f=p/name;assert not f.exists(),f
 if name.endswith('.py'):ast.parse(t)
 f.write_text(t,encoding='utf-8')
output('source-gammaone-exact-joint-character-2-audit-config.json',json.dumps(cfg,indent=2)+'\n')
for oldfile,newfile in [('SourceGammaOneExactJointCharacterAudit1','SourceGammaOneExactJointCharacterAudit2'),('SourceGammaOneExactJointCharacterDependencyAudit1','SourceGammaOneExactJointCharacterDependencyAudit2'),('SourceGammaOneExactJointCharacterScratchOwnership2095','SourceGammaOneExactJointCharacterScratchOwnership2100')]:
 output(newfile+'.lean',(p/(oldfile+'.lean')).read_text(encoding='utf-8').replace(old,new))
fa=p/'SourceGammaOneExactJointCharacterAudit1.lean';fa.rename(fa.with_suffix('.lean.txt'))
route=json.loads((p/'source-gammaone-exact-joint-character-audit-route-2095.json').read_text(encoding='utf-8'))
route['recordedUTC']=datetime.now(timezone.utc).isoformat()
route['linterRepair']=dict(failedAudit=str(p/'SourceGammaOneExactJointCharacterAudit1.log'),failedAuditSha256=sha(p/'SourceGammaOneExactJointCharacterAudit1.log'),failedCanonicalSource=str(failed),failedCanonicalSha256=sha(failed),oldName=old,newName=new,reason='defsWithUnderscore rejected the explicit ring-instance name. Only that declaration identifier is corrected; statement and value remain identical. Fresh dependent compilations and all audits are mandatory. No linter suppression or proof limit change.')
route['reuseChecked'].append(dict(path=str(p/'SourceGammaOneExactJointCharacterAudit1.log'),sha256=sha(p/'SourceGammaOneExactJointCharacterAudit1.log')))
route['boundary']='Focused mathematical statements compiled; fresh canonical and full audits after the instance-name correction pending.'
output('source-gammaone-exact-joint-character-audit-route-2100.json',json.dumps(route,indent=2)+'\n')
subs={'source-gammaone-exact-joint-character-1':'source-gammaone-exact-joint-character-2','SourceGammaOneExactJointCharacterAudit1':'SourceGammaOneExactJointCharacterAudit2','SourceGammaOneExactJointCharacterDependencyAudit1':'SourceGammaOneExactJointCharacterDependencyAudit2','2095':'2100'}
pat=re.compile('|'.join(re.escape(s) for s in sorted(subs,key=len,reverse=True)))
tr=lambda t:pat.sub(lambda m:subs[m[0]],t)
t=tr((p/'build_gammaone_exact_joint_character_canonical_2095.ps1').read_text(encoding='utf-8'))
t=re.sub(r'(?m)^\$names=@\(.*$', '$names=@('+','.join("'"+m+"'" for m in rebuild)+')',t)
output('build_gammaone_exact_joint_character_canonical_2100.ps1',t)
output('audit_gammaone_exact_joint_character_2100.ps1',tr((p/'audit_gammaone_exact_joint_character_2095.ps1').read_text(encoding='utf-8')))
output('record_gammaone_exact_joint_character_2100.py',tr((p/'record_gammaone_exact_joint_character_2095.py').read_text(encoding='utf-8')))
prep=p/'prepare_exact_joint_character_promotion_2096.py'
pt=prep.read_text(encoding='utf-8').replace('source-gammaone-exact-joint-character-1-scratch-receipt.json','source-gammaone-exact-joint-character-2-scratch-receipt.json')
prep.write_text(pt,encoding='utf-8')
print(json.dumps(dict(recompiledModules=rebuild,publicQueries=18,strictValueEdges=27,mathematicalChange=False,instanceNameRepair=True)))
