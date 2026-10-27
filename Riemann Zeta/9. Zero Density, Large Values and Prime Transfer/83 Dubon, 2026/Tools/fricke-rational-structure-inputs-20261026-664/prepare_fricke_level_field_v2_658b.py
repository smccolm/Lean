from pathlib import Path
import json,re
p=Path(r'E:\Lean\.tmp\dubon83')
c=json.loads((p/'source-fricke-level-field-7-audit-config.json').read_text())
mods=c['modules']
for m in mods:
 s=(p/(m+'.lean')).read_text(encoding='utf-8')
 for old in mods:s=s.replace('import '+old+'\n','import '+old+'V2\n')
 s=s.replace('levelGrp_fintype','levelGrpFintype')
 s=s.replace('abbrev levelField (N : ℕ) [NeZero N] : Type','abbrev levelField (N : ℕ) : Type')
 s=s.replace('local instance ringSelfDistribMulAction (N : ℕ) [NeZero N] :','local instance ringSelfDistribMulAction (N : ℕ) :')
 f=p/(m+'V2.lean');assert not f.exists();f.write_text(s,encoding='utf-8')
f=p/'SourceFrickeStableAlgebra.lean';s=f.read_text(encoding='utf-8').replace('import SourceFrickeFixedFieldJ\n','import SourceFrickeFixedFieldJV2\n');f.write_text(s,encoding='utf-8')
s=(p/'prepare_fricke_level_field_audit_658.py').read_text(encoding='utf-8')
for m in mods:s=s.replace("'"+m+"'","'"+m+"V2'")
s=s.replace('source-fricke-level-field-7-audit','source-fricke-level-field-7b-audit').replace('SourceFrickeLevelFieldAudit7.lean','SourceFrickeLevelFieldAudit7b.lean').replace('SourceFrickeLevelFieldDependencyAudit7.lean','SourceFrickeLevelFieldDependencyAudit7b.lean')
fix='''propInstances=['slFn_smulCommClass','levelRing_isDomain','levelRing_smulCommClass','levelFixer_normal','levelFixer_finiteIndex','levelGrp_smulCommClass','levelGrp_faithful','levelGrp_smulDistribClass','levelGrpField_faithful','levelGrpField_smulCommClass']
for n in propInstances:
 defs.remove(ns+n);ths.append(ns+n)
'''
s=s.replace('roots=[ns+',fix+'roots=[ns+',1)
f=p/'prepare_fricke_level_field_audit_658b.py';assert not f.exists();f.write_text(s,encoding='utf-8')
print(json.dumps(dict(modules=[m+'V2' for m in mods],corrections=['name of finite enumeration','remove unused nonzero assumption from fraction-ring type and native self action','classify proposition-valued instances as theorems'],mathematicalConclusionsChanged=False)))
