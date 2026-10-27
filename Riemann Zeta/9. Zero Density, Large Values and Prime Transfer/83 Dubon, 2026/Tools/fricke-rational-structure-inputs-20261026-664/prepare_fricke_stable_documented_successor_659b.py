from pathlib import Path
import json
p=Path(r'E:\Lean\.tmp\dubon83')
mods=['SourceFrickeStableAlgebra','SourceFrickeStableGroup','SourceFrickeStableField','SourceFrickeStableEmbedding','SourceFrickeStableFraction','SourceFrickeStableMonic','SourceFrickeModularOrbit']
for m in mods:
 s=(p/(m+'.lean')).read_text(encoding='utf-8')
 for old in mods:s=s.replace('import '+old+'\n','import '+old+'V2\n')
 if m=='SourceFrickeStableAlgebra':s=s.replace('  S : Set (ℍ → ℂ)','  /-- The actual holomorphic functions generating the enlarged algebra. -/\n  S : Set (ℍ → ℂ)',1)
 f=p/(m+'V2.lean');assert not f.exists();f.write_text(s,encoding='utf-8')
for old,new in [('659','659b'),('660','660b')]:
 stem='prepare_fricke_stable_family_audit_' if old=='659' else 'prepare_fricke_orbit_monic_audit_'
 s=(p/(stem+old+'.py')).read_text(encoding='utf-8')
 for m in mods:s=s.replace("'"+m+"'","'"+m+"V2'")
 if old=='659':
  s=s.replace('source-fricke-stable-family-5-audit','source-fricke-stable-family-5b-audit').replace('SourceFrickeStableFamilyAudit5.lean','SourceFrickeStableFamilyAudit5b.lean').replace('SourceFrickeStableFamilyDependencyAudit5.lean','SourceFrickeStableFamilyDependencyAudit5b.lean')
 else:
  s=s.replace('source-fricke-orbit-monic-2-audit','source-fricke-orbit-monic-2b-audit').replace('SourceFrickeOrbitMonicAudit2.lean','SourceFrickeOrbitMonicAudit2b.lean').replace('SourceFrickeOrbitMonicDependencyAudit2.lean','SourceFrickeOrbitMonicDependencyAudit2b.lean').replace('fricke-orbit-monic-local-reuse-route-660.json','fricke-orbit-monic-local-reuse-route-660b.json').replace('fricke-stable-family-route-659.json','fricke-stable-family-route-659b.json')
 f=p/(stem+new+'.py');assert not f.exists();f.write_text(s,encoding='utf-8')
route=json.loads((p/'fricke-stable-family-route-659.json').read_text())
route['sourceSuccessor']='The original 73 exhaustive theorem checks passed; the full audit found only a missing documentation string on the actual generator-set projection LevelGens.S. V2 adds this documentation string and updates local imports; all mathematical declarations and proof bodies are preserved. The used predecessor source and audit evidence are retained.'
f=p/'fricke-stable-family-route-659b.json';assert not f.exists();f.write_text(json.dumps(route,indent=2)+'\n')
print(json.dumps(dict(modules=[m+'V2' for m in mods],proofBodiesChanged=False)))
