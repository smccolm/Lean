from pathlib import Path
from datetime import datetime,timezone
import ast,json,re
p=Path(__file__).parent
module='SourceFiniteIntegralSaturation';attempt='1167e'
assert (p/(module+attempt+'.exit')).read_text().strip()=='0' and (p/(module+attempt+'.log')).stat().st_size==0
ths=['Dubon2026.sourceFiniteIntegralSubmodule_saturation']
edges=ths+['Submodule.annihilator_top_inter_nonZeroDivisors']
cfg=dict(modules=[module],theorems=ths,constructions=[],queries=ths,roots=ths,proofEdges=edges,localModules=[module],separatelyAxiomChecked=[],compileEvidence={module:module+attempt})
def write(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
stem='source-integral-saturation-1'
write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
old='SourcePrimitiveParabolicKernel';new='SourceIntegralSaturation'
for a,b in [('Audit1','Audit1'),('DependencyAudit1','DependencyAudit1'),('ScratchOwnership1166','ScratchOwnership1183')]:
 s=(p/(old+a+'.lean')).read_text(encoding='utf-8')
 s='import '+module+'\nimport Mathlib.Tactic\n'+s[s.index('\nopen Lean'):]
 if a=='Audit1':
  s=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in ths),s,count=1)
  for k,v in [('modules',[module]),('theorems',ths),('constructions',[])]:s=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),s)
  s=re.sub(r'#lint in [^\n]+\n','',s).rstrip()+'\n\n#lint in '+module+'\n'
 elif a=='DependencyAudit1':
  for k,v in [('roots',ths),('localModules',[module]),('required',edges)]:s=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),s)
  start=s.index(' occur in the ');end=s.index('; DUB17--20 OPEN.',start)
  s=s[:start]+' occur in the fixed torsion-annihilator saturation proof required by the original parabolic Hecke-span congruence. Exceptional primes and finite Gamma1 lifting remain'+s[end:]
 else:s=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr([module]),s)
 s=s.replace('PRIMITIVE PARABOLIC KERNEL','INTEGRAL SATURATION').replace('Primitive Parabolic Kernel','Integral Saturation')
 write(new+b+'.lean',s)
route=json.loads((p/'source-parabolic-saturation-reuse-1167.json').read_text(encoding='utf-8'))
route['recordedUTC']=datetime.now(timezone.utc).isoformat()
route['chain']='DUB17/18 -> original all-weight association -> finite Gamma1 parabolic character -> original parabolic operator congruence -> scalar saturation inside the actual integral Hecke span.'
route['assumptionsToDischarge']=['A finite integral module modulo a submodule has a single nonzero torsion annihilator; every coprime nonzero scalar can therefore be divided inside that submodule.']
route['scope']='Only the generic saturation lemma is promoted because the actual Hecke-span congruence directly consumes it. The separately audited SourceParabolicReductionKernel theorem remains archived scratch work and is deferred; it is not required by the shorter route. No source theorem or acceptance gate is weakened.'
write('source-integral-saturation-audit-route-1183.json',json.dumps(route,indent=2)+'\n')
s=(p/'record_parabolic_character_kernel_1166.py').read_text(encoding='utf-8')
for a,b in [('source-primitive-parabolic-kernel-audit-route-1166','source-integral-saturation-audit-route-1183'),('source-primitive-parabolic-kernel-1',stem),(old,new),('ScratchOwnership1166','ScratchOwnership1183'),('PRIMITIVE PARABOLIC KERNEL','INTEGRAL SATURATION')]:s=s.replace(a,b)
s=s.replace('(1, 2, 6)','(1, 1, 2)').replace('queries=2','queries=1').replace('all 6 required','all 2 required').replace('requiredProofValueEdges=6','requiredProofValueEdges=2').replace('proofEdges=6','proofEdges=2')
ast.parse(s);write('record_integral_saturation_1183.py',s)
s=(p/'audit_parabolic_character_kernel_1166.ps1').read_text(encoding='utf-8')
for a,b in [(old,new),('ScratchOwnership1166','ScratchOwnership1183'),('record_parabolic_character_kernel_1166','record_integral_saturation_1183')]:s=s.replace(a,b)
write('audit_integral_saturation_1183.ps1',s)
