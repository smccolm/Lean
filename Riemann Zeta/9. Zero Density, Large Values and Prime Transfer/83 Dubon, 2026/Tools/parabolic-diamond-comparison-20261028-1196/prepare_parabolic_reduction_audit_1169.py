from pathlib import Path
import ast,json,re,hashlib
from datetime import datetime,timezone
p=Path(__file__).parent
mods=['SourceFiniteIntegralSaturation','SourceParabolicReductionKernel']
ev=dict(zip(mods,['SourceFiniteIntegralSaturation1167e','SourceParabolicReductionKernel1168a']))
for m in mods:
 assert (p/(ev[m]+'.exit')).read_text().strip()=='0' and (p/(ev[m]+'.log')).stat().st_size==0
ths=['Dubon2026.sourceFiniteIntegralSubmodule_saturation','Dubon2026.sourceIntegralParabolicH1_reduction_kernel_away']
edges=ths+['Submodule.annihilator_top_inter_nonZeroDivisors','Dubon2026.sourceBinaryH1Change_zmod_nonzero_eq_zero_iff','Dubon2026.sourceIntegralBinaryH1Finite']
prior=json.loads((p/'source-original-parabolic-entry-1b-audit-config.json').read_text(encoding='utf-8'))
cfg=dict(modules=mods,theorems=ths,constructions=[],queries=ths,roots=ths,proofEdges=edges,localModules=mods+prior['localModules'],separatelyAxiomChecked=[],compileEvidence=ev)
def write(n,t):
 f=p/n;assert not f.exists(),f;f.write_text(t,encoding='utf-8')
stem='source-parabolic-reduction-kernel-1'
write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
old='SourcePrimitiveParabolicKernel';new='SourceParabolicReductionKernel'
for a,b in [('Audit1','Audit1'),('DependencyAudit1','DependencyAudit1'),('ScratchOwnership1166','ScratchOwnership1169')]:
 s=(p/(old+a+'.lean')).read_text(encoding='utf-8')
 s='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+s[s.index('\nopen Lean'):]
 if a=='Audit1':
  s=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in ths),s,count=1)
  for k,v in [('modules',mods),('theorems',ths),('constructions',[])]:s=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),s)
  s=re.sub(r'#lint in [^\n]+\n','',s).rstrip()+'\n\n'+''.join('#lint in '+m+'\n' for m in mods)
 elif a=='DependencyAudit1':
  for k,v in [('roots',ths),('localModules',cfg['localModules']),('required',edges)]:s=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),s)
  s=re.sub(r'logInfo "Scope: [^\n]+', 'logInfo "Scope: finite integral quotient torsion annihilator and exact native parabolic reduction kernel away from one fixed integer. Exceptional primes and finite character descent remain."',s)
 else:s=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),s)
 s=s.replace('PRIMITIVE PARABOLIC KERNEL','PARABOLIC REDUCTION KERNEL').replace('Primitive Parabolic Kernel','Parabolic Reduction Kernel')
 write(new+b+'.lean',s)
route=json.loads((p/'source-parabolic-saturation-reuse-1167.json').read_text(encoding='utf-8'))
route['recordedUTC']=datetime.now(timezone.utc).isoformat()
route['assumptionsToDischarge']=['For each finite integral module and submodule, scalar saturation holds away from a single nonzero torsion annihilator.','For actual original integral parabolic H1, reduction modulo every nonzero modulus coprime to that annihilator has exactly the scalar-multiple kernel within parabolic H1.']
route['preservedFailures']='1167a--d preserved as noncompiling .lean.txt with logs; finite quotient instance and canonical integral action made explicit. No altered goal or raised limit.'
write('source-parabolic-reduction-kernel-audit-route-1169.json',json.dumps(route,indent=2)+'\n')
s=(p/'record_parabolic_character_kernel_1166.py').read_text(encoding='utf-8')
for a,b in [('source-primitive-parabolic-kernel-audit-route-1166','source-parabolic-reduction-kernel-audit-route-1169'),('source-primitive-parabolic-kernel-1',stem),(old,new),('ScratchOwnership1166','ScratchOwnership1169'),('PRIMITIVE PARABOLIC KERNEL','PARABOLIC REDUCTION KERNEL')]:s=s.replace(a,b)
s=s.replace('(1, 2, 6)','(2, 2, 5)').replace('== 1','== 2').replace('all 6 required','all 5 required').replace('linterScopes=1','linterScopes=2').replace('requiredProofValueEdges=6','requiredProofValueEdges=5').replace('modules=1','modules=2').replace('proofEdges=6','proofEdges=5')
ast.parse(s);write('record_parabolic_reduction_kernel_1169.py',s)
s=(p/'audit_parabolic_character_kernel_1166.ps1').read_text(encoding='utf-8')
for a,b in [(old,new),('ScratchOwnership1166','ScratchOwnership1169'),('record_parabolic_character_kernel_1166','record_parabolic_reduction_kernel_1169')]:s=s.replace(a,b)
write('audit_parabolic_reduction_kernel_1169.ps1',s)
print(json.dumps(dict(modules=2,queries=2,edges=5)))
