from pathlib import Path
from datetime import datetime,timezone
import ast,json,re,hashlib
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
mods=['SourceSupportedCharacterFiber','SourceSupportedCharacterDivisibility','SourceParabolicHeckeSpan','SourceParabolicHeckeCongruence','SourceParabolicAdicOperatorKernel']
attempts=['1170b','1171a','1172f','1173d','1174b']
ev={m:m+a for m,a in zip(mods,attempts)}
for m in mods:
 assert (p/(ev[m]+'.exit')).read_text().strip()=='0' and (p/(ev[m]+'.log')).stat().st_size==0,m
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
ths=[];defs=[]
for m in mods:
 code=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',(p/(m+'.lean')).read_text(encoding='utf-8'),flags=re.S))
 ths+=['Dubon2026.'+x for x in re.findall(r'^theorem\s+(\w+)',code,re.M)]
 defs+=['Dubon2026.'+x for x in re.findall(r'^(?:def|abbrev)\s+(\w+)',code,re.M)]
assert (len(mods),len(ths),len(defs))==(5,8,1),(ths,defs)
edges=ths+defs+['Dubon2026.'+x for x in ['sourcePrimitiveFieldH1HeckeCharacter_zero_of_parabolic','sourcePrimitiveH1HeckeCharacter_zero_of_parabolic','sourcePrimitiveIntegralParabolicHecke_relation','sourcePrimitive_originalIntegralParabolic_span','sourceFiniteIntegralSubmodule_saturation','sourceBinaryH1HeckeWord_surjective','sourceBinaryH1HeckeWord_change','sourceBinaryH1PrimeOperators_commute','sourceBinaryH1Change_zmod_nonzero_eq_zero_iff','sourceIntegralBinaryH1Finite','sourcePrimitiveH1AdicQuotientCharacter','sourcePrimitiveLocalH1HeckeCharacter_coe']]+['Module.mem_support_iff_of_finite','Module.mem_support_iff_nontrivial_residueField_tensorProduct','isIntegral_of_smul_mem_submodule']
prior=json.loads((p/'source-primitive-parabolic-kernel-1-audit-config.json').read_text(encoding='utf-8'))
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,roots=ths+defs,proofEdges=edges,localModules=list(dict.fromkeys(mods+['SourceFiniteIntegralSaturation']+prior['localModules'])),separatelyAxiomChecked=[],compileEvidence=ev)
def write(n,t):
 f=p/n;assert not f.exists(),f;f.write_text(t,encoding='utf-8')
stem='source-supported-parabolic-congruence-1b'
write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
old='SourcePrimitiveParabolicKernel';new='SourceSupportedParabolicCongruence'
for a,b in [('Audit1','Audit1b'),('DependencyAudit1','DependencyAudit1b'),('ScratchOwnership1166','ScratchOwnership1175b')]:
 s=(p/(old+a+'.lean')).read_text(encoding='utf-8')
 s='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+s[s.index('\nopen Lean'):]
 if a=='Audit1':
  s=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in cfg['queries']),s,count=1)
  for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:s=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),s)
  s=re.sub(r'#lint in [^\n]+\n','',s).rstrip()+'\n\n'+''.join('#lint in '+m+'\n' for m in mods)
 elif a=='DependencyAudit1':
  for k,v in [('roots',cfg['roots']),('localModules',cfg['localModules']),('required',edges)]:s=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),s)
  start=s.index(' occur in the ');end=s.index('; DUB17--20 OPEN.',start)
  s=s[:start]+' occur in the actual original Fourier character support, finite Hecke span, integral congruence and prime-power adic kernel proofs away from one fixed nonzero integer. Finite Gamma1 parabolic transfer and exceptional primes remain'+s[end:]
 else:s=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),s)
 s=s.replace('PRIMITIVE PARABOLIC KERNEL','SUPPORTED PARABOLIC CONGRUENCE').replace('Primitive Parabolic Kernel','Supported Parabolic Congruence')
 write(new+b+'.lean',s)
route=json.loads((p/'source-supported-character-reuse-1170.json').read_text(encoding='utf-8'))
route['recordedUTC']=datetime.now(timezone.utc).isoformat()
for f in [r/'SourceBinaryPermutationHeckeWords.lean',r/'SourcePrimitiveH1AdicOperatorKernel.lean']:
 route['reuseChecked'].append(dict(path=str(f),sha256=sha(f)))
route['assumptionsToDischarge']+=['The same original compatible adic quotient character kills every operator zero modulo p^(n+1) on original integral parabolic H1, for every n and every prime coprime to one fixed nonzero integer.']
route['preservedFailures']='1170a missing source before preparation; 1172a--d explicit canonical Z-module/coercion and induction repairs; 1173a--b replaced unavailable scalar-tower inference by the same underlying additive subgroup with its actual Z action. All failed sources retained as .lean.txt with logs. No altered mathematical conclusion or raised limits. The first audit found only a missing definition docstring. Its exact source and log are preserved; 1172f adds that docstring and 1173d/1174b recompile dependents.'
write('source-supported-parabolic-congruence-audit-route-1175b.json',json.dumps(route,indent=2)+'\n')
s=(p/'record_parabolic_character_kernel_1166.py').read_text(encoding='utf-8')
for a,b in [('source-primitive-parabolic-kernel-audit-route-1166','source-supported-parabolic-congruence-audit-route-1175b'),('source-primitive-parabolic-kernel-1',stem),(old,new),('ScratchOwnership1166','ScratchOwnership1175b'),('PRIMITIVE PARABOLIC KERNEL','SUPPORTED PARABOLIC CONGRUENCE')]:s=s.replace(a,b)
s=s.replace('(1, 2, 6)',str((len(mods),len(cfg['queries']),len(edges)))).replace('== 1','== 5').replace('all 6 required',f'all {len(edges)} required').replace('linterScopes=1','linterScopes=5').replace('requiredProofValueEdges=6',f'requiredProofValueEdges={len(edges)}').replace('modules=1','modules=5').replace('queries=2','queries=9').replace('proofEdges=6',f'proofEdges={len(edges)}')
s=s.replace(new+'Audit1',new+'Audit1b').replace(new+'DependencyAudit1',new+'DependencyAudit1b')
ast.parse(s);write('record_supported_parabolic_congruence_1175b.py',s)
s=(p/'audit_parabolic_character_kernel_1166.ps1').read_text(encoding='utf-8')
for a,b in [(old,new),('ScratchOwnership1166','ScratchOwnership1175b'),('record_parabolic_character_kernel_1166','record_supported_parabolic_congruence_1175b')]:s=s.replace(a,b)
s=s.replace(new+'Audit1',new+'Audit1b').replace(new+'DependencyAudit1',new+'DependencyAudit1b')
write('audit_supported_parabolic_congruence_1175b.ps1',s)
print(json.dumps(dict(modules=len(mods),queries=len(cfg['queries']),edges=len(edges))))
