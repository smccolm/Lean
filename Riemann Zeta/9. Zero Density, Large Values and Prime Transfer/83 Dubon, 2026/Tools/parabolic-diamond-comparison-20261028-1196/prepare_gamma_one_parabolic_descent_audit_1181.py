from pathlib import Path
from datetime import datetime,timezone
import ast,json,re,hashlib
p=Path(__file__).parent
mods=['SourceGammaOneParabolicOperatorAlgebra','SourceGammaOneParabolicTateKernel','SourceGammaOneParabolicTransferCriterion','SourceParabolicCongruenceException','SourceGammaOneParabolicCharacterTransfer']
attempts=['1176a','1177d','1179b','1180a','1178d']
ev={m:m+a for m,a in zip(mods,attempts)}
for m in mods:
 assert (p/(ev[m]+'.exit')).read_text().strip()=='0' and (p/(ev[m]+'.log')).stat().st_size==0,m
ths=[];defs=[]
for m in mods:
 code=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',(p/(m+'.lean')).read_text(encoding='utf-8'),flags=re.S))
 ns='Dubon2026.SourceFunctionField.GammaOne.' if m in mods[:2] else 'Dubon2026.'
 ths += [ns+x for x in re.findall(r'^theorem\s+(\w+)',code,re.M)]
 defs += [ns+x for x in re.findall(r'^(?:def|abbrev)\s+(\w+)',code,re.M)]
assert (len(ths),len(defs))==(8,4),(ths,defs)
edges=ths+defs+['Dubon2026.'+x for x in ['sourcePrimitiveParabolicH1AdicQuotientCharacter_zero_away','sourcePrimitiveParabolicHecke_congruence_integral_away','sourceGammaOneOriginalHeckeWord_change','sourceGammaOneHeckeWord_transfer','sourceGammaOneConstantH1_finite','sourceFiniteOperatorCharacterDescend','sourceFiniteOperatorCharacterDescend_comp']]+['Dubon2026.SourceFunctionField.GammaOne.'+x for x in ['binaryParabolicH1_hecke_mem','binaryTateH1Equiv_word','binaryTateH1Equiv','binaryTatePrimeOperators']]
prior=json.loads((p/'source-supported-parabolic-congruence-1b-audit-config.json').read_text(encoding='utf-8'))
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,roots=ths+defs,proofEdges=edges,localModules=list(dict.fromkeys(mods+prior['localModules'])),separatelyAxiomChecked=[],compileEvidence=ev)
def write(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
stem='source-gamma-one-parabolic-descent-1'
write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
old='SourceSupportedParabolicCongruence';new='SourceGammaOneParabolicDescent'
for a,b in [('Audit1b','Audit1'),('DependencyAudit1b','DependencyAudit1'),('ScratchOwnership1175b','ScratchOwnership1181')]:
 s=(p/(old+a+'.lean')).read_text(encoding='utf-8')
 s='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+s[s.index('\nopen Lean'):]
 if a=='Audit1b':
  s=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in cfg['queries']),s,count=1)
  for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:s=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),s)
  s=re.sub(r'#lint in [^\n]+\n','',s).rstrip()+'\n\n'+''.join('#lint in '+m+'\n' for m in mods)
 elif a=='DependencyAudit1b':
  for k,v in [('roots',cfg['roots']),('localModules',cfg['localModules']),('required',edges)]:s=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),s)
  start=s.index(' occur in the ');end=s.index('; DUB17--20 OPEN.',start)
  s=s[:start]+' occur in the actual finite Gamma1 parabolic operator image, arithmetic Tate word-kernel comparison and explicitly conditional original-character descent. Exact parabolic transfer preimages and exceptional primes remain unresolved'+s[end:]
 else:s=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),s)
 s=s.replace('SUPPORTED PARABOLIC CONGRUENCE','GAMMA ONE PARABOLIC DESCENT').replace('Supported Parabolic Congruence','Gamma One Parabolic Descent')
 write(new+b+'.lean',s)
route=json.loads((p/'source-parabolic-operator-reuse-1176.json').read_text(encoding='utf-8'))
route['recordedUTC']=datetime.now(timezone.utc).isoformat()
route['assumptionsToDischarge']=route['dischargedTargets']
route['remaining']=route['boundary']+' Explicit hypothesis: '+route['unresolvedInput']
route['preservedFailures']='1177a--c untargeted rewrites exhausted the default limit; explicit fixed-argument comparison removes them. 1178a,c cumulative elaboration was decomposed by naming the already proved uniform exceptional integer; no bound is increased.1178b mixed scratch/production imports, repaired in1179b. All failed sources and logs retained;1180 names the same existential witness, uniformly in E,tau,p,n.'
write('source-gamma-one-parabolic-descent-audit-route-1181.json',json.dumps(route,indent=2)+'\n')
s=(p/'record_supported_parabolic_congruence_1175b.py').read_text(encoding='utf-8')
for a,b in [('source-supported-parabolic-congruence-audit-route-1175b','source-gamma-one-parabolic-descent-audit-route-1181'),('source-supported-parabolic-congruence-1b',stem),(old,new),('Audit1b','Audit1'),('ScratchOwnership1175b','ScratchOwnership1181'),('SUPPORTED PARABOLIC CONGRUENCE','GAMMA ONE PARABOLIC DESCENT')]:s=s.replace(a,b)
s=s.replace('(5, 9, 24)',str((5,12,len(edges)))).replace('queries=9','queries=12').replace('all 24 required',f'all {len(edges)} required').replace('requiredProofValueEdges=24',f'requiredProofValueEdges={len(edges)}').replace('proofEdges=24',f'proofEdges={len(edges)}')
ast.parse(s);write('record_gamma_one_parabolic_descent_1181.py',s)
s=(p/'audit_supported_parabolic_congruence_1175b.ps1').read_text(encoding='utf-8')
for a,b in [(old,new),('Audit1b','Audit1'),('ScratchOwnership1175b','ScratchOwnership1181'),('record_supported_parabolic_congruence_1175b','record_gamma_one_parabolic_descent_1181')]:s=s.replace(a,b)
write('audit_gamma_one_parabolic_descent_1181.ps1',s)
print(json.dumps(dict(modules=5,queries=12,edges=len(edges))))
