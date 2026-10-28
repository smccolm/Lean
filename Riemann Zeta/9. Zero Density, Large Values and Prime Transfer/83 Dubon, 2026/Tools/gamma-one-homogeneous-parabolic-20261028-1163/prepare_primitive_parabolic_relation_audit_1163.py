from pathlib import Path
from datetime import datetime,timezone
import json,re,hashlib
p=Path(__file__).parent
module='SourcePrimitiveParabolicHeckeRelations';attempt='1162a'
assert (p/(module+attempt+'.exit')).read_text().strip()=='0' and (p/(module+attempt+'.log')).stat().st_size==0
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
ths=['Dubon2026.sourcePrimitiveIntegralParabolicHecke_relation']
edges=ths+['Dubon2026.'+x for x in ['sourcePrimitive_originalIntegralParabolic_span','sourceBinaryH1PrimeOperators_change','sourceHeckeWord_intertwine','sourceHeckeWord_eigenvector','sourcePrimitive_nonzero_integralModelComplexEigensystem']]
prior=json.loads((p/'source-original-integral-parabolic-1-audit-config.json').read_text())
cfg=dict(modules=[module],theorems=ths,constructions=[],queries=ths,roots=ths,proofEdges=edges,localModules=[module]+prior['localModules'],separatelyAxiomChecked=[],compileEvidence={module:module+attempt})
def write(n,t):
 f=p/n;assert not f.exists(),f;f.write_text(t,encoding='utf-8')
stem='source-primitive-parabolic-relation-1'
write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
imports='import '+module+'\nimport Mathlib.Tactic\n'
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
old='SourceParabolicRationalSpan';new='SourcePrimitiveParabolicRelation'
for suffix,newSuffix in [('Audit1','Audit1'),('DependencyAudit1','DependencyAudit1'),('ScratchOwnership1150','ScratchOwnership1163')]:
 t=(p/(old+suffix+'.lean')).read_text(encoding='utf-8');t=imports+t[t.index('\nopen Lean'):]
 if suffix=='Audit1':
  t=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in ths),t,count=1)
  for k,v in [('modules',[module]),('theorems',ths),('constructions',[])]:t=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),t)
  t=re.sub(r'#lint in [^\n]+\n','',t).rstrip()+'\n\n#lint in '+module+'\n'
 elif suffix=='DependencyAudit1':
  for k,v in [('roots',ths),('localModules',cfg['localModules']),('required',edges)]:t=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),t)
  t=t.replace('actual original primitive period-class rational parabolic span VALUE closure. Rational coordinates preserve actual local coboundaries. Uniform integral parabolic denominator clearing, integral spanning, finite character descent, diamonds and Galois realization remain','actual original Fourier character annihilates every integral Hecke word that vanishes on integral parabolic H1. The proof consumes the original nonzero period eigenclass, its integral parabolic span, and the native word intertwiner. Finite character descent, diamonds and Galois realization remain')
 else:t=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr([module]),t)
 t=t.replace('PARABOLIC RATIONAL SPAN','PRIMITIVE PARABOLIC RELATION').replace('Parabolic Rational Span','Primitive Parabolic Relation')
 write(new+newSuffix+'.lean',t)
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
files=[r/'SourcePrimitiveH1HeckeRelations.lean',r/'SourceHeckeWordTransport.lean',r/'SourceBinaryH1HeckeAlgebra.lean',p/'source-original-integral-parabolic-1-scratch-receipt.json']
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain='DUB17/18 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight association -> original finite Gamma1 parabolic character -> integral parabolic operator relations for the actual Fourier character.',reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in files],shorterRoute='Reuse the existing integral/complex Hecke-word intertwiner and actual original nonzero period eigenclass. Its proved integral parabolic span suffices to evaluate a word vanishing on that submodule. No new stable Hecke algebra or general corestriction-parabolicity theorem is required for this necessary relation edge.',assumptionsToDischarge=['The original Fourier character vanishes on every integral Hecke word annihilating actual integral parabolic H1; no vanishing on full integral H1 is assumed.'],remaining='Finite congruence and descent to the actual finite parabolic Gamma1 operator image remain. This characteristic-zero relation is not finite-character descent. Diamonds, Galois realization, all-weight association, automorphy and higher symmetric-power continuation remain. DUB17--20 OPEN;16/20 unchanged.')
write('source-primitive-parabolic-relation-audit-route-1163.json',json.dumps(route,indent=2)+'\n')
t=(p/'record_parabolic_rational_span_1150.py').read_text(encoding='utf-8')
for a,b in [('source-parabolic-rational-span-1',stem),('source-parabolic-rational-span-audit-route-1150','source-primitive-parabolic-relation-audit-route-1163'),(old,new),('ScratchOwnership1150','ScratchOwnership1163'),('PARABOLIC RATIONAL SPAN','PRIMITIVE PARABOLIC RELATION')]:t=t.replace(a,b)
t=t.replace('(3, 5, 10)','(1, 1, 6)').replace('all 10 required','all 6 required').replace('requiredProofValueEdges=10','requiredProofValueEdges=6').replace('proofEdges=10','proofEdges=6').replace('queries=5','queries=1').replace('== 3','== 1').replace('linterScopes=3','linterScopes=1').replace('modules=3','modules=1')
write('record_primitive_parabolic_relation_1163.py',t)
t=(p/'audit_parabolic_rational_span_1150.ps1').read_text(encoding='utf-8')
for a,b in [(old,new),('ScratchOwnership1150','ScratchOwnership1163'),('record_parabolic_rational_span_1150','record_primitive_parabolic_relation_1163')]:t=t.replace(a,b)
write('audit_primitive_parabolic_relation_1163.ps1',t)
print(json.dumps(dict(modules=1,queries=1,edges=6)))
