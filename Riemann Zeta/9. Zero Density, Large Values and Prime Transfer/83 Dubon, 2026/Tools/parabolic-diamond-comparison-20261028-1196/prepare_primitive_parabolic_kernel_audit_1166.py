from pathlib import Path
from datetime import datetime,timezone
import json,re,hashlib
p=Path(__file__).parent
module='SourcePrimitiveParabolicCharacterKernel';attempt='1165b'
assert (p/(module+attempt+'.exit')).read_text().strip()=='0' and (p/(module+attempt+'.log')).stat().st_size==0
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
ths=['Dubon2026.sourcePrimitiveH1HeckeCharacter_zero_of_parabolic','Dubon2026.sourcePrimitiveFieldH1HeckeCharacter_zero_of_parabolic']
edges=ths+['Dubon2026.'+x for x in ['sourcePrimitiveIntegralParabolicHecke_relation','sourcePrimitiveH1HeckeCharacter_hecke','sourcePrimitiveH1HeckeCharacter','sourcePrimitiveFieldH1HeckeCharacter']]
prior=json.loads((p/'source-primitive-parabolic-relation-1-audit-config.json').read_text())
cfg=dict(modules=[module],theorems=ths,constructions=[],queries=ths,roots=ths,proofEdges=edges,localModules=[module]+prior['localModules'],separatelyAxiomChecked=[],compileEvidence={module:module+attempt})
def write(n,t):
 f=p/n;assert not f.exists(),f;f.write_text(t,encoding='utf-8')
stem='source-primitive-parabolic-kernel-1'
write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
imports='import '+module+'\nimport Mathlib.Tactic\n'
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
old='SourceParabolicRationalSpan';new='SourcePrimitiveParabolicKernel'
for suffix,newSuffix in [('Audit1','Audit1'),('DependencyAudit1','DependencyAudit1'),('ScratchOwnership1150','ScratchOwnership1166')]:
 t=(p/(old+suffix+'.lean')).read_text(encoding='utf-8');t=imports+t[t.index('\nopen Lean'):]
 if suffix=='Audit1':
  t=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in ths),t,count=1)
  for k,v in [('modules',[module]),('theorems',ths),('constructions',[])]:t=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),t)
  t=re.sub(r'#lint in [^\n]+\n','',t).rstrip()+'\n\n#lint in '+module+'\n'
 elif suffix=='DependencyAudit1':
  for k,v in [('roots',ths),('localModules',cfg['localModules']),('required',edges)]:t=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),t)
  t=t.replace('actual original primitive period-class rational parabolic span VALUE closure. Rational coordinates preserve actual local coboundaries. Uniform integral parabolic denominator clearing, integral spanning, finite character descent, diamonds and Galois realization remain','the already constructed original H1 Hecke character, in its literal Fourier coefficient field, vanishes on every operator annihilating integral parabolic H1. The proof realizes that operator by an actual integral Hecke word and uses the proved parabolic word relation. Finite character descent, diamonds and Galois realization remain')
 else:t=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr([module]),t)
 t=t.replace('PARABOLIC RATIONAL SPAN','PRIMITIVE PARABOLIC KERNEL').replace('Parabolic Rational Span','Primitive Parabolic Kernel')
 write(new+newSuffix+'.lean',t)
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
files=[r/'SourcePrimitiveIntegralH1Character.lean',r/'SourcePrimitiveH1CoefficientField.lean',r/'SourceHeckeWordTransport.lean',p/'source-primitive-parabolic-relation-1-scratch-receipt.json']
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain='DUB17/18 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight association -> original finite Gamma1 parabolic character -> the characteristic-zero kernel of the already constructed original coefficient-field H1 character.',reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in files],shorterRoute='Reuse the native adjoin/range identification for FreeAlgebra.lift and the original character values on prime generators. Realize each actual operator by a word, apply the proved integral parabolic word relation, and use the exact coefficient-field subtype. No new character, eigenclass, field embedding or operator algebra is substituted.',assumptionsToDischarge=['The existing original complex-valued H1 Hecke character annihilates every operator zero on integral parabolic H1.','The existing original Fourier-coefficient-field H1 Hecke character has the same kernel property.'],remaining='Finite congruence and descent to the actual finite parabolic Gamma1 operator image remain. This characteristic-zero relation is not finite-character descent. Diamonds, Galois realization, all-weight association, automorphy and higher symmetric-power continuation remain. DUB17--20 OPEN;16/20 unchanged.')
route['preservedFailures']='1165a rewrite through RingHom coercion was made explicit using change; failed source and log retained, no mathematical hypothesis changed.'
write('source-primitive-parabolic-kernel-audit-route-1166.json',json.dumps(route,indent=2)+'\n')
t=(p/'record_parabolic_rational_span_1150.py').read_text(encoding='utf-8')
for a,b in [('source-parabolic-rational-span-1',stem),('source-parabolic-rational-span-audit-route-1150','source-primitive-parabolic-kernel-audit-route-1166'),(old,new),('ScratchOwnership1150','ScratchOwnership1166'),('PARABOLIC RATIONAL SPAN','PRIMITIVE PARABOLIC KERNEL')]:t=t.replace(a,b)
t=t.replace('(3, 5, 10)','(1, 2, 6)').replace('all 10 required','all 6 required').replace('requiredProofValueEdges=10','requiredProofValueEdges=6').replace('proofEdges=10','proofEdges=6').replace('queries=5','queries=2').replace('== 3','== 1').replace('linterScopes=3','linterScopes=1').replace('modules=3','modules=1')
write('record_parabolic_character_kernel_1166.py',t)
t=(p/'audit_parabolic_rational_span_1150.ps1').read_text(encoding='utf-8')
for a,b in [(old,new),('ScratchOwnership1150','ScratchOwnership1166'),('record_parabolic_rational_span_1150','record_parabolic_character_kernel_1166')]:t=t.replace(a,b)
write('audit_parabolic_character_kernel_1166.ps1',t)
print(json.dumps(dict(modules=1,queries=2,edges=6)))
