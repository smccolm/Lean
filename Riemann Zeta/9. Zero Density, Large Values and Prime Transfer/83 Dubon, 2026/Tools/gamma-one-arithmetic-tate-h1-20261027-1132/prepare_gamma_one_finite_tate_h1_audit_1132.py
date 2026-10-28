from pathlib import Path
from datetime import datetime, timezone
import json,re,hashlib
p=Path(__file__).parent
names=[('SourceGammaOneIntegralCharacterFactor','1125b'),('SourceGammaOneFiniteParabolicCharacters','1126b'),('SourceGammaOneFiniteParabolicH1','1127a'),('SourceGammaOneFiniteParabolicHecke','1128b'),('SourceGammaOneArithmeticPeriodInclusion','1129a'),('SourceGammaOneArithmeticTateFiniteH1','1130a'),('SourceGammaOneArithmeticTateFiniteHecke','1131a')]
mods=[n for n,a in names]
ths=[];defs=[]
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
for n,a in names:
 t=(p/(n+'.lean')).read_text(encoding='utf-8')
 ns=re.search(r'^namespace (\S+)',t,re.M)[1]+'.'
 ths += [ns+x for x in re.findall(r'^theorem (\w+)',t,re.M)]
 defs += [ns+x for x in re.findall(r'^(?:def|abbrev) (\w+)',t,re.M)]
 assert (p/(n+a+'.exit')).read_text().strip()=='0'
 assert (p/(n+a+'.log')).stat().st_size==0
ns='Dubon2026.SourceFunctionField.GammaOne.'
roots=[ns+x for x in ['arithmeticTateFiniteH1Equiv_hecke_restrict','arithmeticTateFiniteH1Equiv_hom_apply','arithmeticTateFiniteH1Equiv','finiteParabolicHecke']]
separate=[ns+'finiteLatticeCharacterEquiv_apply']
edges=[x for x in ths+defs if x not in separate]
edges += ['Dubon2026.sourceGamma1_integral_parabolic_character_lift','Dubon2026.sourceGamma1_exists_cuspForm_of_real_parabolic_character','Dubon2026.sourceGammaOneConstantHeckeH1_hom_apply']
edges += [ns+x for x in ['arithmeticPicardTatePeriodTensorEquiv_hecke','arithmeticPicardTatePeriodTensorEquiv','periodHeckeLinear_dualPeriod','integralLattice_eq_dualPeriodHom_range']]
prior=json.loads((p/'source-gamma-one-arithmetic-hecke-1-audit-config.json').read_text())
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,roots=roots,proofEdges=edges,localModules=list(dict.fromkeys(mods+prior['localModules'])),separatelyAxiomChecked=separate,compileEvidence={n:n+a for n,a in names})
def write(n,t):
 f=p/n;assert not f.exists(),f
 f.write_text(t,encoding='utf-8')
stem='source-gamma-one-finite-tate-h1-1'
write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
imports='\n'.join('import '+n for n in mods)+'\nimport Mathlib.Tactic\n'
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
old='SourceGammaOneArithmeticHecke'
new='SourceGammaOneFiniteTateH1'
for suffix in ['Audit1','DependencyAudit1','ScratchOwnership1124']:
 t=(p/(old+suffix+'.lean')).read_text(encoding='utf-8')
 t=imports+t[t.index('\nopen Lean'):]
 if suffix=='Audit1':
  t=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in ths+defs),t,count=1)
  for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:
   t=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),t)
  t=re.sub(r'#lint in [^\n]+\n','',t).rstrip()+'\n\n'+'\n'.join('#lint in '+m for m in mods)+'\n'
 elif suffix=='DependencyAudit1':
  for k,v in [('roots',roots),('localModules',cfg['localModules']),('required',edges)]:
   t=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),t)
  t=t.replace('actual arithmetic Picard Hecke, Tate Hecke and original period tensor Hecke VALUE closures. All commuting-map premises are discharged for the actual degeneracy maps. Finite-coefficient H1, diamond, transpose and Galois realization remain','actual arithmetic finite Tate dual/native H1 equivalence and Hecke transpose VALUE closures. Parabolic and finite-order vanishing define the explicit H1 target. Full/parabolic passage, homogeneous coefficients, diamond and Galois realization remain')
 else:
  t=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),t)
 t=t.replace('GAMMA ONE ARITHMETIC HECKE','GAMMA ONE FINITE TATE H1').replace('Gamma One Hecke Geometric Fibers','Gamma One Finite Tate H1')
 write(new+suffix.replace('1124','1132')+'.lean',t)
routes=['source-gamma-one-finite-parabolic-route-1125.json','source-gamma-one-arithmetic-dual-reuse-1129.json','source-gamma-one-arithmetic-hecke-1-scratch-receipt.json']
reuse=[dict(path=str(p/f),sha256=sha(p/f)) for f in routes]
reuse+=json.loads((p/routes[0]).read_text())['reuseChecked']
native=json.loads((p/routes[1]).read_text());reuse.append(dict(path=native['source'],sha256=native['sha256']))
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain=json.loads((p/routes[0]).read_text())['chain'],reuseChecked=reuse,
 shorterRoute='The actual real-period surjectivity kills the kernel of the period map for integer parabolic characters. The existing integral lift then factors finite characters that vanish on parabolic and finite-order elements. Native H1 character equivalence realizes that literal submodule. The actual coset trace gives Hecke transpose. Native IsBaseChange lifts the dual from the integral lattice to the actual arithmetic Tate module using the already proved arithmetic period equivalence. No second integral Poincare-duality proof or tensor-coordinate argument is needed.',
 assumptionsToDischarge=['Every integer parabolic character factors through the actual integral-period lattice.','Every modulus character trivial on parabolic and finite-order elements is uniquely a character of that lattice.','The literal native finite H1 submodule with those conditions equals the lattice dual and is stable under every nonzero-index native Hecke operator.','The actual arithmetic Picard Tate module dual modulo p^n is equivalent to that native H1 submodule, and actual prime Picard Hecke duals intertwine the existing H1 Hecke operator, including primes dividing the level.'],
 remaining='The H1 target explicitly retains parabolic and finite-order vanishing. Full/parabolic passage, discharge of finite-order vanishing for the application, homogeneous coefficients, diamonds, coefficient/Frobenius/inertia realization, original all-weight characteristic-zero association and higher symmetric-power continuation remain. DUB17--20 OPEN; 16/20.',
 preservedFailures='1125a lattice coercions, 1126a explicit smul binder, 1128a rewrite of native character application; immutable sources and diagnostics retained before correction. No source proposition or proof limit changed.')
write('source-gamma-one-finite-tate-h1-audit-route-1132.json',json.dumps(route,indent=2)+'\n')
t=(p/'record_source_gamma_one_arithmetic_hecke_1124.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-arithmetic-hecke-1',stem),('source-gamma-one-arithmetic-hecke-audit-route-1124','source-gamma-one-finite-tate-h1-audit-route-1132'),(old,new),('ScratchOwnership1124','ScratchOwnership1132'),('GAMMA ONE ARITHMETIC HECKE','GAMMA ONE FINITE TATE H1')]:t=t.replace(a,b)
t=t.replace('(9, 36, 38)',str((len(mods),len(ths+defs),len(edges))))
t=t.replace('all 38 required',f'all {len(edges)} required').replace('requiredProofValueEdges=38',f'requiredProofValueEdges={len(edges)}').replace('proofEdges=38',f'proofEdges={len(edges)}').replace('queries=36',f'queries={len(ths+defs)}')
t=t.replace('== 9',f'== {len(mods)}').replace('linterScopes=9',f'linterScopes={len(mods)}').replace('modules=9',f'modules={len(mods)}')
write('record_source_gamma_one_finite_tate_h1_1132.py',t)
t=(p/'audit_gamma_one_arithmetic_hecke_1124.ps1').read_text(encoding='utf-8')
for a,b in [(old,new),('ScratchOwnership1124','ScratchOwnership1132'),('record_source_gamma_one_arithmetic_hecke_1124','record_source_gamma_one_finite_tate_h1_1132')]:t=t.replace(a,b)
write('audit_gamma_one_finite_tate_h1_1132.ps1',t)
print(json.dumps(dict(modules=len(mods),theorems=len(ths),constructions=len(defs),queries=len(ths+defs),edges=len(edges))))
