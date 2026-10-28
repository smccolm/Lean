from pathlib import Path
from datetime import datetime,timezone
import json,re,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
names=[('SourceGammaOneHeckeConstantField', '1115a'), ('SourceGammaOneHeckeSpanSeparation', '1116a'), ('SourceGammaOneHeckeValuationExtension', '1117a'), ('SourceGammaOneHeckeConstantPlaces', '1118a'), ('SourceGammaOneHeckeConorm', '1119a'), ('SourceGammaOneHeckeComplexPlaces', '1120b'), ('SourceGammaOneHeckeComplexDivisors', '1121d'), ('SourceGammaOneHeckeComplexPicard', '1122c'), ('SourceGammaOneArithmeticTateHecke', '1123a')]
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
ns='Dubon2026.SourceFunctionField.GammaOne.ConstantField.'
gns='Dubon2026.SourceFunctionField.GammaOne.'
hns=gns+'HeckeConstantField.'
roots=[gns+'arithmeticPicardTatePeriodTensorEquiv_hecke',gns+'tateComplexEquiv_hecke']
separate=[hns+x for x in ['fieldMap_j','complexAlgebra','fieldAlgebra','complexFieldAlgebra','complexScalarTower','arithmeticFieldScalarTower']]
edges=[x for x in ths+defs if x not in separate]
edges+=['Dubon2026.SourceCurve.Place.comap_restrictAlong_eq_of_commute','Dubon2026.SourceCurve.Place.ord_restrictAlong',gns+'heckeAlpha_coefficientMap',gns+'heckeBeta_coefficientMap',ns+'tateComplexEquiv_naturality',gns+'complexPicardTatePeriodTensorEquiv_hecke',gns+'periodHeckeLinear_preserves_integralLattice',gns+'picardPeriodEquiv_hecke']
prior=json.loads((p/'source-gamma-one-arithmetic-torsion-tate-1b-audit-config.json').read_text())
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,roots=roots,proofEdges=edges,localModules=list(dict.fromkeys(mods+prior['localModules'])),separatelyAxiomChecked=separate,compileEvidence={n:n+a for n,a in names})
def write(n,t):
 f=p/n
 assert not f.exists(),f
 f.write_text(t,encoding='utf-8')
stem='source-gamma-one-arithmetic-hecke-1'
write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
imports='\n'.join('import '+n for n in mods)+'\nimport Mathlib.Tactic\n'
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
t=(p/'SourceGammaOneHeckeGeometricFibersAudit1b.lean').read_text(encoding='utf-8')
t=imports+t[t.index('\nopen Lean'):]
t=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in ths+defs),t,count=1)
for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:
 t=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),t)
t=re.sub(r'#lint in [^\n]+\n','',t).rstrip()+'\n\n'+'\n'.join('#lint in '+m for m in mods)+'\n'
t=t.replace('GAMMA ONE HECKE GEOMETRIC FIBERS','GAMMA ONE ARITHMETIC HECKE')
write('SourceGammaOneArithmeticHeckeAudit1.lean',t)
t=(p/'SourceGammaOneHeckeGeometricFibersDependencyAudit1b.lean').read_text(encoding='utf-8')
t=imports+t[t.index('\nopen Lean'):]
for k,v in [('roots',roots),('localModules',cfg['localModules']),('required',edges)]:
 t=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),t)
t=t.replace('GAMMA ONE HECKE GEOMETRIC FIBERS','GAMMA ONE ARITHMETIC HECKE')
t=t.replace('actual intersection-curve orbit identification and exact stabilizer ramification VALUE closures. Actual coset-to-pullback multiplicity assembly and full Picard/parabolic/diamond/transpose/arithmetic comparisons remain','actual arithmetic Picard Hecke, Tate Hecke and original period tensor Hecke VALUE closures. All commuting-map premises are discharged for the actual degeneracy maps. Finite-coefficient H1, diamond, transpose and Galois realization remain')
write('SourceGammaOneArithmeticHeckeDependencyAudit1.lean',t)
t=(p/'SourceGammaOneHeckeGeometricFibersScratchOwnership1060b.lean').read_text(encoding='utf-8')
t=imports+t[t.index('\nopen Lean'):]
t=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),t)
write('SourceGammaOneArithmeticHeckeScratchOwnership1124.lean',t)
routes=['source-gamma-one-arithmetic-hecke-route-1115.json','source-gamma-one-arithmetic-torsion-tate-1b-scratch-receipt.json','source-gamma-one-arithmetic-picard-injectivity-1-scratch-receipt.json','source-gamma-one-complex-tate-hecke-1-scratch-receipt.json']
reuse=[dict(path=str(p/f),sha256=sha(p/f)) for f in routes]
reuse+=json.loads((p/routes[0]).read_text())['reuseChecked']
ext=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
for n in ['SourceCurvePicardCorrespondence.lean','SourceConstantFieldExtensionOrders.lean','SourceGammaOneHeckeFieldFinite.lean']:
 reuse.append(dict(path=str(ext/n),sha256=sha(ext/n)))
reuse=list({row['path']:row for row in reuse}.values())
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain=json.loads((p/routes[0]).read_text())['chain'],reuseChecked=reuse,
shorterRoute='The native fieldCoefficientMap and actual alpha/beta coefficient identities supply the commuting field squares. Only unique place extension, exact orders and finite-support conorm are needed for the intersection field; no Picard descent or period theory is rebuilt there. Existing finite-map restriction and ramification formulas give divisor naturality. Explicit equality composition handles the definitionally equal field presentations. Actual geometric Picard naturality discharges the Tate commuting-map premise, and the proved complex period Hecke comparison supplies the original tensor action.',
assumptionsToDischarge=['The actual Hecke intersection curve has unique complex extensions of arithmetic places with exact orders.','The literal conorm commutes with actual beta pullback and alpha pushforward; actual arithmetic and complex Picard Hecke operators intertwine.','The actual arithmetic-to-complex Tate equivalence intertwines every nonzero-index original Hecke operator.','At every prime Hecke index, the actual arithmetic Picard Tate module identifies with the p-adic tensor of the original period lattice, with the native dual cusp Hecke action, without requiring either prime to avoid the level.'],
remaining='Finite-coefficient H1, full/parabolic and diamond/transpose comparisons, coefficient-field and Frobenius/inertia realizations, original all-weight association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain. DUB17--20 OPEN; 16/20.',
preservedFailures='1120a old consumer name; 1121a/b/c incomplete universe elaboration with four local field notations, followed by 1121d explicit identical field types and the explicit correspondence import; 1122a missing helper declarations and 1122b alias rewriting, followed by 1122c explicit equality composition. Used source snapshots and logs are preserved. No mathematical hypothesis or statement was weakened, and proof limits are unchanged.')
write('source-gamma-one-arithmetic-hecke-audit-route-1124.json',json.dumps(route,indent=2)+'\n')
t=(p/'record_source_gamma_one_hecke_geometric_fibers_1060b.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-hecke-geometric-fibers-1b',stem),('source-gamma-one-hecke-geometric-fibers-audit-route-1060','source-gamma-one-arithmetic-hecke-audit-route-1124'),('SourceGammaOneHeckeGeometricFibersAudit1b','SourceGammaOneArithmeticHeckeAudit1'),('SourceGammaOneHeckeGeometricFibersDependencyAudit1b','SourceGammaOneArithmeticHeckeDependencyAudit1'),('SourceGammaOneHeckeGeometricFibersScratchOwnership1060b','SourceGammaOneArithmeticHeckeScratchOwnership1124'),('GAMMA ONE HECKE GEOMETRIC FIBERS','GAMMA ONE ARITHMETIC HECKE')]:
 t=t.replace(a,b)
t=t.replace('(9, 29, 41)',str((len(mods),len(ths+defs),len(edges))))
t=t.replace('all 41 required',f'all {len(edges)} required').replace('requiredProofValueEdges=41',f'requiredProofValueEdges={len(edges)}').replace('queries=29',f'queries={len(ths+defs)}').replace('proofEdges=41',f'proofEdges={len(edges)}')
t=t.replace('== 9',f'== {len(mods)}').replace('linterScopes=9',f'linterScopes={len(mods)}').replace('modules=9',f'modules={len(mods)}')
write('record_source_gamma_one_arithmetic_hecke_1124.py',t)
t=(p/'audit_gamma_one_hecke_geometric_fibers_1060b.ps1').read_text(encoding='utf-8')
for a,b in [('SourceGammaOneHeckeGeometricFibersAudit1b','SourceGammaOneArithmeticHeckeAudit1'),('SourceGammaOneHeckeGeometricFibersDependencyAudit1b','SourceGammaOneArithmeticHeckeDependencyAudit1'),('SourceGammaOneHeckeGeometricFibersScratchOwnership1060b','SourceGammaOneArithmeticHeckeScratchOwnership1124'),('record_source_gamma_one_hecke_geometric_fibers_1060b','record_source_gamma_one_arithmetic_hecke_1124')]:
 t=t.replace(a,b)
write('audit_gamma_one_arithmetic_hecke_1124.ps1',t)
print(json.dumps(dict(modules=len(mods),theorems=len(ths),constructions=len(defs),queries=len(ths+defs),edges=len(edges))))
