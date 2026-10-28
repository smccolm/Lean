from pathlib import Path
from datetime import datetime,timezone
import json,re,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
names=[('SourceGammaOneComplexConstantAutomorphisms', '1099a'), ('SourceGammaOneComplexTranslations', '1100a'), ('SourceGammaOneOffImageValues', '1101b'), ('SourceGammaOneTranslationOrbits', '1102b'), ('SourceGammaOneReducedRiemannRochSpace', '1103a'), ('SourceGammaOnePrincipalDivisors', '1104a'), ('SourceGammaOnePrincipalDivisorIdentities', '1105a'), ('SourceGammaOneFiniteTorsionAction', '1106b'), ('SourceGammaOneReducedDivisorInvariance', '1107a'), ('SourceGammaOneFixedReducedDivisor', '1108a'), ('SourceGammaOneInvariantSupport', '1109a'), ('SourceGammaOneTorsionDivisorDescent', '1110a'), ('SourceGammaOneTorsionComparison', '1111a'), ('SourceGammaOneTateComparison', '1112a'), ('SourceGammaOneArithmeticTatePeriods', '1113a')]
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
roots=[ns+'arithmetic_torsion_cardinality_period_rank',ns+'tateComplexEquiv_naturality',gns+'arithmeticPicardTatePeriodTensorEquiv',gns+'arithmeticPicardTatePeriodTensorEquiv_symm_tmul']
separate=[ns+'principal_inv',ns+'tateComplexEquiv_apply']
edges=[x for x in ths+defs if x not in separate]
edges+=['Dubon2026.SourceCurve.ConstantField.exists_reduced_space_of_nonempty','Dubon2026.SourceCurve.exists_pole_clearing_function_of_finite_coordinate','Dubon2026.SourceCurve.ConstantField.exists_translation_of_transcendental','Dubon2026.SourceFunctionField.OriginalConstantField.complex_translation_pow',ns+'complexPicardMap_injective',gns+'finite_complex_torsion',gns+'arithmeticPicardRep',gns+'arithmeticPlace_ord_action','Dubon2026.TateModule.tateEquivOfInjective',gns+'complexPicardTatePeriodTensorEquiv']
prior=json.loads((p/'source-gamma-one-arithmetic-picard-injectivity-1-audit-config.json').read_text())
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,roots=roots,proofEdges=edges,localModules=list(dict.fromkeys(mods+prior['localModules'])),separatelyAxiomChecked=separate,compileEvidence={n:n+a for n,a in names})
def write(n,t):
 f=p/n
 assert not f.exists(),f
 f.write_text(t,encoding='utf-8')
stem='source-gamma-one-arithmetic-torsion-tate-1'
write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
imports='\n'.join('import '+n for n in mods)+'\nimport Mathlib.Tactic\n'
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
t=(p/'SourceGammaOneHeckeGeometricFibersAudit1b.lean').read_text(encoding='utf-8')
t=imports+t[t.index('\nopen Lean'):]
t=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in ths+defs),t,count=1)
for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:
 t=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),t)
t=re.sub(r'#lint in [^\n]+\n','',t).rstrip()+'\n\n'+'\n'.join('#lint in '+m for m in mods)+'\n'
t=t.replace('GAMMA ONE HECKE GEOMETRIC FIBERS','GAMMA ONE ARITHMETIC TORSION TATE')
write('SourceGammaOneArithmeticTorsionTateAudit1.lean',t)
t=(p/'SourceGammaOneHeckeGeometricFibersDependencyAudit1b.lean').read_text(encoding='utf-8')
t=imports+t[t.index('\nopen Lean'):]
for k,v in [('roots',roots),('localModules',cfg['localModules']),('required',edges)]:
 t=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),t)
t=t.replace('GAMMA ONE HECKE GEOMETRIC FIBERS','GAMMA ONE ARITHMETIC TORSION TATE')
t=t.replace('actual intersection-curve orbit identification and exact stabilizer ramification VALUE closures. Actual coset-to-pullback multiplicity assembly and full Picard/parabolic/diamond/transpose/arithmetic comparisons remain','actual torsion descent, arithmetic Tate equivalence and original period tensor VALUE closures. General Tate naturality retains its explicit commuting-map premise; actual arithmetic Hecke and Galois realization remain')
write('SourceGammaOneArithmeticTorsionTateDependencyAudit1.lean',t)
t=(p/'SourceGammaOneHeckeGeometricFibersScratchOwnership1060b.lean').read_text(encoding='utf-8')
t=imports+t[t.index('\nopen Lean'):]
t=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),t)
write('SourceGammaOneArithmeticTorsionTateScratchOwnership1114.lean',t)
routes=['source-gamma-one-torsion-descent-route-1099.json','source-gamma-one-arithmetic-picard-injectivity-1-scratch-receipt.json','source-gamma-one-complex-tate-hecke-1-scratch-receipt.json']
reuse=[dict(path=str(p/f),sha256=sha(p/f)) for f in routes]
reuse+=json.loads((p/routes[0]).read_text())['reuseChecked']
ext=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
for n in ['SourceTateFunctor.lean','SourceOriginalTorsionDivisorDescent.lean','SourceOriginalTorsionComparison.lean','SourceOriginalTateComparison.lean']:
 reuse.append(dict(path=str(ext/n),sha256=sha(ext/n)))
reuse=list({row['path']:row for row in reuse}.values())
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain=json.loads((p/routes[0]).read_text())['chain'],reuseChecked=reuse,
shorterRoute='The existing coefficient automorphism restriction fixes actual arithmetic Gamma1 functions and their unique lifted places. Native finite-coordinate pole bounds and the reduced-space minimum give a unique reduced representative without a genus identification. Finite torsion gives factorial invariance. Native translations and unique coordinate values exclude nonarithmetic support, so literal conorm descends the divisor. Picard injectivity reflects torsion. Native tateEquivOfInjective then gives the arithmetic/complex Tate equivalence, composed with the already proved original period tensor equivalence.',
assumptionsToDischarge=['Actual complex constant automorphisms fix arithmetic functions and lifted places.','Finite torsion supplies a fixed reduced representative; its support consists of lifted arithmetic places.','Every nonzero-order actual complex Gamma1 torsion class has an arithmetic torsion preimage, and the actual arithmetic and complex torsion cardinalities agree.','The actual arithmetic Gamma1 Picard Tate module is p-adically linearly equivalent to the actual complex Tate module and to the p-adic extension of the original integral period lattice.'],
remaining='Actual arithmetic Hecke compatibility remains. The generic Tate naturality consumer is conditional on its explicit commuting-map equation, not a proof of that geometric equation. Finite-coefficient H1, diamond/transpose comparisons, arithmetic Galois realization, original all-weight association and higher symmetric-power continuation remain. No rank-versus-genus identity is asserted. DUB17--20 OPEN; 16/20.')
write('source-gamma-one-arithmetic-torsion-tate-audit-route-1114.json',json.dumps(route,indent=2)+'\n')
t=(p/'record_source_gamma_one_hecke_geometric_fibers_1060b.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-hecke-geometric-fibers-1b',stem),('source-gamma-one-hecke-geometric-fibers-audit-route-1060','source-gamma-one-arithmetic-torsion-tate-audit-route-1114'),('SourceGammaOneHeckeGeometricFibersAudit1b','SourceGammaOneArithmeticTorsionTateAudit1'),('SourceGammaOneHeckeGeometricFibersDependencyAudit1b','SourceGammaOneArithmeticTorsionTateDependencyAudit1'),('SourceGammaOneHeckeGeometricFibersScratchOwnership1060b','SourceGammaOneArithmeticTorsionTateScratchOwnership1114'),('GAMMA ONE HECKE GEOMETRIC FIBERS','GAMMA ONE ARITHMETIC TORSION TATE')]:
 t=t.replace(a,b)
t=t.replace('(9, 29, 41)',str((len(mods),len(ths+defs),len(edges))))
t=t.replace('all 41 required',f'all {len(edges)} required').replace('requiredProofValueEdges=41',f'requiredProofValueEdges={len(edges)}').replace('queries=29',f'queries={len(ths+defs)}').replace('proofEdges=41',f'proofEdges={len(edges)}')
t=t.replace('== 9',f'== {len(mods)}').replace('linterScopes=9',f'linterScopes={len(mods)}').replace('modules=9',f'modules={len(mods)}')
write('record_source_gamma_one_arithmetic_torsion_tate_1114.py',t)
t=(p/'audit_gamma_one_hecke_geometric_fibers_1060b.ps1').read_text(encoding='utf-8')
for a,b in [('SourceGammaOneHeckeGeometricFibersAudit1b','SourceGammaOneArithmeticTorsionTateAudit1'),('SourceGammaOneHeckeGeometricFibersDependencyAudit1b','SourceGammaOneArithmeticTorsionTateDependencyAudit1'),('SourceGammaOneHeckeGeometricFibersScratchOwnership1060b','SourceGammaOneArithmeticTorsionTateScratchOwnership1114'),('record_source_gamma_one_hecke_geometric_fibers_1060b','record_source_gamma_one_arithmetic_torsion_tate_1114')]:
 t=t.replace(a,b)
write('audit_gamma_one_arithmetic_torsion_tate_1114.ps1',t)
print(json.dumps(dict(modules=len(mods),theorems=len(ths),constructions=len(defs),queries=len(ths+defs),edges=len(edges))))
