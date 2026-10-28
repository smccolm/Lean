from pathlib import Path
from datetime import datetime, timezone
import json,re,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
names=[('SourceGammaOneFinitePeriodLattice','1075c'),('SourceGammaOneComplexTatePeriods','1076a'),('SourceGammaOnePeriodTateHecke','1077b'),('SourceGammaOneComplexTateHecke','1078a')]
mods=[n for n,a in names]
ns='Dubon2026.SourceFunctionField.GammaOne.'
ths=[];defs=[]
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
for n,a in names:
 t=(p/(n+'.lean')).read_text(encoding='utf-8')
 ths += [ns+x for x in re.findall(r'^theorem (\w+)',t,re.M)]
 defs += [ns+x for x in re.findall(r'^def (\w+)',t,re.M)]
 assert (p/(n+a+'.exit')).read_text().strip()=='0'
 assert (p/(n+a+'.log')).stat().st_size==0
roots=[ns+'complexPicardTatePeriodTensorEquiv_hecke',ns+'complexPicardTatePeriodTensorEquiv_symm_tmul']
edges=ths+defs+[ns+'picardPeriodEquiv_hecke',ns+'periodHeckeLinear_preserves_integralLattice',
ns+'picardPeriodEquiv_analytic_divisor','Dubon2026.TateModule.Period.phi2',
'Dubon2026.TateModule.Period.phi2_baseChange','Dubon2026.TateModule.ofAddEquiv',
'Dubon2026.sourceWeightTwoDualPeriod_mem','Dubon2026.sourceWeightTwoPeriodHom']

receipts=[
'source-gamma-one-analytic-abel-kernel-1-scratch-receipt.json',
'source-gamma-one-picard-period-equivalence-1d-scratch-receipt.json',
'source-gamma-one-hecke-analytic-maps-1-scratch-receipt.json',
'source-gamma-one-hecke-primitive-trace-1-scratch-receipt.json',
'source-gamma-one-holomorphic-h1-hecke-1-scratch-receipt.json',
'source-gamma-one-period-lattice-hecke-1b-scratch-receipt.json',
'source-gamma-one-hecke-geometric-fibers-1b-scratch-receipt.json','source-gamma-one-picard-period-hecke-1-scratch-receipt.json']
local=mods[:]
for f in receipts: local+=json.loads((p/f).read_text())['modules']
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,roots=roots,proofEdges=edges,localModules=list(dict.fromkeys(local)),separatelyAxiomChecked=[],compileEvidence={n:n+a for n,a in names})
def write(n,t):
 f=p/n
 assert not f.exists(),f
 f.write_text(t,encoding='utf-8')
write('source-gamma-one-complex-tate-hecke-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
imports='\n'.join('import '+n for n in mods)+'\nimport Mathlib.Tactic\n'
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
t=(p/'SourceGammaOneHeckeGeometricFibersAudit1b.lean').read_text(encoding='utf-8')
t=imports+t[t.index('\nopen Lean'):]
t=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in ths+defs),t,count=1)
for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:
 t=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]', 'let '+k+' : Array Name := '+arr(v),t)
t=re.sub(r'#lint in [^\n]+\n','',t).rstrip()+'\n\n'+'\n'.join('#lint in '+m for m in mods)+'\n'
t=t.replace('GAMMA ONE HECKE GEOMETRIC FIBERS','GAMMA ONE COMPLEX TATE HECKE').replace('Gamma One Hecke Geometric Fibers','Gamma One Complex Tate Hecke')
write('SourceGammaOneComplexTateHeckeAudit1.lean',t)
t=(p/'SourceGammaOneHeckeGeometricFibersDependencyAudit1b.lean').read_text(encoding='utf-8')
t=imports+t[t.index('\nopen Lean'):]
for k,v in [('roots',roots),('localModules',cfg['localModules']),('required',edges)]:
 t=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]', 'let '+k+' : Array Name := '+arr(v),t)
t=t.replace('GAMMA ONE HECKE GEOMETRIC FIBERS','GAMMA ONE COMPLEX TATE HECKE')
t=t.replace('actual intersection-curve orbit identification and exact stabilizer ramification VALUE closures. Actual coset-to-pullback multiplicity assembly and full Picard/parabolic/diamond/transpose/arithmetic comparisons remain','actual complex Picard Tate tensor equivalence, tensor formula and prime Hecke compatibility VALUE closures. Full parabolic/diamond/transpose/arithmetic comparisons and higher symmetric-power continuation remain')
write('SourceGammaOneComplexTateHeckeDependencyAudit1.lean',t)
t=(p/'SourceGammaOneHeckeGeometricFibersScratchOwnership1060b.lean').read_text(encoding='utf-8')
t=imports+t[t.index('\nopen Lean'):]
t=re.sub(r'let mods : Array Name := #\[[^\n]*\]', 'let mods : Array Name := '+arr(mods),t)
write('SourceGammaOneComplexTateHeckeScratchOwnership1079.lean',t)
reuse=[]
for f in receipts+['source-gamma-one-period-tate-route-1075.json']:
 reuse.append(dict(path=str(p/f),sha256=sha(p/f)))
ext=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
for f in ['SourceWeightTwoIntegralPeriods.lean','SourceIntegralCohomologyFinite.lean','SourceTateTorusBasis.lean','SourceTateTorusNaturality.lean','SourceTateEquivalences.lean']:
 reuse.append(dict(path=str(ext/f),sha256=sha(ext/f)))
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),
chain='DUB17 Theorem 2.6 / DUB18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> actual finite Gamma1 homogeneous-coefficient arithmetic realization -> actual Picard/Tate and H1 comparison -> original finite period lattice and complex Picard Tate tensor equivalence.',
reuseChecked=reuse,
shorterRoute='Native finite-index group finite generation and the exact period-image identity prove finiteness of the original integral lattice. Native torsion-free PID freeness supplies its finite basis. Reuse TateModule.ofAddEquiv, Period.phi2 and phi2_baseChange on the proved original Picard-period equivalence. No second lattice-discreteness proof or new Tate-module infrastructure is required for this exact tensor comparison.',
assumptionsToDischarge=['The original integer-period lattice is the actual modular-period image, finitely generated and free over the integers.','The actual complex Gamma1 Picard Tate module is the p-adic scalar extension of that same lattice, with the proved tensor formula.','The actual prime algebraic Hecke action corresponds to base change of the original integral-period Hecke action, with no coprimality condition on either prime.'],
remaining='Complex Picard Tate comparison only; no rank-2g or arithmetic Galois association is inferred from finite freeness. Arithmetic/complex torsion descent, finite-coefficient H1, diamond and transpose compatibility, original all-weight association and higher continuation remain. DUB17--20 OPEN; 16/20.')

write('source-gamma-one-complex-tate-hecke-audit-route-1079.json',json.dumps(route,indent=2)+'\n')
t=(p/'record_source_gamma_one_hecke_geometric_fibers_1060b.py').read_text(encoding='utf-8')
t=t.replace('source-gamma-one-hecke-geometric-fibers-1b','source-gamma-one-complex-tate-hecke-1').replace('source-gamma-one-hecke-geometric-fibers-audit-route-1060','source-gamma-one-complex-tate-hecke-audit-route-1079')
t=t.replace('SourceGammaOneHeckeGeometricFibersAudit1b','SourceGammaOneComplexTateHeckeAudit1').replace('SourceGammaOneHeckeGeometricFibersDependencyAudit1b','SourceGammaOneComplexTateHeckeDependencyAudit1').replace('SourceGammaOneHeckeGeometricFibersScratchOwnership1060b','SourceGammaOneComplexTateHeckeScratchOwnership1079')
t=t.replace('GAMMA ONE HECKE GEOMETRIC FIBERS','GAMMA ONE COMPLEX TATE HECKE')
t=t.replace('(9, 29, 41)',str((len(mods),len(ths+defs),len(edges))))
t=t.replace('all 41 required',f'all {len(edges)} required').replace('requiredProofValueEdges=41',f'requiredProofValueEdges={len(edges)}').replace('queries=29',f'queries={len(ths+defs)}').replace('proofEdges=41',f'proofEdges={len(edges)}')
t=t.replace('== 9','== 4').replace('linterScopes=9','linterScopes=4').replace('modules=9','modules=4')
write('record_source_gamma_one_complex_tate_hecke_1079.py',t)
t=(p/'audit_gamma_one_hecke_geometric_fibers_1060b.ps1').read_text(encoding='utf-8')
t=t.replace('SourceGammaOneHeckeGeometricFibersAudit1b','SourceGammaOneComplexTateHeckeAudit1').replace('SourceGammaOneHeckeGeometricFibersDependencyAudit1b','SourceGammaOneComplexTateHeckeDependencyAudit1').replace('SourceGammaOneHeckeGeometricFibersScratchOwnership1060b','SourceGammaOneComplexTateHeckeScratchOwnership1079').replace('record_source_gamma_one_hecke_geometric_fibers_1060b','record_source_gamma_one_complex_tate_hecke_1079')
write('audit_gamma_one_complex_tate_hecke_1079.ps1',t)
print(json.dumps(dict(modules=len(mods),theorems=len(ths),definitions=len(defs),edges=len(edges))))
