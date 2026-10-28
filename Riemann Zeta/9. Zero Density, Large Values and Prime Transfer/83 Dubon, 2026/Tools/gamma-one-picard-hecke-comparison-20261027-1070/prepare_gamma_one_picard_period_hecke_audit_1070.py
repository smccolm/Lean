from pathlib import Path
from datetime import datetime, timezone
import json,re,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
names=[
('SourceGammaOneCentralStabilizerCard','1061b'),
('SourceGammaOneHeckeActualStabilizers','1062b'),
('SourceGammaOneHeckeUpperOrbits','1063a'),
('SourceGammaOneHeckeCosetMultiplicity','1064b'),
('SourceGammaOneHeckeAnalyticDivisor','1065c'),
('SourceGammaOneAnalyticHeckeDivisors','1066a'),
('SourceGammaOnePicardHeckeDivisors','1067c'),
('SourceGammaOneEndpointHecke','1068a'),
('SourceGammaOnePicardPeriodHecke','1069a')]
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
roots=[ns+'picardPeriodEquiv_hecke']
edges=ths+defs+[ns+x for x in [
'HeckeFiberOrbits.analyticHeckePlace_eq_iff_orbit',
'HeckeFiberOrbits.two_mul_ramification_eq_stabilizer_card',
'heckeBeta_analytic_ramification',
'exists_analytic_place_of_restrict_heckeBeta',
'picardPeriodEquiv_analytic_divisor','analyticPicardHom_surjective',
'periodHeckeLinear_along','periodHeckeLinear_preserves_integralLattice',
'heckePicard_mk','periodValue_cuspHeckeTrace']]
receipts=[
'source-gamma-one-analytic-abel-kernel-1-scratch-receipt.json',
'source-gamma-one-picard-period-equivalence-1d-scratch-receipt.json',
'source-gamma-one-hecke-analytic-maps-1-scratch-receipt.json',
'source-gamma-one-hecke-primitive-trace-1-scratch-receipt.json',
'source-gamma-one-holomorphic-h1-hecke-1-scratch-receipt.json',
'source-gamma-one-period-lattice-hecke-1b-scratch-receipt.json',
'source-gamma-one-hecke-geometric-fibers-1b-scratch-receipt.json']
local=mods[:]
for f in receipts: local+=json.loads((p/f).read_text())['modules']
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,roots=roots,proofEdges=edges,localModules=list(dict.fromkeys(local)),separatelyAxiomChecked=[],compileEvidence={n:n+a for n,a in names})
def write(n,t):
 f=p/n
 assert not f.exists(),f
 f.write_text(t,encoding='utf-8')
write('source-gamma-one-picard-period-hecke-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
imports='\n'.join('import '+n for n in mods)+'\nimport Mathlib.Tactic\n'
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
t=(p/'SourceGammaOneHeckeGeometricFibersAudit1b.lean').read_text(encoding='utf-8')
t=imports+t[t.index('\nopen Lean'):]
t=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in ths+defs),t,count=1)
for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:
 t=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]', 'let '+k+' : Array Name := '+arr(v),t)
t=re.sub(r'#lint in [^\n]+\n','',t).rstrip()+'\n\n'+'\n'.join('#lint in '+m for m in mods)+'\n'
t=t.replace('GAMMA ONE HECKE GEOMETRIC FIBERS','GAMMA ONE PICARD PERIOD HECKE').replace('Gamma One Hecke Geometric Fibers','Gamma One Picard Period Hecke')
write('SourceGammaOnePicardPeriodHeckeAudit1.lean',t)
t=(p/'SourceGammaOneHeckeGeometricFibersDependencyAudit1b.lean').read_text(encoding='utf-8')
t=imports+t[t.index('\nopen Lean'):]
for k,v in [('roots',roots),('localModules',cfg['localModules']),('required',edges)]:
 t=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]', 'let '+k+' : Array Name := '+arr(v),t)
t=t.replace('GAMMA ONE HECKE GEOMETRIC FIBERS','GAMMA ONE PICARD PERIOD HECKE')
t=t.replace('actual intersection-curve orbit identification and exact stabilizer ramification VALUE closures. Actual coset-to-pullback multiplicity assembly and full Picard/parabolic/diamond/transpose/arithmetic comparisons remain','actual Picard-period prime Hecke compatibility VALUE closure. Full parabolic/diamond/transpose/arithmetic comparisons and higher symmetric-power continuation remain')
write('SourceGammaOnePicardPeriodHeckeDependencyAudit1.lean',t)
t=(p/'SourceGammaOneHeckeGeometricFibersScratchOwnership1060b.lean').read_text(encoding='utf-8')
t=imports+t[t.index('\nopen Lean'):]
t=re.sub(r'let mods : Array Name := #\[[^\n]*\]', 'let mods : Array Name := '+arr(mods),t)
write('SourceGammaOnePicardPeriodHeckeScratchOwnership1070.lean',t)
reuse=[]
for f in receipts+['source-gamma-one-hecke-coset-multiplicity-route-1062.json']:
 reuse.append(dict(path=str(p/f),sha256=sha(p/f)))
ext=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
for f in ['SourceGammaOneHeckePicard.lean','SourceWeightTwoEndpointPeriods.lean','SourceHeckeCosetFiberCount.lean']:
 reuse.append(dict(path=str(ext/f),sha256=sha(ext/f)))
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),
chain='DUB17 Theorem 2.6 / DUB18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> actual finite Gamma1 homogeneous-coefficient arithmetic realization -> full/parabolic, diamond, transpose and Picard/H1 comparison -> actual Picard-period Hecke compatibility.',
reuseChecked=reuse,
shorterRoute='Reuse native literal divisor pull/push and coset-stabilizer counting. Extend the single-place identity by Finsupp.addHom_ext and AddMonoidHom.ext_int. Native linearCombination and the original endpoint difference identity cancel the degree-zero basepoint term. Surjective actual analytic divisor presentation proves the existing Picard equivalence is Hecke-equivariant. No separate quotient-curve atlas, general correspondence functor or generalized basepoint infrastructure.',
assumptionsToDischarge=['Central-sign cancellation between exact stabilizer orders and actual beta ramification.','Literal prime beta pullback multiplicities equal the full coset multiplicities, including elliptic fibers.','Actual algebraic Hecke divisor/Picard action agrees with finite analytic coset summation.','Endpoint Hecke discrepancy equals divisor degree times an explicit basepoint vector; degree zero discharges it.','Original Picard-period equivalence intertwines the actual prime algebraic correspondence and dual native cusp trace.'],
remaining='Complex prime Hecke compatibility only. Full parabolic, diamond, transpose and arithmetic compatibility, original all-weight characteristic-zero association, arithmetic automorphy and literal higher symmetric-power continuation remain. DUB17--20 OPEN; 16/20.')
write('source-gamma-one-picard-period-hecke-audit-route-1070.json',json.dumps(route,indent=2)+'\n')
t=(p/'record_source_gamma_one_hecke_geometric_fibers_1060b.py').read_text(encoding='utf-8')
t=t.replace('source-gamma-one-hecke-geometric-fibers-1b','source-gamma-one-picard-period-hecke-1').replace('source-gamma-one-hecke-geometric-fibers-audit-route-1060','source-gamma-one-picard-period-hecke-audit-route-1070')
t=t.replace('SourceGammaOneHeckeGeometricFibersAudit1b','SourceGammaOnePicardPeriodHeckeAudit1').replace('SourceGammaOneHeckeGeometricFibersDependencyAudit1b','SourceGammaOnePicardPeriodHeckeDependencyAudit1').replace('SourceGammaOneHeckeGeometricFibersScratchOwnership1060b','SourceGammaOnePicardPeriodHeckeScratchOwnership1070')
t=t.replace('GAMMA ONE HECKE GEOMETRIC FIBERS','GAMMA ONE PICARD PERIOD HECKE')
t=t.replace('(9, 29, 41)',str((len(mods),len(ths+defs),len(edges))))
t=t.replace('all 41 required',f'all {len(edges)} required').replace('requiredProofValueEdges=41',f'requiredProofValueEdges={len(edges)}').replace('queries=29',f'queries={len(ths+defs)}').replace('proofEdges=41',f'proofEdges={len(edges)}')
write('record_source_gamma_one_picard_period_hecke_1070.py',t)
t=(p/'audit_gamma_one_hecke_geometric_fibers_1060b.ps1').read_text(encoding='utf-8')
t=t.replace('SourceGammaOneHeckeGeometricFibersAudit1b','SourceGammaOnePicardPeriodHeckeAudit1').replace('SourceGammaOneHeckeGeometricFibersDependencyAudit1b','SourceGammaOnePicardPeriodHeckeDependencyAudit1').replace('SourceGammaOneHeckeGeometricFibersScratchOwnership1060b','SourceGammaOnePicardPeriodHeckeScratchOwnership1070').replace('record_source_gamma_one_hecke_geometric_fibers_1060b','record_source_gamma_one_picard_period_hecke_1070')
write('audit_gamma_one_picard_period_hecke_1070.ps1',t)
print(json.dumps(dict(modules=len(mods),theorems=len(ths),definitions=len(defs),edges=len(edges))))
