from pathlib import Path
from datetime import datetime, timezone
import json,re,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
names=[('SourceGammaOneRealPeriodH1Hecke','1071e'),('SourceGammaOneRealParabolicH1','1072a'),('SourceGammaOneRealParabolicHecke','1073b')]
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
roots=[ns+'realParabolicPeriodEquiv_cuspHeckeTrace']
edges=ths+defs+[ns+'periodValue_cuspHeckeTrace']+['Dubon2026.'+x for x in [
'sourceGamma1RealParabolicPeriodHom_surjective','sourceGamma1RealPeriodHom_injective',
'sourceGamma1_period_eq_zero_of_trace','sourceGammaOneConstantHeckeH1',
'sourceGammaOneConstantHeckeH1_hom_apply']]

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
write('source-gamma-one-real-parabolic-hecke-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
imports='\n'.join('import '+n for n in mods)+'\nimport Mathlib.Tactic\n'
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
t=(p/'SourceGammaOneHeckeGeometricFibersAudit1b.lean').read_text(encoding='utf-8')
t=imports+t[t.index('\nopen Lean'):]
t=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in ths+defs),t,count=1)
for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:
 t=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]', 'let '+k+' : Array Name := '+arr(v),t)
t=re.sub(r'#lint in [^\n]+\n','',t).rstrip()+'\n\n'+'\n'.join('#lint in '+m for m in mods)+'\n'
t=t.replace('GAMMA ONE HECKE GEOMETRIC FIBERS','GAMMA ONE REAL PARABOLIC HECKE').replace('Gamma One Hecke Geometric Fibers','Gamma One Real Parabolic Hecke')
write('SourceGammaOneRealParabolicHeckeAudit1.lean',t)
t=(p/'SourceGammaOneHeckeGeometricFibersDependencyAudit1b.lean').read_text(encoding='utf-8')
t=imports+t[t.index('\nopen Lean'):]
for k,v in [('roots',roots),('localModules',cfg['localModules']),('required',edges)]:
 t=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]', 'let '+k+' : Array Name := '+arr(v),t)
t=t.replace('GAMMA ONE HECKE GEOMETRIC FIBERS','GAMMA ONE REAL PARABOLIC HECKE')
t=t.replace('actual intersection-curve orbit identification and exact stabilizer ramification VALUE closures. Actual coset-to-pullback multiplicity assembly and full Picard/parabolic/diamond/transpose/arithmetic comparisons remain','actual native real parabolic H1 period equivalence and Hecke compatibility VALUE closure. Full parabolic/diamond/transpose/arithmetic comparisons and higher symmetric-power continuation remain')
write('SourceGammaOneRealParabolicHeckeDependencyAudit1.lean',t)
t=(p/'SourceGammaOneHeckeGeometricFibersScratchOwnership1060b.lean').read_text(encoding='utf-8')
t=imports+t[t.index('\nopen Lean'):]
t=re.sub(r'let mods : Array Name := #\[[^\n]*\]', 'let mods : Array Name := '+arr(mods),t)
write('SourceGammaOneRealParabolicHeckeScratchOwnership1074.lean',t)
reuse=[]
for f in receipts+['source-gamma-one-real-parabolic-hecke-route-1071.json','source-gamma-one-real-h1-direct-route-1071d.json']:
 reuse.append(dict(path=str(p/f),sha256=sha(p/f)))
ext=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
for f in ['SourceGammaOneRealPeriodSurjectivity.lean','SourceGammaOneRealParabolicPeriods.lean','SourceGammaOneConstantHecke.lean']:
 reuse.append(dict(path=str(ext/f),sha256=sha(ext/f)))
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),
chain='DUB17 Theorem 2.6 / DUB18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> actual finite Gamma1 homogeneous-coefficient arithmetic realization -> full/parabolic H1 comparison -> native real parabolic H1 equivalence and Hecke stability.',
reuseChecked=reuse,
shorterRoute='Reuse native real-period surjectivity and injectivity, the exact trace-square-four parabolic criterion, and the audited holomorphic H1 proof directly over real periods. The actual native H1 Hecke correspondence is restricted only after proving stability from the range equality. Failed extra character-coordinate constructions are preserved and not retained as active Lean modules; no proof limits were changed.',
assumptionsToDischarge=['The range of the actual real cusp-period map is exactly native trace-square-four parabolic H1.','That map is injective and gives an actual real linear equivalence.','The native H1 Hecke operator preserves the actual parabolic submodule for every nonzero index.','The actual real-period equivalence intertwines the restricted native Hecke correspondence.'],
remaining='Real scalar parabolic H1 comparison only. Complex/full coefficient, diamond, transpose and arithmetic comparisons, original all-weight characteristic-zero association and higher symmetric-power continuation remain. DUB17--20 OPEN; 16/20.')

write('source-gamma-one-real-parabolic-hecke-audit-route-1074.json',json.dumps(route,indent=2)+'\n')
t=(p/'record_source_gamma_one_hecke_geometric_fibers_1060b.py').read_text(encoding='utf-8')
t=t.replace('source-gamma-one-hecke-geometric-fibers-1b','source-gamma-one-real-parabolic-hecke-1').replace('source-gamma-one-hecke-geometric-fibers-audit-route-1060','source-gamma-one-real-parabolic-hecke-audit-route-1074')
t=t.replace('SourceGammaOneHeckeGeometricFibersAudit1b','SourceGammaOneRealParabolicHeckeAudit1').replace('SourceGammaOneHeckeGeometricFibersDependencyAudit1b','SourceGammaOneRealParabolicHeckeDependencyAudit1').replace('SourceGammaOneHeckeGeometricFibersScratchOwnership1060b','SourceGammaOneRealParabolicHeckeScratchOwnership1074')
t=t.replace('GAMMA ONE HECKE GEOMETRIC FIBERS','GAMMA ONE REAL PARABOLIC HECKE')
t=t.replace('(9, 29, 41)',str((len(mods),len(ths+defs),len(edges))))
t=t.replace('all 41 required',f'all {len(edges)} required').replace('requiredProofValueEdges=41',f'requiredProofValueEdges={len(edges)}').replace('queries=29',f'queries={len(ths+defs)}').replace('proofEdges=41',f'proofEdges={len(edges)}')
t=t.replace('== 9','== 3').replace('linterScopes=9','linterScopes=3').replace('modules=9','modules=3')
write('record_source_gamma_one_real_parabolic_hecke_1074.py',t)
t=(p/'audit_gamma_one_hecke_geometric_fibers_1060b.ps1').read_text(encoding='utf-8')
t=t.replace('SourceGammaOneHeckeGeometricFibersAudit1b','SourceGammaOneRealParabolicHeckeAudit1').replace('SourceGammaOneHeckeGeometricFibersDependencyAudit1b','SourceGammaOneRealParabolicHeckeDependencyAudit1').replace('SourceGammaOneHeckeGeometricFibersScratchOwnership1060b','SourceGammaOneRealParabolicHeckeScratchOwnership1074').replace('record_source_gamma_one_hecke_geometric_fibers_1060b','record_source_gamma_one_real_parabolic_hecke_1074')
write('audit_gamma_one_real_parabolic_hecke_1074.ps1',t)
print(json.dumps(dict(modules=len(mods),theorems=len(ths),definitions=len(defs),edges=len(edges))))
