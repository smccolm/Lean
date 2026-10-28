from pathlib import Path
from datetime import datetime,timezone
import json,re,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
names=[('SourceGammaOneComplexCoefficientMap','1080b'),('SourceGammaOneComplexFieldExtension','1081b'),('SourceGammaOneComplexFieldIndependence','1082a'),('SourceGammaOneComplexSpanSeparation','1083a'),('SourceGammaOneConstantFieldValuationExtension','1084a'),('SourceGammaOneConstantFieldPlaces','1085a'),('SourceGammaOneExtendedPlaceMap','1086a'),('SourceGammaOneDivisorConorm','1087a'),('SourceGammaOneComplexPicardMap','1088a'),('SourceGammaOneComplexTorsionFinite','1089a'),('SourceGammaOneDegreeBaseChange','1090a'),('SourceGammaOneNewCoordinatePlaces','1091a'),('SourceGammaOneComplexCoordinateBasis','1092a'),('SourceGammaOneComplexCoordinateTrace','1093a'),('SourceGammaOneCoordinateDescent','1094a'),('SourceGammaOneComplexSpanDescent','1095a'),('SourceGammaOnePrincipalDescent','1096a'),('SourceGammaOneComplexPicardInjectivity','1097a')]
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
roots=[ns+'finite_arithmetic_torsion']
separate=[ns+x for x in ['fieldMap_linearIndependent','liftPlace_unique','forall_ne_liftPlace_of_comap_ne','forall_comap_ne_of_ne_liftPlace','conorm_single','complexAlgebra','fieldAlgebra','complexFieldAlgebra','complexScalarTower','arithmeticFieldScalarTower']]
edges=[x for x in ths+defs if x not in separate]
edges+=['Dubon2026.SourceCurve.ConstantField.extension_order_and_unique','Dubon2026.SourceCurve.ConstantField.exists_extending_valuation_of_proper_ideal','Dubon2026.SourceFunctionField.mem_span_of_coeffMap_mem_span','Dubon2026.SourceFunctionField.DegreeTransport.relfinrank_eq_of_finite','Dubon2026.SourceCurve.ConstantField.exists_coordinate_basis_of_finrank_eq','Dubon2026.SourceCurve.ConstantField.mem_span_of_coordinate_regular','Dubon2026.SourceCurve.ConstantField.eq_sum_trace_mul','Dubon2026.SourceCurve.ConstantField.ord_sum_le','Dubon2026.SourceFunctionField.GammaOne.picardPeriodEquiv','Dubon2026.ComplexLatticeTorsion.natCard_torsion_quotient']
prior=json.loads((p/'source-gamma-one-complex-tate-hecke-1-audit-config.json').read_text())
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,roots=roots,proofEdges=edges,localModules=list(dict.fromkeys(mods+prior['localModules'])),separatelyAxiomChecked=separate,compileEvidence={n:n+a for n,a in names})
def write(n,t):
 f=p/n
 assert not f.exists(),f
 f.write_text(t,encoding='utf-8')
stem='source-gamma-one-arithmetic-picard-injectivity-1'
write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
imports='\n'.join('import '+n for n in mods)+'\nimport Mathlib.Tactic\n'
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
t=(p/'SourceGammaOneHeckeGeometricFibersAudit1b.lean').read_text(encoding='utf-8')
t=imports+t[t.index('\nopen Lean'):]
t=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in ths+defs),t,count=1)
for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:
 t=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),t)
t=re.sub(r'#lint in [^\n]+\n','',t).rstrip()+'\n\n'+'\n'.join('#lint in '+m for m in mods)+'\n'
t=t.replace('GAMMA ONE HECKE GEOMETRIC FIBERS','GAMMA ONE ARITHMETIC PICARD INJECTIVITY')
write('SourceGammaOneArithmeticPicardInjectivityAudit1.lean',t)
t=(p/'SourceGammaOneHeckeGeometricFibersDependencyAudit1b.lean').read_text(encoding='utf-8')
t=imports+t[t.index('\nopen Lean'):]
for k,v in [('roots',roots),('localModules',cfg['localModules']),('required',edges)]:
 t=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),t)
t=t.replace('GAMMA ONE HECKE GEOMETRIC FIBERS','GAMMA ONE ARITHMETIC PICARD INJECTIVITY')
t=t.replace('actual intersection-curve orbit identification and exact stabilizer ramification VALUE closures. Actual coset-to-pullback multiplicity assembly and full Picard/parabolic/diamond/transpose/arithmetic comparisons remain','actual arithmetic torsion finiteness VALUE closure through the original complex Picard map, principal descent and exact place orders. Torsion surjectivity, arithmetic Tate and Galois realization remain')
write('SourceGammaOneArithmeticPicardInjectivityDependencyAudit1.lean',t)
t=(p/'SourceGammaOneHeckeGeometricFibersScratchOwnership1060b.lean').read_text(encoding='utf-8')
t=imports+t[t.index('\nopen Lean'):]
t=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),t)
write('SourceGammaOneArithmeticPicardInjectivityScratchOwnership1098.lean',t)
routes=['source-gamma-one-arithmetic-complex-route-1080.json','source-gamma-one-span-descent-reuse-1083.json','source-gamma-one-principal-descent-route-1090.json','source-gamma-one-complex-tate-hecke-1-scratch-receipt.json']
reuse=[dict(path=str(p/f),sha256=sha(p/f)) for f in routes]
for f in routes[:3]:
 reuse+=json.loads((p/f).read_text())['reuseChecked']
reuse=list({row['path']:row for row in reuse}.values())
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain=json.loads((p/routes[0]).read_text())['chain'],reuseChecked=reuse,
shorterRoute='Native coefficient-span retraction, constant-field valuation extension and exact orders apply to the literal Gamma1 fields. Existing Laurent coordinate degree transport supplies corresponding bases without a new independence proof. Native coordinate trace descent and independent-coefficient order bounds prove principal descent; degree-zero effective differences vanish. The already proved complex period equivalence supplies finite torsion; no rank-versus-genus identity is needed. The separately checked coefficient-independence lemma is not a dependency of the chosen shorter coordinate-basis route; no expansion of that alternative is planned.',
assumptionsToDischarge=['Actual coefficient embedding, compatible scalar towers and generation of the complex Gamma1 field.','Unique complex extension of every actual arithmetic place with exact orders; actual divisor conorm preserves degree and principal divisors.','The actual Gamma1 coordinate-basis and trace-descent inputs to principal-divisor descent.','Every arithmetic Gamma1 divisor becoming principal over C is already principal over Qbar.','The actual arithmetic-to-complex Picard map is injective and actual nonzero-order arithmetic torsion is finite.'],
remaining='Torsion surjectivity, arithmetic Tate/Hecke comparison, finite-coefficient H1 and diamond/transpose comparisons, arithmetic Galois realization, all-weight association and higher symmetric-power continuation remain. DUB17--20 OPEN; 16/20.')
write('source-gamma-one-arithmetic-picard-injectivity-audit-route-1098.json',json.dumps(route,indent=2)+'\n')
t=(p/'record_source_gamma_one_hecke_geometric_fibers_1060b.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-hecke-geometric-fibers-1b',stem),('source-gamma-one-hecke-geometric-fibers-audit-route-1060','source-gamma-one-arithmetic-picard-injectivity-audit-route-1098'),('SourceGammaOneHeckeGeometricFibersAudit1b','SourceGammaOneArithmeticPicardInjectivityAudit1'),('SourceGammaOneHeckeGeometricFibersDependencyAudit1b','SourceGammaOneArithmeticPicardInjectivityDependencyAudit1'),('SourceGammaOneHeckeGeometricFibersScratchOwnership1060b','SourceGammaOneArithmeticPicardInjectivityScratchOwnership1098'),('GAMMA ONE HECKE GEOMETRIC FIBERS','GAMMA ONE ARITHMETIC PICARD INJECTIVITY')]:
 t=t.replace(a,b)
t=t.replace('(9, 29, 41)',str((len(mods),len(ths+defs),len(edges))))
t=t.replace('all 41 required',f'all {len(edges)} required').replace('requiredProofValueEdges=41',f'requiredProofValueEdges={len(edges)}').replace('queries=29',f'queries={len(ths+defs)}').replace('proofEdges=41',f'proofEdges={len(edges)}')
t=t.replace('== 9',f'== {len(mods)}').replace('linterScopes=9',f'linterScopes={len(mods)}').replace('modules=9',f'modules={len(mods)}')
write('record_source_gamma_one_arithmetic_picard_injectivity_1098.py',t)
t=(p/'audit_gamma_one_hecke_geometric_fibers_1060b.ps1').read_text(encoding='utf-8')
for a,b in [('SourceGammaOneHeckeGeometricFibersAudit1b','SourceGammaOneArithmeticPicardInjectivityAudit1'),('SourceGammaOneHeckeGeometricFibersDependencyAudit1b','SourceGammaOneArithmeticPicardInjectivityDependencyAudit1'),('SourceGammaOneHeckeGeometricFibersScratchOwnership1060b','SourceGammaOneArithmeticPicardInjectivityScratchOwnership1098'),('record_source_gamma_one_hecke_geometric_fibers_1060b','record_source_gamma_one_arithmetic_picard_injectivity_1098')]:
 t=t.replace(a,b)
write('audit_gamma_one_arithmetic_picard_injectivity_1098.ps1',t)
print(json.dumps(dict(modules=len(mods),theorems=len(ths),constructions=len(defs),queries=len(ths+defs),edges=len(edges))))
