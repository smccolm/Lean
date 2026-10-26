from pathlib import Path
import json,re,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
prod=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
ns='Dubon2026.SourceFunctionField.GammaOne.'
mods=['SourceGammaOneGeometricCohomology']
roots=[ns+n for n in ['geometricHeckeH1','geometricHeckeH1_eq','geometricBetaGroup_injective','geometricAlphaGroup_upper','geometricBetaGroup_matrix','geometricBetaGroup_smul']]
extra=['Dubon2026.originalCohomologyReindex','Dubon2026.originalCohomologyReindex_isIso','Dubon2026.sourceHeckeH1Trace','Dubon2026.sourceGammaOneConstantHeckeH1','groupCohomology.map_comp',ns+'heckeUpperGeometricEquiv',ns+'upperToGeometric_smul',ns+'upperToGeometric_matrix']
route=dict(chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero Galois association -> arithmetic realization of original finite Gamma1 Hecke characters -> geometric/H1 comparison retaining original homogeneous coefficients -> exact geometric group maps and their native H1 pullback/trace.',
 reuseChecked=[dict(path=str(prod/(m+'.lean')),sha256=sha(prod/(m+'.lean'))) for m in ['OriginalGroupCohomologyReindex','SourceGammaOneConstantHecke','SourceGammaOneHeckeSubgroup','SourceGammaOneSubgroupCohomologyMap']],
 primaryReview=dict(path=str(p/'gamma1-h1-geometric-reuse-assessment-628.json'),sha256=sha(p/'gamma1-h1-geometric-reuse-assessment-628.json')),
 selectedRoute='Use the audited actual upper/geometric subgroup isomorphism. The geometric inclusion and integral level-raising group maps are explicit and the latter is injective. Its analytic matrix/action identity follows from the existing original identity. Define its trace by the actual subgroup factorization and native cohomology reindexing. Native cohomology map composition proves exact equality with the original Gamma1 H1 Hecke operator for every explicit coefficient endomorphism, so the original homogeneous matrix action is retained.',
 assumptionsToDischarge='No group-map preservation, group injectivity, analytic intertwining, pullback composition or H1 operator-comparison hypothesis remains between these two literal cohomological correspondences.',
 remaining='The cohomological equality does not identify the actual Picard operator with H1. The full/parabolic distinction, transpose/diamond conventions, arithmetic Galois realization of finite characters, original all-weight characteristic-zero association, local/image/regularity, automorphy and literal higher continuation remain required. No characteristic-zero lift is inferred from finite characters. 16/20; DUB-17--20 OPEN.',
 productionStatus='Scratch development; audits and production promotion pending.',rootPinsChanged=False,proofLimitsChanged=False)
def out(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
out('gamma1-geometric-cohomology-route-629.json',json.dumps(route,indent=2)+'\n')
s=(p/'prepare_gamma_one_geometric_subgroup_audit_627.py').read_text(encoding='utf-8')
for k,v in [('mods',mods),('roots',roots),('extra',extra)]:s=re.sub(r'^'+k+'=.+$',lambda _,k=k,v=v:k+'='+repr(v),s,flags=re.M)
s=s.replace('source-gamma-one-geometric-subgroup-1','source-gamma-one-geometric-cohomology-1').replace('SourceGammaOneGeometricSubgroupAudit1','SourceGammaOneGeometricCohomologyAudit1').replace('SourceGammaOneGeometricSubgroupDependencyAudit1','SourceGammaOneGeometricCohomologyDependencyAudit1').replace('SOURCE GAMMA ONE GEOMETRIC SUBGROUP','SOURCE GAMMA ONE GEOMETRIC COHOMOLOGY').replace('gamma1-upper-geometric-correspondence-route-627.json','gamma1-geometric-cohomology-route-629.json')
a=s.index("dep=dep[:dep.index('  logInfo m!')]");b=s.index("\noutput('SourceGammaOneGeometricCohomologyDependencyAudit1",a)
msg='SOURCE GAMMA ONE GEOMETRIC COHOMOLOGY DEPENDENCY AUDIT PASS: all {required.size} required dependencies occur in the actual geometric Hecke H1 construction, its exact equality with the original operator and the actual group-map injection and analytic identities. Only declaration values are traversed. Native group-cohomology composition and the existing reindexing isomorphism are reused; the coefficient endomorphism is retained. Picard/H1, parabolic and diamond comparison, all-weight Galois realization and higher continuation remain required. 16/20; DUB-17--20 OPEN.'
s=s[:a]+"dep=dep[:dep.index('  logInfo m!')]+ "+repr('  logInfo m!"'+msg+'"\n\n#eval runPlanarPairingDependencyAudit\n')+s[b:]
out('prepare_gamma_one_geometric_cohomology_audit_629.py',s)
s=(p/'record_gamma_one_geometric_subgroup_627.py').read_text(encoding='utf-8')
s=s.replace('source-gamma-one-geometric-subgroup-1','source-gamma-one-geometric-cohomology-1').replace('SourceGammaOneGeometricSubgroupAudit1','SourceGammaOneGeometricCohomologyAudit1').replace('SourceGammaOneGeometricSubgroupDependencyAudit1','SourceGammaOneGeometricCohomologyDependencyAudit1').replace('SOURCE GAMMA ONE GEOMETRIC SUBGROUP','SOURCE GAMMA ONE GEOMETRIC COHOMOLOGY').replace('gamma1-upper-geometric-correspondence-route-627.json','gamma1-geometric-cohomology-route-629.json')
s=s.replace('==(1,8,15)','==(1,10,18)').replace('all 15 required proof dependencies','all 18 required dependencies').replace('requiredProofValueEdges=15','requiredProofValueEdges=18').replace('modules=1,queries=8','modules=1,queries=10').replace('proofEdges=15','proofEdges=18')
out('record_gamma_one_geometric_cohomology_629.py',s)
