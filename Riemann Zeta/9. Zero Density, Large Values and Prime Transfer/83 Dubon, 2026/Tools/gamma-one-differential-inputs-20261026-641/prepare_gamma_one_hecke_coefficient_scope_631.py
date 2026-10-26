from pathlib import Path
import json,re,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
prod=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
ns='Dubon2026.SourceFunctionField.GammaOne.'
mods=['SourceGammaOneHeckeCoefficientAction']
roots=[ns+'geometricHeckeH1_coefficient',ns+'constantCoefficientH1']
extra=['Dubon2026.sourceGammaOneConstantHeckeH1_cocycle','groupCohomology.H1π_comp_map_apply',ns+'geometricHeckeH1_eq','Rep.trivialFunctor']
route=dict(chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> higher symmetric continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> finite Gamma1 character arithmetic realization -> geometric/H1 comparison -> retention and exact factorization of the original homogeneous coefficient endomorphism.',
 reuseChecked=[dict(path=str(prod/(m+'.lean')),sha256=sha(prod/(m+'.lean'))) for m in ['SourceGammaOneConstantHecke','OriginalCohomologyTraceNaturality','SourceGammaOneHeckeWords']],
 selectedRoute='Use the existing full literal coset formula and native coefficient-map cocycles. Linearity commutes the coefficient endomorphism with the finite sum, and the existing H1 projection formula descends both orders. Apply the already audited geometric cohomology equality. This is shorter than new tensor decompositions or a second trace-naturality framework.',
 assumptionsToDischarge='The H1 operator with any prescribed coefficient endomorphism equals the ordinary constant-coefficient correspondence followed by that endomorphism on H1, and also equals the reverse composition. This includes exactly the original homogeneous diagonal matrix action and does not remove it.',
 remaining='An arithmetic Picard/H1 comparison must realize the ordinary correspondence and retain this explicit coefficient factor. Full/parabolic and diamond conventions, arithmetic finite-character realization, original all-weight characteristic-zero association, local/image/regularity, automorphy and higher continuation remain open. No character lift follows merely from this factorization. 16/20; DUB-17--20 OPEN.',
 productionStatus='Scratch development; audits and production promotion pending.',rootPinsChanged=False,proofLimitsChanged=False)
def out(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
out('gamma1-hecke-coefficient-factor-route-631.json',json.dumps(route,indent=2)+'\n')
s=(p/'prepare_gamma_one_geometric_cohomology_audit_629.py').read_text(encoding='utf-8')
for k,v in [('mods',mods),('roots',roots),('extra',extra)]:s=re.sub(r'^'+k+'=.+$',lambda _,k=k,v=v:k+'='+repr(v),s,flags=re.M)
s=s.replace('source-gamma-one-geometric-cohomology-1','source-gamma-one-hecke-coefficient-1').replace('SourceGammaOneGeometricCohomologyAudit1','SourceGammaOneHeckeCoefficientAudit1').replace('SourceGammaOneGeometricCohomologyDependencyAudit1','SourceGammaOneHeckeCoefficientDependencyAudit1').replace('SOURCE GAMMA ONE GEOMETRIC COHOMOLOGY','SOURCE GAMMA ONE HECKE COEFFICIENT').replace('gamma1-geometric-cohomology-route-629.json','gamma1-hecke-coefficient-factor-route-631.json')
a=s.index("dep=dep[:dep.index('  logInfo m!')]");b=s.index("\noutput('SourceGammaOneHeckeCoefficientDependencyAudit1",a)
msg='SOURCE GAMMA ONE HECKE COEFFICIENT DEPENDENCY AUDIT PASS: all {required.size} required dependencies occur in the exact geometric H1 coefficient-factor theorem and the native coefficient-action construction. Only declaration values are traversed. Both orders retain the actual coefficient endomorphism, using the literal coset sum and native H1 projection. Picard/H1, parabolic and diamond comparison, all-weight Galois realization and higher continuation remain required. 16/20; DUB-17--20 OPEN.'
s=s[:a]+"dep=dep[:dep.index('  logInfo m!')]+ "+repr('  logInfo m!"'+msg+'"\n\n#eval runPlanarPairingDependencyAudit\n')+s[b:]
out('prepare_gamma_one_hecke_coefficient_audit_631.py',s)
s=(p/'record_gamma_one_geometric_cohomology_629.py').read_text(encoding='utf-8')
s=s.replace('source-gamma-one-geometric-cohomology-1','source-gamma-one-hecke-coefficient-1').replace('SourceGammaOneGeometricCohomologyAudit1','SourceGammaOneHeckeCoefficientAudit1').replace('SourceGammaOneGeometricCohomologyDependencyAudit1','SourceGammaOneHeckeCoefficientDependencyAudit1').replace('SOURCE GAMMA ONE GEOMETRIC COHOMOLOGY','SOURCE GAMMA ONE HECKE COEFFICIENT').replace('gamma1-geometric-cohomology-route-629.json','gamma1-hecke-coefficient-factor-route-631.json')
s=s.replace('==(1,10,18)','==(1,7,11)').replace('all 18 required dependencies','all 11 required dependencies').replace('requiredProofValueEdges=18','requiredProofValueEdges=11').replace('modules=1,queries=10','modules=1,queries=7').replace('proofEdges=18','proofEdges=11')
out('record_gamma_one_hecke_coefficient_631.py',s)
