from pathlib import Path
import json,re,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
prod=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
ns='Dubon2026.SourceFunctionField.GammaOne.'
mods=['SourceGammaOneHeckeGeometricSubgroup']
roots=[ns+n for n in ['heckeUpperGeometricEquiv','upperToGeometric_conjugation','upperToGeometric_matrix','upperToGeometric_smul']]
extra=['Dubon2026.'+n for n in ['originalHeckeRaisedToUpper_toRaised','originalHeckeUpperToRaised_toUpper','originalHeckeUpperToRaised_matrix','originalHeckeUpperToRaised_smul','sourceGammaOneHeckeConjugation','sourceGammaOneUpperToGammaZero']]+[ns+'levelRaiseConj_mem_Gamma1']
reuse=['SourceOriginalHeckeUpperEquiv','SourceGammaOneHeckeSubgroup','ModularDegeneracy','SourceGammaOneConstantHecke','SourceGammaOneHeckeWords']
route=dict(chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero Galois association -> arithmetic realization of original finite Gamma1 Hecke characters -> geometric/H1 comparison preserving original homogeneous coefficients -> exact upper/geometric correspondence subgroup and analytic matrix equation.',
reuseChecked=[dict(path=str(prod/(m+'.lean')),sha256=sha(prod/(m+'.lean'))) for m in reuse],
selectedRoute='Restrict the existing original upper-to-raised equivalence to Gamma1 using the already proved Gamma1 preservation of level raising. Reuse both existing inverse identities and the original analytic matrix/action equation. The existing Gamma1 conjugation homomorphism supplies multiplication. No new matrix arithmetic or coprimality premise is needed.',
assumptionsToDischarge='The actual upper correspondence subgroup inside Gamma1(M), defined by upper-right divisibility, is isomorphic to Gamma1(M) intersect Gamma0(d*M). The forward map is exactly the original diagonal conjugation, and the inverse is the existing integral level-raising matrix. Both inverse laws and the analytic matrix/action identity are proved at every positive index.',
remaining='This group isomorphism does not itself identify the Picard and H1 operators. Their transpose/diamond conventions and the original homogeneous matrix coefficient action still require exact comparison. The full/parabolic H1 distinction, Frobenius/inertia, finite-character Galois realization, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain required. 16/20; DUB-17--20 OPEN.',
productionStatus='Scratch development; audits and production promotion pending.',rootPinsChanged=False,proofLimitsChanged=False)
def out(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
out('gamma1-upper-geometric-correspondence-route-627.json',json.dumps(route,indent=2)+'\n')
s=(p/'prepare_gamma_one_hecke_field_audit_622.py').read_text(encoding='utf-8')
for k,v in [('mods',mods),('roots',roots),('extra',extra)]:s=re.sub(r'^'+k+'=.+$',lambda _,k=k,v=v:k+'='+repr(v),s,flags=re.M)
s=s.replace('source-gamma-one-hecke-field-5','source-gamma-one-geometric-subgroup-1').replace('SourceGammaOneHeckeFieldAudit5','SourceGammaOneGeometricSubgroupAudit1').replace('SourceGammaOneHeckeFieldDependencyAudit5','SourceGammaOneGeometricSubgroupDependencyAudit1').replace('SOURCE GAMMA ONE HECKE FIELD','SOURCE GAMMA ONE GEOMETRIC SUBGROUP').replace('gamma1-finite-hecke-field-route-622.json','gamma1-upper-geometric-correspondence-route-627.json')
a=s.index("dep=dep[:dep.index('  logInfo m!')]");b=s.index("\noutput('SourceGammaOneGeometricSubgroupDependencyAudit1",a)
msg='SOURCE GAMMA ONE GEOMETRIC SUBGROUP DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the actual upper/geometric subgroup isomorphism, its literal original-conjugation identity or analytic matrix/action equation. Only declaration values are traversed. Both original inverse identities, Gamma1-preserving level raising and original integral conjugation are reused. H1/Picard transpose and diamond conventions, original homogeneous coefficient action, full/parabolic comparison, arithmetic Galois realization and higher continuation remain required. 16/20; DUB-17--20 OPEN.'
s=s[:a]+"dep=dep[:dep.index('  logInfo m!')]+ "+repr('  logInfo m!"'+msg+'"\n\n#eval runPlanarPairingDependencyAudit\n')+s[b:]
out('prepare_gamma_one_geometric_subgroup_audit_627.py',s)
s=(p/'record_gamma_one_hecke_field_622.py').read_text(encoding='utf-8').replace('source-gamma-one-hecke-field-5','source-gamma-one-geometric-subgroup-1').replace('SourceGammaOneHeckeFieldAudit5','SourceGammaOneGeometricSubgroupAudit1').replace('SourceGammaOneHeckeFieldDependencyAudit5','SourceGammaOneGeometricSubgroupDependencyAudit1').replace('SOURCE GAMMA ONE HECKE FIELD','SOURCE GAMMA ONE GEOMETRIC SUBGROUP').replace('gamma1-finite-hecke-field-route-622.json','gamma1-upper-geometric-correspondence-route-627.json')
s=s.replace('==(5,17,27)','==(1,8,15)').replace('==5','==1').replace('all 27 required proof dependencies','all 15 required proof dependencies').replace('linterScopes=5','linterScopes=1').replace('requiredProofValueEdges=27','requiredProofValueEdges=15').replace('modules=5,queries=17','modules=1,queries=8').replace('proofEdges=27','proofEdges=15')
out('record_gamma_one_geometric_subgroup_627.py',s)
