from pathlib import Path
import json,re,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
prod=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
ns='Dubon2026.SourceFunctionField.GammaOne.'
mods=['SourceGammaOneCurveGeometry','SourceGammaOneCurveInputs']
roots=[ns+n for n in ['gamma1_diffQExp_injective','gamma1_localDifferentials','gamma1_isCurveOver','gamma1_hasCanonicalDivisor','gamma1_hecke_diffQExp_injective','gamma1_hecke_localDifferentials','gamma1_hecke_isCurveOver','gamma1_hecke_hasCanonicalDivisor']]
extra=[ns+'finiteDimensional_jCoordinateOver',ns+'transcendental_jCoordinateOver','Dubon2026.SourceDifferential.diffQExp_injective_of_transcendental','Dubon2026.SourceDifferential.qEuler_ne_zero_of_transcendental','Dubon2026.SourceCurve.isCurveOver_finite_coordinate','Dubon2026.SourceCurve.hasCanonicalDivisor_finite_coordinate','Dubon2026.SourceCurve.finite_coordinate_place_dCoordGenerates','Dubon2026.SourceCurve.finite_coordinate_place_differentials']
route=dict(chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric continuation -> arithmetic automorphy -> original all-weight characteristic-zero Galois association -> arithmetic realization of finite Gamma1 Hecke characters -> Picard/H1 comparison -> actual Gamma1 curve and differential realization.',
 reuseChecked=[dict(path=str(prod/(m+'.lean')),sha256=sha(prod/(m+'.lean'))) for m in ['SourceGammaOneFunctionFieldBaseChange','SourceGammaOneCurveFinite','SourceDifferentialExpansionInjectivity','SourceCurveFiniteCoordinateGeometry','SourceCurveFiniteCoordinateCanonical']],
 selectedRoute='The original transcendental j in the actual Laurent scalar-extension field has nonzero differential. Existing finite-coordinate theorems supply actual curve, local differentials and canonical divisors; existing separable-coordinate expansion proves differential q-expansion injectivity. Native Gamma1 and Hecke subgroup congruences discharge every finite-index and translation input. No duplicate curve, local residue, Riemann--Roch or genus development.',
 assumptionsToDischarge='For the actual Gamma1(M) curve and Gamma1(M) intersect Gamma0(d*M) Hecke curve at positive levels, differential q-expansion is injective, every local coordinate differential generates and local differentials are finite, and over algebraically closed characteristic-zero coefficients the actual fields satisfy IsCurveOver and HasCanonicalDivisor. None of these is left as a hypothesis in the actual-level consumers.',
 remaining='Regular differentials still require actual cusp-form comparison and rational/base-change realization; Picard/H1 and diamond compatibility, full/parabolic comparison, arithmetic finite-character realization, original all-weight association, local/image/regularity, automorphy and higher continuation remain required. 16/20; DUB-17--20 OPEN.',
 productionStatus='Scratch development; audits and production promotion pending.',rootPinsChanged=False,proofLimitsChanged=False)
def out(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
out('gamma1-actual-curve-differential-route-632.json',json.dumps(route,indent=2)+'\n')
s=(p/'prepare_gamma_one_hecke_coefficient_audit_631.py').read_text(encoding='utf-8')
for k,v in [('mods',mods),('roots',roots),('extra',extra)]:s=re.sub(r'^'+k+'=.+$',lambda _,k=k,v=v:k+'='+repr(v),s,flags=re.M)
s=s.replace('source-gamma-one-hecke-coefficient-1','source-gamma-one-curve-geometry-2').replace('SourceGammaOneHeckeCoefficientAudit1','SourceGammaOneCurveGeometryAudit2').replace('SourceGammaOneHeckeCoefficientDependencyAudit1','SourceGammaOneCurveGeometryDependencyAudit2').replace('SOURCE GAMMA ONE HECKE COEFFICIENT','SOURCE GAMMA ONE CURVE GEOMETRY').replace('gamma1-hecke-coefficient-factor-route-631.json','gamma1-actual-curve-differential-route-632.json')
a=s.index("dep=dep[:dep.index('  logInfo m!')]");b=s.index("\noutput('SourceGammaOneCurveGeometryDependencyAudit2",a)
msg='SOURCE GAMMA ONE CURVE GEOMETRY DEPENDENCY AUDIT PASS: all {required.size} required dependencies occur in the actual Gamma1 and Hecke-curve consumers. Only declaration values are traversed. Original j and existing finite-coordinate curve, local differential, canonical-divisor and injective expansion theorems discharge all geometric input premises. Cusp/differential, Picard/H1 and diamond comparison, all-weight Galois realization and higher continuation remain required. 16/20; DUB-17--20 OPEN.'
s=s[:a]+"dep=dep[:dep.index('  logInfo m!')]+ "+repr('  logInfo m!"'+msg+'"\n\n#eval runPlanarPairingDependencyAudit\n')+s[b:]
out('prepare_gamma_one_curve_geometry_audit_632.py',s)
s=(p/'record_gamma_one_hecke_coefficient_631.py').read_text(encoding='utf-8')
s=s.replace('source-gamma-one-hecke-coefficient-1','source-gamma-one-curve-geometry-2').replace('SourceGammaOneHeckeCoefficientAudit1','SourceGammaOneCurveGeometryAudit2').replace('SourceGammaOneHeckeCoefficientDependencyAudit1','SourceGammaOneCurveGeometryDependencyAudit2').replace('SOURCE GAMMA ONE HECKE COEFFICIENT','SOURCE GAMMA ONE CURVE GEOMETRY').replace('gamma1-hecke-coefficient-factor-route-631.json','gamma1-actual-curve-differential-route-632.json')
s=s.replace('==(1,7,11)','==(2,14,22)').replace('all 11 required dependencies','all 22 required dependencies').replace('requiredProofValueEdges=11','requiredProofValueEdges=22').replace('modules=1,queries=7','modules=2,queries=14').replace('proofEdges=11','proofEdges=22').replace("with 16 linters')==1","with 16 linters')==2").replace('linterScopes=1','linterScopes=2')
out('record_gamma_one_curve_geometry_632.py',s)
