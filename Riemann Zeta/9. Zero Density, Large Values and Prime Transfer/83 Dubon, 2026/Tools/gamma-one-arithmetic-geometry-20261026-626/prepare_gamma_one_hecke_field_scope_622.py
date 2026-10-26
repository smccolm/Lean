from pathlib import Path
import json,re,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
prod=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
mods=['SourceGammaOneModularStretch','SourceGammaOneModularStretchCoefficients','SourceGammaOneHeckeFieldInclusion','SourceGammaOneHeckeDegeneracy','SourceGammaOneHeckeFieldFinite']
ns='Dubon2026.SourceFunctionField.GammaOne.'
roots=[ns+n for n in ['heckeAlpha_finite','heckeBeta_finite','heckeAlpha_coe','heckeBeta_coe']]
extra=['ModularForm.translate','Dubon2026.levelRaiseFun_apply','Dubon2026.hasSum_pow_dvd_reindex','ModularFormClass.qExpansion_coeff_unique','Dubon2026.SourceFunctionField.coeffMap_qExpand','Dubon2026.SourceCurve.finite_over_transcendental_of_finite_coordinate','Dubon2026.SourceCurve.finite_hom_of_finite_image_coordinate']+[ns+n for n in ['gamma1_finite_coordinate','gamma1_hecke_finite_coordinate','gamma1_hecke_baseChange_le']]
reuse=['ModularDegeneracy','ModularDegeneracyCoefficients','SourceModularNormPolynomial','SourceCuspDegeneracyLaurent','SourceOriginalSlotRange','SourceLaurentCoefficientReindex','SourceOriginalHeckeDegeneracy','SourceFiniteCoordinateHom','SourceCurveFiniteCoordinateResidues']
route=dict(chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero Galois association -> arithmetic realization of actual original finite Gamma1 Hecke characters -> genuine finite geometric Gamma1 Hecke correspondences -> actual integral modular dilation and literal rational/scalar-extended field maps.',
reuseChecked=[dict(path=str(prod/(m+'.lean')),sha256=sha(prod/(m+'.lean'))) for m in reuse],
primaryAssessment=dict(path=str(p/'gamma1-hecke-correspondence-reuse-assessment-621.json'),sha256=sha(p/'gamma1-hecke-correspondence-reuse-assessment-621.json')),
selectedRoute='Native ModularForm.translate supplies holomorphy and cusp bounds. Reuse the original diagonal matrix, exact integral conjugate and slash evaluation; only Gamma1 membership is new. Native power-series expansion plus existing q-parameter/sparse-sum identities prove integral q-expansion preservation. Existing Laurent substitution and coefficient compatibility, native intermediate-field adjoin maps and already proved finite-coordinate exchange construct both literal finite field maps. No second cusp analysis, duplicate sparse-series algebra, external fallback definition or new general curve finiteness argument is introduced.',
deferred=['Arithmetic geometric/H1 and diamond comparisons','Divisor and Picard comparison until actual maps are audited','External conditional fallback beta definition and duplicate Laurent coefficient compatibility'],
assumptionsToDischarge='The actual translated modular form has q-expansion a(n/d) on multiples of d and zero otherwise. Integral expansions remain integral under native power-series expansion. The original qExpand preserves the actual Gamma1 integral-ratio field into Gamma1(M) intersect Gamma0(d*M). This gives the literal scalar-extended second field map, alongside the existing inclusion as the first map. Both maps are finite using actual proved finite coordinates; no field-preservation, modular-polynomial symmetry or finite-map hypothesis remains.',
remaining='Arithmetic geometric and diamond comparison, finite-character Galois realization, original all-weight characteristic-zero association, required local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain required. 16/20; DUB-17--20 OPEN.',
productionStatus='Scratch development; exhaustive audits and production promotion pending.',rootPinsChanged=False,proofLimitsChanged=False,
preservedFailure=dict(path=str(p/'gamma1-hecke-fields-622-before-explicit-inclusion-projection/evidence.json'),sha256=sha(p/'gamma1-hecke-fields-622-before-explicit-inclusion-projection/evidence.json'),resolution='Use IntermediateField.coe_inclusion to avoid reflexivity unfolding the concrete field. Same statement and unchanged limits.'))
def output(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('gamma1-finite-hecke-field-route-622.json',json.dumps(route,indent=2)+'\n')
s=(p/'prepare_gamma_one_function_field_audit_620b.py').read_text(encoding='utf-8')
s=re.sub(r'^mods=.+$',lambda _:'mods='+repr(mods),s,flags=re.M)
s=re.sub(r'^roots=.+$',lambda _:'roots='+repr(roots),s,flags=re.M)
s=re.sub(r'^extra=.+$',lambda _:'extra='+repr(extra),s,flags=re.M)
s=s.replace('^theorem (',r'^(?:@\[[^\n]*\]\s*)?theorem (')
s=s.replace('source-gamma-one-function-field-10b','source-gamma-one-hecke-field-5').replace('SourceGammaOneFunctionFieldAudit10b','SourceGammaOneHeckeFieldAudit5').replace('SourceGammaOneFunctionFieldDependencyAudit10b','SourceGammaOneHeckeFieldDependencyAudit5').replace('SOURCE GAMMA ONE FUNCTION FIELD','SOURCE GAMMA ONE HECKE FIELD').replace('gamma1-function-field-finite-route-620b.json','gamma1-finite-hecke-field-route-622.json')
start=s.index("dep=dep[:dep.index('  logInfo m!')]")
end=s.index("\noutput('SourceGammaOneHeckeFieldDependencyAudit5",start)
msg='SOURCE GAMMA ONE HECKE FIELD DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in finiteness or literal projection of the actual Gamma1 Hecke maps. Only declaration values are traversed. Native modular translation, existing sparse sums, actual integral ratios, Laurent coefficient compatibility and proved coordinate exchange discharge the field-preservation and finite-map inputs. Arithmetic geometric and diamond comparison, finite-character Galois realization, original all-weight characteristic-zero association and higher continuation remain required. 16/20; DUB-17--20 OPEN.'
s=s[:start]+"dep=dep[:dep.index('  logInfo m!')]+ "+repr('  logInfo m!"'+msg+'"\n\n#eval runPlanarPairingDependencyAudit\n')+s[end:]
output('prepare_gamma_one_hecke_field_audit_622.py',s)
s=(p/'record_gamma_one_function_field_620b.py').read_text(encoding='utf-8').replace('source-gamma-one-function-field-10b','source-gamma-one-hecke-field-5').replace('SourceGammaOneFunctionFieldAudit10b','SourceGammaOneHeckeFieldAudit5').replace('SourceGammaOneFunctionFieldDependencyAudit10b','SourceGammaOneHeckeFieldDependencyAudit5').replace('SOURCE GAMMA ONE FUNCTION FIELD','SOURCE GAMMA ONE HECKE FIELD').replace('gamma1-function-field-finite-route-620b.json','gamma1-finite-hecke-field-route-622.json')
# Counts are validated against the newly generated configuration, then fixed in the receipt.
s=s.replace("==(10,37,46)","==(5,17,27)").replace("==10","==5").replace("'all 46 required proof dependencies'","'all 27 required proof dependencies'").replace('linterScopes=10','linterScopes=5').replace('requiredProofValueEdges=46','requiredProofValueEdges=27').replace('modules=10,queries=37','modules=5,queries=17').replace('proofEdges=46','proofEdges=27')
output('record_gamma_one_hecke_field_622.py',s)
print(json.dumps(dict(prepared=True,modules=mods,roots=roots,expectedQueries=17,expectedEdges=27)))
