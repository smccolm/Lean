from pathlib import Path
import json,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
repo=Path(r'E:\Lean\Riemann Zeta')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
old=json.loads((p/'fricke-transformation-route-647.json').read_text())
cfg=json.loads((p/'source-fricke-transformation-4c-audit-config.json').read_text())
sources=[p/'gamma1-cusp-realization-reuse-assessment-644.json',p/'gamma1-rational-structure-input-reuse-assessment-646.json',p/'gamma1-rational-structure-input-reuse-646/snapshots.json',p/'fricke-transformation-documented-successor-647b.json',repo/'Tools/none']
sources=sources[:-1]+[repo/'9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026/Tools/reuse-20261025-579/anthropics__fermats-last-theorem/LICENSE.txt',repo/'.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean',repo/'.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/SlashInvariantForms.lean']
# The native slash declaration may live in SlashInvariantForms. Resolve its actual checked location.
sources=[f for f in sources if f.exists()]
rd=dict(chain=old['dependency'],reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in sources],selectedRoute=old['selectedRoute'],assumptionsToDischarge='The actual normalized Fricke functions transform by the original row-vector action on torsion indices, are invariant under the principal congruence subgroup and are unchanged by negating the index. Every original SL2 matrix permutes the actual nonzero-index family. All lattice scaling, basis change, lift-independence and native modular-form transformations are proved inputs.',remaining=old['remaining'],scratchImportClosure=cfg['modules'],separateAxiomChecks=cfg['separatelyAxiomChecked'],separateReason=cfg['separateReason'],successor='V2 modules add definition documentation only; failed full audit and failed dependency audit remain immutable. Native proof reduction removes five rfl theorem constants while their actual definitions remain required value dependencies.',rootPinsChanged=False,proofLimitsChanged=False,externalImport=False)
f=p/'fricke-transformation-route-647c.json';assert not f.exists();f.write_text(json.dumps(rd,indent=2)+'\n',encoding='utf-8')
s=(p/'record_gamma_one_differential_regularity_643b.py').read_text(encoding='utf-8')
s=s.replace('source-gamma-one-differential-regularity-6b','source-fricke-transformation-4c').replace('SourceGammaOneDifferentialRegularityAudit6','SourceFrickeTransformationAudit4b').replace('SourceGammaOneDifferentialRegularityDependencyAudit6b','SourceFrickeTransformationDependencyAudit4c').replace('SOURCE GAMMA ONE DIFFERENTIAL REGULARITY','SOURCE FRICKE TRANSFORMATION').replace('gamma1-differential-regularity-route-643b.json','fricke-transformation-route-647c.json')
s=s.replace('(6,11,21)','(4,42,39)').replace('==6','==4').replace('all 21 required dependencies','all 39 required proof dependencies').replace('linterScopes=6','linterScopes=4').replace('requiredProofValueEdges=21','requiredProofValueEdges=39').replace('modules=6,queries=11','modules=4,queries=42').replace('proofEdges=21','proofEdges=39')
f=p/'record_fricke_transformation_647c.py';assert not f.exists();f.write_text(s,encoding='utf-8')
print('Prepared exact Fricke transformation receipt recorder.')
