from pathlib import Path
import json, re
p=Path(__file__).parent
versions={
 'SourceIntegralDiamondScalarFixedField':'1739a',
 'SourceOriginalResidueCoordinateIndex':'1742a',
 'SourceIntegralDiamondFixedPlaceTransitivity':'1744c',
 'SourceOriginalResidueDiamondFixedField':'1745b',
 'SourceIntegralDiamondBaseFiberTransitivity':'1747a',
 'SourceOriginalResidueDiamondFiberTransitivity':'1748b'}
ns='Dubon2026.SourceFunctionField.IntegralDiamond.'
names=['scalar_fixedField_eq_fullBase_of_coordinate_degree',
 'residue_original_coordinate_degree_eq_signed_index',
 'diamond_exists_comapEquiv_of_restrict_fixed_eq',
 'originalResidueDiamond_fixedField_eq_fullBase',
 'diamond_exists_comapEquiv_of_fullBase_comap_eq',
 'originalResidueDiamond_exists_comapEquiv_of_fullBase_comap_eq']
ths=[ns+n for n in names]
defs=[ns+'originalResidueDiamondAction']
roots=[ths[3],ths[5]]
edges=ths+defs+[ns+n for n in [
 'reducedFieldActionOver','reducedFieldActionOver_range_finite',
 'reduced_over_fixedField_degree_eq_signed_relativeIndex',
 'reducedFieldActionOver_fixes_fullBase','fullBase_le_originalField',
 'gammaOne_degree_and_residueField_away_level']]+[
 'Dubon2026.SourceFunctionField.GammaOne.gammaOne_coordinate_relfinrank_eq_index',
 'Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction.gammaOne_degree_and_residueField_of_integral_ratio_index',
 'Dubon2026.SourceFunctionField.residue_full_generation_and_degree',
 'Dubon2026.SourceFunctionField.valuation_residue_isAlgClosed',
 'Dubon2026.SourceLevelProjective.gamma0_index',
 'Dubon2026.SourceCurve.Place.exists_comapEquiv_of_restrict_eq',
 'FixedPoints.toAlgAut_bijective',
 'IntermediateField.relfinrank_mul_relfinrank',
 'IntermediateField.relfinrank_eq_one_iff']
mods=[m+v for m,v in versions.items()]
for m in mods:
 assert (p/(m+'.exit')).read_text().strip()=='0'
 assert (p/(m+'.log')).stat().st_size==0
old=json.loads((p/'source-reduced-diamond-scalar-1-audit-config.json').read_text())
cfg=dict(modules=mods,theorems=ths,constructions=defs,roots=roots,proofEdges=edges,
 localModules=mods+old['localModules'],queries=ths+defs,separatelyAxiomChecked=[],
 compileEvidence={m:m for m in mods})
def write(n,t):
 f=p/n;assert not f.exists(),f;f.write_text(t,encoding='utf-8')
write('original-residue-fixed-fibers-versions-1749.json',json.dumps(versions,indent=2)+'\n')
write('original-residue-fixed-fibers-preflight-config-1749.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda xs:'#['+', '.join('`'+x for x in xs)+']'
imports='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n\nopen Lean\n\n'
audit=(p/'SourceReducedDiamondScalarAudit1.lean').read_text(encoding='utf-8')
audit=imports+'\n'.join('#print axioms '+n for n in cfg['queries'])+'\n\n'+audit[audit.index('private def'):]
audit=audit[:audit.index('\n#lint in')]+ '\n\n'+'\n'.join('#lint in '+m for m in mods)+'\n'
for k in ['modules','theorems','constructions']:
 audit=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(cfg[k]),audit)
audit=audit.replace('REDUCED DIAMOND SCALAR','ORIGINAL RESIDUE FIXED FIBERS PREFLIGHT').replace('Reduced diamond action','Original residue fixed fibers')
write('SourceOriginalResidueFixedFibersPreflight1749.lean',audit)
dep=(p/'SourceReducedDiamondScalarDependencyAudit1.lean').read_text(encoding='utf-8')
dep=imports+dep[dep.index('private def'):]
for k in ['roots','localModules']:
 dep=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(cfg[k]),dep)
dep=re.sub(r'let required : Array Name := #\[[^\n]*\]','let required : Array Name := '+arr(edges),dep)
start=dep.index('  logInfo m!')
end=dep.index('\n\n#eval',start)
dep=dep[:start]+'  logInfo m!"SOURCE ORIGINAL RESIDUE FIXED FIBERS PREFLIGHT DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in declaration-value closures of the actual original residue fixed-field identity and diamond transitivity over the full modular base. Original degree preservation discharges the degree premise; native Galois place transitivity and Artin surjectivity supply the literal matrix. Fiber bounds and reverse genus remain open; DUB17--20 OPEN."'+dep[end:]
write('SourceOriginalResidueFixedFibersValuePreflight1749.lean',dep)
runner=(p/'audit_reduced_diamond_scalar_1741.ps1').read_text()
runner=re.sub(r'\$names=@\([^\n]*\)',"$names=@('SourceOriginalResidueFixedFibersPreflight1749','SourceOriginalResidueFixedFibersValuePreflight1749')",runner)
runner=runner[:runner.index("python 'E:")]+"Write-Output 'PASS: original residue fixed field and fiber transitivity preflight'\n"
write('audit_original_residue_fixed_fibers_preflight_1749.ps1',runner)
print(json.dumps(dict(modules=len(mods),queries=len(ths+defs),valueEdges=len(edges))))
