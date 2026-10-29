from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re
p=Path(__file__).parent
versions={
 'SourceIntegralSlashCoefficientLocalization':'1764a',
 'SourceIntegralSlashCoefficientReduction':'1764a',
 'SourceIntegralSlashReducedSeries':'1764a',
 'SourceIntegralSlashReducedScaling':'1764a',
 'SourceIntegralSlashReducedZero':'1764a',
 'SourceIntegralSlashReducedOperations':'1764a',
 'SourceIntegralSlashReducedSums':'1764a',
 'SourceIntegralSlashLinearRelation':'1764a'}
ns='Dubon2026.SourceFunctionField.IntegralSlash.'
mods=[m+v for m,v in versions.items()]; ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 s=f.read_text(encoding='utf-8')
 ths += [ns+n for n in re.findall(r'^theorem (\w+)',s,re.M)]
 defs += [ns+n for n in re.findall(r'^(?:def|abbrev) (\w+)',s,re.M)]
roots=[ns+n for n in ['reducedSlashSeries_linear_relation','map_clearedSlash_eq_smul_reducedSlash','reducedSlashSeries_mul','levelReduction_clearing']]+defs
edges=ths+defs+[
 'Dubon2026.SourceFunctionField.IntegralFricke.RN',
 'Dubon2026.SourceFunctionField.IntegralFricke.inv_natCast_mem_RN',
 ns+'exists_level_power_integral_even_slash_coefficients',
 ns+'cusp_strictPeriod',
 'Dubon2026.SourceFunctionField.IntegralDiamond.red_eq_zero_iff',
 'Dubon2026.SourceFunctionField.IntegralDiamond.integralQExp_inv_int_smul',
 'Dubon2026.SourceFunctionField.IntegralDiamond.integralQExp_int_smul',
 'Dubon2026.SourceFunctionField.IntegralDiamond.integralQExp_add',
 'Dubon2026.SourceFunctionField.IntegralDiamond.integralQExp_mul',
 'IsLocalization.Away.lift','IsLocalization.Away.lift_eq',
 'ModularForm.qExpansion_smul','ModularForm.qExpansion_add','ModularForm.qExpansion_mul_coe']
assert (len(mods),len(ths),len(defs),len(edges))==(8,15,5,34)
old=json.loads((p/'source-reduced-diamond-scalar-1-audit-config.json').read_text())
cfg=dict(modules=mods,theorems=ths,constructions=defs,roots=roots,proofEdges=edges,
 localModules=mods+old['localModules'],queries=ths+defs,separatelyAxiomChecked=[],compileEvidence={m:m for m in mods})
def write(n,t):
 f=p/n;assert not f.exists(),f;f.write_text(t,encoding='utf-8')
arr=lambda xs:'#['+', '.join('`'+x for x in xs)+']'
write('integral-slash-chart-relations-versions-1764.json',json.dumps(versions,indent=2)+'\n')
write('integral-slash-chart-relations-preflight-config-1764.json',json.dumps(cfg,indent=2)+'\n')
imports='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n\nopen Lean\n\n'
s=(p/'SourceOriginalResidueFixedFibersPreflight1752.lean').read_text()
s=imports+'\n'.join('#print axioms '+n for n in cfg['queries'])+'\n\n'+s[s.index('private def'):]
s=s[:s.index('\n#lint in')]+'\n\n'+'\n'.join('#lint in '+m for m in mods)+'\n'
for k in ['modules','theorems','constructions']:
 s=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(cfg[k]),s)
s=s.replace('ORIGINAL RESIDUE FIXED FIBERS PREFLIGHT','INTEGRAL SLASH CHART RELATIONS PREFLIGHT').replace('Original residue fixed fibers','Integral slash chart relations')
write('SourceIntegralSlashChartRelationsPreflight1764.lean',s)
s=(p/'SourceOriginalResidueFixedFibersValuePreflight1752.lean').read_text()
s=imports+s[s.index('private def'):]
for k in ['roots','localModules']:
 s=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(cfg[k]),s)
s=re.sub(r'let required : Array Name := #\[[^\n]*\]','let required : Array Name := '+arr(edges),s)
start=s.index('  logInfo m!');end=s.index('\n\n#eval',start)
s=s[:start]+'  logInfo m!"SOURCE INTEGRAL SLASH CHART RELATIONS PREFLIGHT DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the declaration-value closures of actual localized coefficient constructions, clearing-power comparison, product reduction and finite residue-field linear relation transfer. Native uniform slash integrality and the prime-multiple Fourier kernel discharge the integrality and relation premises. The actual field embedding, stabilizer charts, residue fiber bounds and reverse genus remain open; DUB17--20 OPEN."'+s[end:]
write('SourceIntegralSlashChartRelationsValuePreflight1764.lean',s)
s=(p/'audit_original_residue_fixed_fibers_preflight_1752.ps1').read_text()
s=s.replace('SourceOriginalResidueFixedFibersPreflight1752','SourceIntegralSlashChartRelationsPreflight1764').replace('SourceOriginalResidueFixedFibersValuePreflight1752','SourceIntegralSlashChartRelationsValuePreflight1764').replace('original residue fixed field and fiber transitivity','integral slash chart relations')
write('audit_integral_slash_chart_relations_preflight_1764.ps1',s)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
refs=['anthropic-residue-chart-construction-1751/manifest.json','anthropic-chart-field-extension-1762/manifest.json','source-original-residue-fixed-fibers-1-scratch-receipt.json']
write('integral-slash-chart-relations-route-1764.json',json.dumps(dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain='DUB17 Theorem 2.6 / DUB18 Corollary 8.2 -> literal higher continuation -> automorphy -> original all-weight association -> actual homogeneous Gamma1 Hecke-character realization -> original genus preservation -> reverse genus inequality -> cusp residue fiber bounds -> actual reduced slash field embedding -> literal coefficient reduction and finite linear relations.',reuseReviewed=[dict(path=str(p/n),sha256=sha(p/n)) for n in refs],shorterRoute='Native RN level-integral coefficient ring plus Mathlib localization replaces coefficientwise choices and denominator-independence arithmetic. Native uniform even slash integrality, integral-form operations and exact prime-multiple Fourier kernel give all finite relation transfer. Existing even representatives cover every original integral ratio. The separate field-extension review found native IsFractionRing.isAlgebraic_iff and Algebra.IsAlgebraic.injective_tower_top as a potentially shorter rigorous route; their actual consumer is still to be proved.',remaining='No field embedding, stabilizer chart, residue fiber bound or reverse genus conclusion claimed. Acceptance 16/20; DUB17--20 OPEN.',rootPinsChanged=False,proofLimitsChanged=False,externalBuild=False,externalImport=False),indent=2)+'\n')
print(json.dumps(dict(modules=8,queries=20,valueEdges=34)))
