from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re
p=Path(__file__).parent
versions={
 'SourceIntegralSlashLevelOne':'1765b',
 'SourceIntegralSlashDiscriminantNormalization':'1766e',
 'SourceCoordinateAlgebraicChartInjectivity':'1767d',
 'SourceIntegralSlashReducedPowers':'1769c',
 'SourceIntegralSlashReducedEquality':'1770b',
 'SourceIntegralSlashNormalizedGenerators':'1771a',
 'SourceIntegralSlashNormalizedRatioEquality':'1772a',
 'SourceIntegralSlashNormalizedMap':'1773a',
 'SourceIntegralSlashNormalizedLinearRelations':'1774a',
 'SourceIntegralSlashNormalizedCoordinate':'1775a',
 'SourceMonoidGeneratorAlgebraLift':'1776b',
 'SourceIntegralSlashNormalizedAlgebra':'1777d',
 'SourceCoordinateChartFractionExtension':'1778b',
 'SourceIntegralSlashFieldEmbedding':'1779g',
 'SourceOriginalResidueSlashFieldEmbedding':'1780c'}
ns='Dubon2026.SourceFunctionField.IntegralSlash.'
mods=[m+v for m,v in versions.items()]; ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 s=f.read_text(encoding='utf-8')
 ths += [ns+n for n in re.findall(r'^theorem (\w+)',s,re.M)]
 defs += [ns+n for n in re.findall(r'^(?:def|abbrev) (\w+)',s,re.M)]
roots=[ns+'exists_originalResidueSlashFieldHom']+defs
edges=ths+defs+[
 'Dubon2026.SourceFricke.qExpansion_coeff_width',
 'Dubon2026.SourceFunctionField.qExpand_ofPowerSeries_eq_expand',
 'Dubon2026.SourceFunctionField.IntegralJCoordinate.transcendental_qExpand_jqModC',
 'Dubon2026.SourceFunctionField.constantCoeff_dedekindEtaUnit',
 'Dubon2026.SourceFunctionField.dedekindEtaUnit_mul_inv',
 'Dubon2026.SourceFunctionField.IntegralDiamond.residue_original_coordinate_degree_eq_signed_index',
 'Dubon2026.SourceFunctionField.IntegralDiamond.gammaOne_degree_and_residueField_away_level',
 ns+'reducedSlashSeries_linear_relation',ns+'levelReduction_integers',
 ns+'reducedSlashSeries_mul',ns+'reducedSlashSeries_zero_of_prime_reduction',
 'IsFractionRing.comap_isAlgebraic_iff','Algebra.IsAlgebraic.injective_tower_top',
 'Algebra.IsAlgebraic.tower_bot_of_injective','MonoidAlgebra.lift',
 'RingHom.liftOfRightInverse','IsFractionRing.liftAlgHom']
j=json.loads((p/'source-original-residue-fixed-fibers-1-audit-config.json').read_text())
k=json.loads((p/'integral-slash-chart-relations-preflight-config-1764.json').read_text())
local=list(dict.fromkeys(mods+k['localModules']+j['localModules']))
cfg=dict(modules=mods,theorems=ths,constructions=defs,roots=roots,proofEdges=edges,
 localModules=local,queries=ths+defs,separatelyAxiomChecked=[],compileEvidence={m:m for m in mods})
def write(n,t):
 f=p/n;assert not f.exists(),f;f.write_text(t,encoding='utf-8')
arr=lambda xs:'#['+', '.join('`'+x for x in xs)+']'
write('original-residue-slash-embedding-versions-1782.json',json.dumps(versions,indent=2)+'\n')
write('original-residue-slash-embedding-preflight-config-1782.json',json.dumps(cfg,indent=2)+'\n')
imports='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n\nopen Lean\n\n'
s=(p/'SourceIntegralSlashChartRelationsPreflight1764.lean').read_text()
s=imports+'\n'.join('#print axioms '+n for n in cfg['queries'])+'\n\n'+s[s.index('private def'):]
s=s[:s.index('\n#lint in')]+'\n\n'+'\n'.join('#lint in '+m for m in mods)+'\n'
for name in ['modules','theorems','constructions']:
 s=re.sub(r'let '+name+r' : Array Name := #\[[^\n]*\]','let '+name+' : Array Name := '+arr(cfg[name]),s)
s=s.replace('INTEGRAL SLASH CHART RELATIONS PREFLIGHT','ORIGINAL RESIDUE SLASH EMBEDDING PREFLIGHT').replace('Integral slash chart relations','Original residue slash embedding')
write('SourceOriginalResidueSlashEmbeddingPreflight1782.lean',s)
s=(p/'SourceIntegralSlashChartRelationsValuePreflight1764.lean').read_text()
s=imports+s[s.index('private def'):]
for name in ['roots','localModules']:
 s=re.sub(r'let '+name+r' : Array Name := #\[[^\n]*\]','let '+name+' : Array Name := '+arr(cfg[name]),s)
s=re.sub(r'let required : Array Name := #\[[^\n]*\]','let required : Array Name := '+arr(edges),s)
start=s.index('  logInfo m!');end=s.index('\n\n#eval',start)
s=s[:start]+'  logInfo m!"SOURCE ORIGINAL RESIDUE SLASH EMBEDDING PREFLIGHT DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the declaration-value closures of the actual valuation-residue cusp field embedding and explicitly audited original modular constructions. Native original degree preservation, coefficient relation transfer, monoid-algebra quotient descent, coordinate transcendence and fraction-ring algebraicity discharge every degree, algebraicity, injectivity and embedding certificate. Stabilizer charts, residue fiber bounds and reverse genus remain open; DUB17--20 OPEN."'+s[end:]
write('SourceOriginalResidueSlashEmbeddingValuePreflight1782.lean',s)
s=(p/'audit_integral_slash_chart_relations_preflight_1764.ps1').read_text()
s=s.replace('SourceIntegralSlashChartRelationsPreflight1764','SourceOriginalResidueSlashEmbeddingPreflight1782').replace('SourceIntegralSlashChartRelationsValuePreflight1764','SourceOriginalResidueSlashEmbeddingValuePreflight1782').replace('integral slash chart relations','original residue slash embedding')
write('audit_original_residue_slash_embedding_preflight_1782.ps1',s)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
refs=['anthropic-residue-chart-construction-1751/manifest.json','anthropic-chart-field-extension-1762/manifest.json','source-original-residue-fixed-fibers-1-scratch-receipt.json','source-integral-slash-chart-relations-1-scratch-receipt.json']
write('original-residue-slash-embedding-route-1782.json',json.dumps(dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain='DUB17 Theorem 2.6 / DUB18 Corollary 8.2 -> literal higher continuation -> automorphy -> original all-weight association -> actual homogeneous Gamma1 Hecke-character realization -> original genus preservation -> reverse genus inequality -> cusp residue fiber bounds -> actual residue cusp field embedding.',reuseReviewed=[dict(path=str(p/n),sha256=sha(p/n)) for n in refs],shorterRoute='Native width expansion computes all level-one images. Original discriminant powers normalize all original integral ratios, even when their original weight is negative or odd. Native finite relation transfer extends to all normalized generators. Native MonoidAlgebra.lift and RingHom.liftOfRightInverse replace separate span and bilinear multiplicativity constructions. Native IsFractionRing.comap_isAlgebraic_iff and Algebra.IsAlgebraic.injective_tower_top replace the external minimal-polynomial denominator argument. The already proved original residue coordinate degree discharges algebraicity in the actual residue consumer, and the original j image is exactly the already proved transcendental j(q^N).',remaining='Stabilizer equivariance, actual residue fiber bounds and reverse genus remain open. The map is proved for every supplied algebraic-integer reduction homomorphism; construction of reductions with prescribed root-of-unity image remains a separate cusp-chart input. Acceptance 16/20; DUB17--20 OPEN.',rootPinsChanged=False,proofLimitsChanged=False,externalBuild=False,externalImport=False),indent=2)+'\n')
print(json.dumps(dict(modules=len(mods),theorems=len(ths),constructions=len(defs),queries=len(ths+defs),valueEdges=len(edges))))
