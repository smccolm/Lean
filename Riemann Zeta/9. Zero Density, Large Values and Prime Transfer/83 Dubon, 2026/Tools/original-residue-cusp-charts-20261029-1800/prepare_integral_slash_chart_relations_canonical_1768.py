from pathlib import Path
from datetime import datetime, timezone
import ast, hashlib, json, re
p=Path(__file__).parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
versions=json.loads((p/'integral-slash-chart-relations-versions-1764.json').read_text())
for n in ['SourceIntegralSlashChartRelationsPreflight1764','SourceIntegralSlashChartRelationsValuePreflight1764']:
 f=p/(n+'.log');assert f.with_suffix('.exit').read_text().strip()=='0'
 assert not re.search(r'warning:|error(?:\(|:)|PANIC|Try this:|sorryAx|Found [1-9]',f.read_text(encoding='utf-16'))
def write(n,t):
 f=p/n;assert not f.exists(),f;f.write_text(t,encoding='utf-8')
def canonical(s):
 for n,v in versions.items():s=s.replace(n+v,n)
 return s
mods=list(versions)
for n,v in versions.items():
 f=p/(n+v+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0
 s=f.read_text(encoding='utf-8')
 for m,w in versions.items():s=s.replace('import '+m+w+'\n','import '+m+'\n')
 write(n+'.lean',s)
write('integral-slash-chart-relations-versions-1768.json',json.dumps(versions,indent=2)+'\n')
cfg=json.loads(canonical((p/'integral-slash-chart-relations-preflight-config-1764.json').read_text()))
cfg['compileEvidence']={m:m+'-1768' for m in mods}
stem='source-integral-slash-chart-relations-1'
write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
for a,b in [('SourceIntegralSlashChartRelationsPreflight1764','SourceIntegralSlashChartRelationsAudit1'),('SourceIntegralSlashChartRelationsValuePreflight1764','SourceIntegralSlashChartRelationsDependencyAudit1')]:
 s=canonical((p/(a+'.lean')).read_text()).replace('CHART RELATIONS PREFLIGHT','CHART RELATIONS')
 write(b+'.lean',s)
arr=lambda xs:'#['+', '.join('`'+x for x in xs)+']'
s=(p/'SourceOriginalResidueFixedFibersScratchOwnership1754.lean').read_text()
s='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+s[s.index('\nopen Lean'):]
s=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),s)
write('SourceIntegralSlashChartRelationsScratchOwnership1768.lean',s)
chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> automorphy -> original all-weight characteristic-zero association -> finite homogeneous Gamma1 Hecke-character realization -> original genus preservation -> reverse genus inequality -> cusp residue fiber bounds -> actual reduced slash field embedding -> localized coefficients and finite linear relation transfer.'
discharged=[
 'The literal level-integral coefficient ring is the localization of the actual complex algebraic integers at the level. Its universal reduction map gives exact clearing-power formulas without choosing a denominator independently for each proof.',
 'Native uniform even-weight slash integrality puts every actual cusp Fourier series in this ring. Every algebraic-integer series clearing it by any level power reduces to the same normalized series.',
 'The actual reduced slash series preserves addition, products, integer multiples and finite integer sums. The exact prime-multiple Fourier kernel transfers zero reduction to every cusp.',
 'Projecting onto a basis over the prime field and reassembling finite supports proves preservation of every finite residue-field linear relation between original integral modular forms of the same even weight. No relation-preservation certificate remains in this consumer.'
]
remaining='The actual normalized-generator field embedding, its stabilizer charts, residue fiber bounds and reverse genus inequality remain open. Original genus preservation, integral parabolic transfer, exceptional-prime removal, two-dimensional characteristic-zero realization, original all-weight association, local/image/regularity inputs, automorphy and literal higher continuation remain required. Acceptance remains 16/20; DUB-17--20 OPEN under every original completion condition.'
route='The native level-integral subring, Mathlib localization, original uniform slash integrality, integral modular-form operations and exact prime-multiple Fourier kernel replace the longer coefficientwise-choice construction in the pinned external reference. Existing even representatives cover every original integral ratio. The first preflight found one missing declaration docstring; the fresh successor adds that docstring, preserving all mathematical statements and proof bodies and every audit check. The failed predecessor is retained. A separate native algebraicity shortcut for the later field-map injectivity is under development and is not claimed here.'
report='Dubon Actual Reduced Slash Relations Assessment 2026-10-29.md'
write(report,'# Actual reduced slash relations — 29 October 2026\n\n'+chain+'\n\n'+'\n\n'.join(discharged)+'\n\n'+route+'\n\n'+remaining+'\n\nScratch-audited only; production promotion and assembled verification remain pending. Frozen paper, root pins, proof limits and owner-only BAT are unchanged.\n')
refs=['integral-slash-chart-relations-route-1764.json','anthropic-residue-chart-construction-1751/manifest.json','anthropic-chart-field-extension-1762/manifest.json',report]
rf='source-integral-slash-chart-relations-audit-route-1768'
write(rf+'.json',json.dumps(dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain=chain,reuseChecked=[dict(path=str(p/n),sha256=sha(p/n)) for n in refs],shorterRoute=route,assumptionsToDischarge=discharged,remaining=remaining,externalBuild=False,externalImport=False,rootPinsChanged=False,proofLimitsChanged=False),indent=2)+'\n')
s=(p/'record_original_residue_fixed_fibers_1754.py').read_text()
for a,b in [('source-original-residue-fixed-fibers-1',stem),('SourceOriginalResidueFixedFibersAudit1','SourceIntegralSlashChartRelationsAudit1'),('SourceOriginalResidueFixedFibersDependencyAudit1','SourceIntegralSlashChartRelationsDependencyAudit1'),('SourceOriginalResidueFixedFibersScratchOwnership1754','SourceIntegralSlashChartRelationsScratchOwnership1768'),('source-original-residue-fixed-fibers-audit-route-1754',rf),('ORIGINAL RESIDUE FIXED FIBERS','INTEGRAL SLASH CHART RELATIONS')]:s=s.replace(a,b)
for a,b in [('(6, 7, 22)','(8, 20, 34)'),('modules=6','modules=8'),('queries=7','queries=20'),('linterScopes=6','linterScopes=8'),("text.count('with 16 linters') == 6","text.count('with 16 linters') == 8"),('all 22 required','all 34 required'),('requiredProofValueEdges=22','requiredProofValueEdges=34'),('proofEdges=22','proofEdges=34')]:s=s.replace(a,b)
ast.parse(s);write('record_integral_slash_chart_relations_1768.py',s)
s=(p/'audit_original_residue_fixed_fibers_1754.ps1').read_text()
for a,b in [('SourceOriginalResidueFixedFibersAudit1','SourceIntegralSlashChartRelationsAudit1'),('SourceOriginalResidueFixedFibersDependencyAudit1','SourceIntegralSlashChartRelationsDependencyAudit1'),('SourceOriginalResidueFixedFibersScratchOwnership1754','SourceIntegralSlashChartRelationsScratchOwnership1768'),('record_original_residue_fixed_fibers_1754','record_integral_slash_chart_relations_1768')]:s=s.replace(a,b)
write('audit_integral_slash_chart_relations_1768.ps1',s)
s=(p/'build_original_residue_fixed_fibers_canonical_1754.ps1').read_text()
s=re.sub(r'\$names=@\([^\n]+\)',"$names=@("+','.join(repr(m) for m in mods)+')',s).replace("$ev=$base+'-1754'","$ev=$base+'-1768'").replace('audit_original_residue_fixed_fibers_1754','audit_integral_slash_chart_relations_1768')
write('build_integral_slash_chart_relations_canonical_1768.ps1',s)
print(json.dumps(dict(modules=8,queries=20,valueEdges=34,status='Canonical mathematical bodies and comments frozen; build/audit pending')))
