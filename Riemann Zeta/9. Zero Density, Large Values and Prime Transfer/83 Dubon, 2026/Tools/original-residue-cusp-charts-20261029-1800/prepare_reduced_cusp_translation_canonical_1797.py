from pathlib import Path
import ast,json,re
p=Path(__file__).parent
def write(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
versions=json.loads((p/'reduced-cusp-translation-versions-1796.json').read_text())
for n in ['SourceReducedCuspTranslationPreflight1796','SourceReducedCuspTranslationValuePreflight1796']:
 assert (p/(n+'.exit')).read_text().strip()=='0'
 assert not re.search(r'warning:|error(?:\(|:)|PANIC|Try this:|sorryAx|Found [1-9]',(p/(n+'.log')).read_text(encoding='utf-16'))
def canon(s):
 for n,v in versions.items():s=s.replace(n+v,n)
 return s
for n,v in versions.items():
 s=(p/(n+v+'.lean')).read_text(encoding='utf-8')
 for m,w in versions.items():s=s.replace('import '+m+w+'\n','import '+m+'\n')
 write(n+'.lean',s)
write('reduced-cusp-translation-versions-1797.json',json.dumps(versions,indent=2)+'\n')
cfg=json.loads(canon((p/'reduced-cusp-translation-preflight-config-1796.json').read_text()))
cfg['compileEvidence']={m:m+'-1797' for m in versions}
stem='source-reduced-cusp-translation-1'
write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
for a,b in [('SourceReducedCuspTranslationPreflight1796','SourceReducedCuspTranslationAudit1'),('SourceReducedCuspTranslationValuePreflight1796','SourceReducedCuspTranslationDependencyAudit1')]:
 write(b+'.lean',canon((p/(a+'.lean')).read_text()).replace('TRANSLATION PREFLIGHT','TRANSLATION'))
mods=list(versions);arr=lambda a:'#['+', '.join('`'+n for n in a)+']'
s=(p/'SourcePrescribedResidueCuspChartScratchOwnership1790.lean').read_text()
s='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+s[s.index('\nopen Lean'):]
s=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),s)
write('SourceReducedCuspTranslationScratchOwnership1797.lean',s)
r=json.loads((p/'reduced-cusp-translation-route-1796.json').read_text())
rf='source-reduced-cusp-translation-audit-route-1797'
write(rf+'.json',json.dumps(r,indent=2)+'\n')
write('Dubon Reduced Cusp Translation Assessment 2026-10-29.md','# Reduced cusp translation — 29 October 2026\n\n'+r['chain']+'\n\n'+r['shorterRoute']+'\n\n'+r['remaining']+'\n\nScratch-audited only; promotion and assembled verification remain pending. Frozen paper, root pins and owner-only BAT unchanged.\n')
s=(p/'record_prescribed_residue_cusp_chart_1790.py').read_text()
for a,b in [('source-prescribed-residue-cusp-chart-1',stem),('SourcePrescribedResidueCuspChartAudit1','SourceReducedCuspTranslationAudit1'),('SourcePrescribedResidueCuspChartDependencyAudit1','SourceReducedCuspTranslationDependencyAudit1'),('SourcePrescribedResidueCuspChartScratchOwnership1790','SourceReducedCuspTranslationScratchOwnership1797'),('source-prescribed-residue-cusp-chart-audit-route-1790',rf),('PRESCRIBED RESIDUE CUSP CHART','REDUCED CUSP TRANSLATION'),('(2, 2, 10)','(5, 11, 18)'),('modules=2','modules=5'),('queries=2','queries=11'),('linterScopes=2','linterScopes=5'),("text.count('with 16 linters') == 2","text.count('with 16 linters') == 5"),('all 10 required','all 18 required'),('requiredProofValueEdges=10','requiredProofValueEdges=18'),('proofEdges=10','proofEdges=18')]:s=s.replace(a,b)
ast.parse(s);write('record_reduced_cusp_translation_1797.py',s)
s=(p/'audit_prescribed_residue_cusp_chart_1790.ps1').read_text()
for a,b in [('SourcePrescribedResidueCuspChartAudit1','SourceReducedCuspTranslationAudit1'),('SourcePrescribedResidueCuspChartDependencyAudit1','SourceReducedCuspTranslationDependencyAudit1'),('SourcePrescribedResidueCuspChartScratchOwnership1790','SourceReducedCuspTranslationScratchOwnership1797'),('record_prescribed_residue_cusp_chart_1790','record_reduced_cusp_translation_1797')]:s=s.replace(a,b)
write('audit_reduced_cusp_translation_1797.ps1',s)
s=(p/'build_prescribed_residue_cusp_chart_canonical_1790.ps1').read_text()
s=re.sub(r'\$names=@\([^\n]+\)',"$names=@("+','.join(repr(m) for m in mods)+')',s).replace("$ev=$base+'-1790'","$ev=$base+'-1797'").replace('audit_prescribed_residue_cusp_chart_1790','audit_reduced_cusp_translation_1797')
write('build_reduced_cusp_translation_canonical_1797.ps1',s)
print('Canonical translation bodies frozen; 5 modules, 11 queries, 18 VALUE edges')
