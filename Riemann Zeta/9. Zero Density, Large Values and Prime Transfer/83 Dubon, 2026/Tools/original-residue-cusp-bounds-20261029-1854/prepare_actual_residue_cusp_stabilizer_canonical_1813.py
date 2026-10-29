from pathlib import Path
import ast,json,re
p=Path(__file__).parent
def write(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
versions=json.loads((p/'actual-residue-cusp-stabilizer-versions-1810.json').read_text())
for n in ['SourceActualResidueCuspStabilizerPreflight1810','SourceActualResidueCuspStabilizerValuePreflight1810']:
 assert (p/(n+'.exit')).read_text().strip()=='0'
 assert not re.search(r'warning:|error(?:\(|:)|PANIC|Try this:|sorryAx|Found [1-9]',(p/(n+'.log')).read_text(encoding='utf-16'))
def canon(s):
 for n,v in versions.items():s=s.replace(n+v,n)
 return s
for n,v in versions.items():
 s=(p/(n+v+'.lean')).read_text(encoding='utf-8')
 for m,w in versions.items():s=s.replace('import '+m+w+'\n','import '+m+'\n')
 write(n+'.lean',s)
write('actual-residue-cusp-stabilizer-versions-1813.json',json.dumps(versions,indent=2)+'\n')
cfg=json.loads(canon((p/'actual-residue-cusp-stabilizer-preflight-config-1810.json').read_text()))
cfg['compileEvidence']={m:m+'-1813' for m in versions}
stem='source-actual-residue-cusp-stabilizer-1'
write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
for a,b in [('SourceActualResidueCuspStabilizerPreflight1810','SourceActualResidueCuspStabilizerAudit1'),('SourceActualResidueCuspStabilizerValuePreflight1810','SourceActualResidueCuspStabilizerDependencyAudit1')]:
 write(b+'.lean',canon((p/(a+'.lean')).read_text()).replace('STABILIZER PREFLIGHT','STABILIZER'))
mods=list(versions);arr=lambda a:'#['+', '.join('`'+n for n in a)+']'
s=(p/'SourcePrescribedResidueCuspChartScratchOwnership1790.lean').read_text()
s='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+s[s.index('\nopen Lean'):]
s=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),s)
write('SourceActualResidueCuspStabilizerScratchOwnership1813.lean',s)
r=json.loads((p/'actual-residue-cusp-stabilizer-route-1810.json').read_text())
rf='source-actual-residue-cusp-stabilizer-audit-route-1813'
write(rf+'.json',json.dumps(r,indent=2)+'\n')
write('Dubon Actual Residue Cusp Stabilizer Assessment 2026-10-29.md','# Actual residue cusp stabilizer — 29 October 2026\n\n'+r['chain']+'\n\n'+r['shorterRoute']+'\n\n'+r['remaining']+'\n\nScratch-audited only; promotion and assembled verification remain pending. Frozen paper, root pins and owner-only BAT unchanged.\n')
s=(p/'record_prescribed_residue_cusp_chart_1790.py').read_text()
for a,b in [('source-prescribed-residue-cusp-chart-1',stem),('SourcePrescribedResidueCuspChartAudit1','SourceActualResidueCuspStabilizerAudit1'),('SourcePrescribedResidueCuspChartDependencyAudit1','SourceActualResidueCuspStabilizerDependencyAudit1'),('SourcePrescribedResidueCuspChartScratchOwnership1790','SourceActualResidueCuspStabilizerScratchOwnership1813'),('source-prescribed-residue-cusp-chart-audit-route-1790',rf),('PRESCRIBED RESIDUE CUSP CHART','ACTUAL RESIDUE CUSP STABILIZER'),('(2, 2, 10)','(7, 9, 20)'),('modules=2','modules=7'),('queries=2','queries=9'),('linterScopes=2','linterScopes=7'),("text.count('with 16 linters') == 2","text.count('with 16 linters') == 7"),('all 10 required','all 20 required'),('requiredProofValueEdges=10','requiredProofValueEdges=20'),('proofEdges=10','proofEdges=20')]:s=s.replace(a,b)
ast.parse(s);write('record_actual_residue_cusp_stabilizer_1813.py',s)
s=(p/'audit_prescribed_residue_cusp_chart_1790.ps1').read_text()
for a,b in [('SourcePrescribedResidueCuspChartAudit1','SourceActualResidueCuspStabilizerAudit1'),('SourcePrescribedResidueCuspChartDependencyAudit1','SourceActualResidueCuspStabilizerDependencyAudit1'),('SourcePrescribedResidueCuspChartScratchOwnership1790','SourceActualResidueCuspStabilizerScratchOwnership1813'),('record_prescribed_residue_cusp_chart_1790','record_actual_residue_cusp_stabilizer_1813')]:s=s.replace(a,b)
write('audit_actual_residue_cusp_stabilizer_1813.ps1',s)
s=(p/'build_prescribed_residue_cusp_chart_canonical_1790.ps1').read_text()
s=re.sub(r'\$names=@\([^\n]+\)',"$names=@("+','.join(repr(m) for m in mods)+')',s).replace("$ev=$base+'-1790'","$ev=$base+'-1813'").replace('audit_prescribed_residue_cusp_chart_1790','audit_actual_residue_cusp_stabilizer_1813')
write('build_actual_residue_cusp_stabilizer_canonical_1813.ps1',s)
print('Canonical translation bodies frozen; 7 modules, 9 queries, 20 VALUE edges')
