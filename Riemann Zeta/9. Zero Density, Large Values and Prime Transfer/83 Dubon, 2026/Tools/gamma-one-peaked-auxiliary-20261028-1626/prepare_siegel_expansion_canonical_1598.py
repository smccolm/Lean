from pathlib import Path
from datetime import datetime,timezone
import ast,json,re,hashlib
s=Path(__file__).parent;sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
old=json.loads((s/'siegel-expansion-versions-1594.json').read_text(encoding='utf-8'))
versions=old|{'SourceSiegelLeadingUnit':'1589b','SourceSiegelNormalizedProduct':'1590c','SourceSiegelCoefficientSeries':'1591c','SourceSiegelIntegralExpansion':'1592c'}
mods=list(versions)
def write(n,t):
 f=s/n;assert not f.exists(),f;f.write_text(t,encoding='utf-8')
for m,v in versions.items():
 f=s/(m+v+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 c=f.read_text(encoding='utf-8')
 for vv in [old,versions]:
  for n,ver in vv.items():c=c.replace('import '+n+ver+'\n','import '+n+'\n')
 write(m+'.lean',c)
write('siegel-expansion-versions-1598.json',json.dumps(versions,indent=2)+'\n')
cfg=json.loads((s/'siegel-expansion-preflight-config-1594.json').read_text(encoding='utf-8'))
unused='Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.EulerExpansion.zeta_ne_zero'
for key in ['theorems','proofEdges']:cfg[key].remove(unused)
cfg.update(modules=mods,queries=cfg['theorems']+cfg['constructions'],localModules=mods,separatelyAxiomChecked=[],compileEvidence={m:m+'-1598' for m in mods})
stem='source-siegel-expansion-1';write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
for a,b in [('SourceSiegelExpansionPreflight1594','SourceSiegelExpansionAudit1'),('SourceSiegelExpansionValuePreflight1594','SourceSiegelExpansionDependencyAudit1')]:
 c=(s/(a+'.lean')).read_text(encoding='utf-8')
 for n,v in old.items():c=c.replace(n+v,n)
 c=c.replace('#print axioms '+unused+'\n','')
 for key in ['theorems','constructions','roots']:
  c=re.sub(r'let '+key+r' : Array Name := #\[[^\n]*\]','let '+key+' : Array Name := '+arr(cfg[key]),c)
 c=re.sub(r'let required : Array Name := #\[[^\n]*\]','let required : Array Name := '+arr(cfg['proofEdges']),c)
 c=c.replace('SIEGEL EXPANSION PREFLIGHT','SIEGEL EXPANSION');write(b+'.lean',c)
c=(s/'SourceIntegralTraceScratchOwnership1532.lean').read_text(encoding='utf-8')
c='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+c[c.index('\nopen Lean'):]
c=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),c)
write('SourceSiegelExpansionScratchOwnership1598.lean',c)
report='Dubon Integral Siegel Expansion Assessment 2026-10-28.md'
write(report,'''# Integral Siegel expansion reuse assessment — 28 October 2026

DUB-17 Theorem 2.6 and DUB-18 Corollary 8.2 remain unresolved through literal higher continuation, automorphy, original all-weight characteristic-zero association, original Gamma1 degree/genus preservation, reduced field action, level-power slash integrality and actual peaked auxiliary existence. This scope supplies the exact integral single-factor Siegel expansion needed by that auxiliary. Acceptance remains 16/20; DUB-17–20 OPEN.

The [pinned source candidate](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_SiegelUnit_exists_isIntegral_hasSum_siegelFun.lean) builds substantial general formal-product and coefficient-majorant machinery. The source conclusion only requires actual coefficients, their integrality, the exact analytic series, the specified constant term, a level-cleared inverse and the cusp limit. The shorter faithful route adapts the repository's existing discriminant Taylor argument: finite polynomial coefficients stabilize, native locally uniform product convergence gives convergence of derivatives, and native Taylor expansion identifies the exact series. Integral coefficients follow from those actual finite polynomial products. No topological closure of integral elements is assumed.

Actual residue reindexing identifies the two sparse polynomial factor streams with the literal Siegel product. A finite geometric-sum identity proves the level-cleared leading inverse. Existing q-parameter norm control and the existing cusp-limit theorem are reused. The final public exists_integral_hasSum_siegelFun has the original nonzero-pair hypotheses and exact source conclusion. Its coefficient construction and series identity additionally work at the zero pair, enabling a shorter finite-product consumer without a dummy coefficient series.

All twelve versioned modules passed exhaustive axiom checks and sixteen linters each. The value-only preflight found one unused nonvanishing helper; it was removed in fresh versions, preserving the earlier evidence. Canonical ownership, value-dependency and axiom checks are recorded separately. No external repository build or direct import is claimed. No proof limits or root pins changed.

The finite Siegel product expansion, discriminant adjustment, source cusp orders and decay estimates still need assembly before actual peaked auxiliary existence. Reduced field action, degree/genus preservation, integral parabolic transfer, characteristic-zero realization, automorphy and literal higher continuation remain required. This is a scratch scope, pending production promotion and assembled verification.
''')
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher continuation -> automorphy -> original all-weight characteristic-zero association -> original Gamma1 degree/genus preservation -> reduced field action -> level-power slash integrality -> actual peaked auxiliary -> integral Siegel expansion.',reuseChecked=[dict(path=str(s/n),sha256=sha(s/n)) for n in ['siegel-expansion-shorter-route-1578.json','siegel-expansion-trim-review-1595.json',report]],shorterRoute='Stable finite polynomial coefficients, native locally uniform product and derivative convergence, native Taylor expansion and existing q-parameter/cusp-limit APIs replace the external general formal-product mapping and coefficient-majorant construction.',assumptionsToDischarge=['Exact normalized literal Siegel series from stable finite-product coefficients.','Every actual series coefficient is integral over the integers.','The constant coefficient is exactly the specified cyclotomic factor or one.','The level times the inverse of that constant coefficient is integral.','The normalized actual function tends to its constant coefficient at the cusp.'],remaining='Finite product expansion, discriminant adjustment, cusp orders and decay bounds, and actual peaked auxiliary existence. Reduced field action, degree/genus preservation, integral parabolic transfer, characteristic-zero realization, automorphy and literal higher continuation remain. Acceptance remains 16/20; DUB-17--20 OPEN.',externalBuild=False,externalImport=False,rootPinsChanged=False,proofLimitsChanged=False)
rf='source-siegel-expansion-audit-route-1598.json';write(rf,json.dumps(route,indent=2)+'\n')
c=(s/'record_siegel_function_1580.py').read_text(encoding='utf-8')
for a,b in [('source-siegel-function-1',stem),('SourceSiegelFunctionAudit1','SourceSiegelExpansionAudit1'),('SourceSiegelFunctionDependencyAudit1','SourceSiegelExpansionDependencyAudit1'),('SourceSiegelFunctionScratchOwnership1580','SourceSiegelExpansionScratchOwnership1598'),('source-siegel-function-audit-route-1580',rf[:-5]),('SIEGEL FUNCTION','SIEGEL EXPANSION')]:c=c.replace(a,b)
nm,nq,ne=len(mods),len(cfg['queries']),len(cfg['proofEdges'])
c=c.replace('(19, 101, 110)',str((nm,nq,ne))).replace('modules=19',f'modules={nm}').replace('queries=101',f'queries={nq}').replace('linterScopes=19',f'linterScopes={nm}').replace("text.count('with 16 linters') == 19",f"text.count('with 16 linters') == {nm}").replace('all 110 required',f'all {ne} required').replace('requiredProofValueEdges=110',f'requiredProofValueEdges={ne}').replace('proofEdges=110',f'proofEdges={ne}')
ast.parse(c);write('record_siegel_expansion_1598.py',c)
c=(s/'audit_siegel_function_1580.ps1').read_text(encoding='utf-8')
for a,b in [('SourceSiegelFunctionAudit1','SourceSiegelExpansionAudit1'),('SourceSiegelFunctionDependencyAudit1','SourceSiegelExpansionDependencyAudit1'),('SourceSiegelFunctionScratchOwnership1580','SourceSiegelExpansionScratchOwnership1598'),('record_siegel_function_1580','record_siegel_expansion_1598')]:c=c.replace(a,b)
write('audit_siegel_expansion_1598.ps1',c)
c=(s/'build_siegel_function_canonical_1580.ps1').read_text(encoding='utf-8')
c=re.sub(r'\$names=@\([^\n]+\)',"$names=@("+','.join(repr(m) for m in mods)+')',c).replace("$ev=$base+'-1580'","$ev=$base+'-1598'").replace('audit_siegel_function_1580','audit_siegel_expansion_1598')
write('build_siegel_expansion_canonical_1598.ps1',c)
print(json.dumps(dict(modules=nm,queries=nq,edges=ne,status='Canonical mathematical bodies and comments frozen.')))
