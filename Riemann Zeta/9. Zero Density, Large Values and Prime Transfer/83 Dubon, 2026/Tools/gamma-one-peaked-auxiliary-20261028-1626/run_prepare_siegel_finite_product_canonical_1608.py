from pathlib import Path
from datetime import datetime,timezone
import ast,json,re,hashlib
s=Path(__file__).parent;sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
old=json.loads((s/'siegel-finite-product-versions-1602.json').read_text(encoding='utf-8'))
versions=old.copy()
mods=list(versions)
def write(n,t):
 f=s/n;assert not f.exists(),f;f.write_text(t,encoding='utf-8')
for m,v in versions.items():
 f=s/(m+v+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 c=f.read_text(encoding='utf-8')
 for vv in [old,versions]:
  for n,ver in vv.items():c=c.replace('import '+n+ver+'\n','import '+n+'\n')
 write(m+'.lean',c)
write('siegel-finite-product-versions-1608.json',json.dumps(versions,indent=2)+'\n')
cfg=json.loads((s/'siegel-finite-product-preflight-config-1602.json').read_text(encoding='utf-8'))
cfg.update(modules=mods,queries=cfg['theorems']+cfg['constructions'],localModules=mods,separatelyAxiomChecked=[],compileEvidence={m:m+'-1608' for m in mods})
stem='source-siegel-finite-product-1';write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
for a,b in [('SourceSiegelFiniteProductPreflight1602','SourceSiegelFiniteProductAudit1'),('SourceSiegelFiniteProductValuePreflight1602','SourceSiegelFiniteProductDependencyAudit1')]:
 c=(s/(a+'.lean')).read_text(encoding='utf-8')
 for n,v in old.items():c=c.replace(n+v,n)
 for key in ['theorems','constructions','roots']:
  c=re.sub(r'let '+key+r' : Array Name := #\[[^\n]*\]','let '+key+' : Array Name := '+arr(cfg[key]),c)
 c=re.sub(r'let required : Array Name := #\[[^\n]*\]','let required : Array Name := '+arr(cfg['proofEdges']),c)
 c=c.replace('SIEGEL FINITE PRODUCT PREFLIGHT','SIEGEL FINITE PRODUCT');write(b+'.lean',c)
c=(s/'SourceIntegralTraceScratchOwnership1532.lean').read_text(encoding='utf-8')
c='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+c[c.index('\nopen Lean'):]
c=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),c)
write('SourceSiegelFiniteProductScratchOwnership1608.lean',c)
report='Dubon Finite Siegel Product Expansion Assessment 2026-10-28.md'
write(report,'''# Finite Siegel product expansion reuse assessment — 28 October 2026

DUB-17 Theorem 2.6 and DUB-18 Corollary 8.2 still require literal higher continuation through automorphy and original all-weight characteristic-zero association. This scope serves original Gamma1 degree/genus preservation through reduced field action, level-power slash integrality and actual peaked auxiliary existence. Acceptance remains 16/20; DUB-17–20 OPEN.

The [pinned finite-product source](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_SiegelUnit_exists_isIntegral_hasSum_prod_siegelFun_pow.lean) is adapted using existing native q-series multiplication and cusp limits, and audited trace coefficient multiplication/power lemmas. The explicit single-factor coefficients represent every residue pair, including the zero pair. Its exponent zero removes that factor directly. This avoids the candidate's chosen coefficient family, dummy series and duplicated coefficient algebra. Its raised heartbeat setting is not adopted.

The exact finite product has integral coefficients, the specified nonzero cyclotomic leading coefficient, an integral level-power multiple of its inverse, the literal constant phase with Nth power one, the source normalized HasSum and cusp limit. The final source consumer derives these from e(0,0)=0. Neither product convergence, coefficient integrality, nonvanishing, inverse integrality nor phase normalization is assumed.

All five versioned modules passed exhaustive axiom checks, sixteen linters per module and the value-only dependency audit. Canonical scratch ownership, axiom and value-dependency evidence are recorded separately. The single-factor existential wrapper is deliberately not needed by the finite-product proof: the actual explicit coefficients and their proved HasSum/integrality/constant-term properties are consumed directly. That shorter route retains the exact source conclusion. No external build, direct import or root-pin change is claimed.

Discriminant adjustment, exact auxiliary q-expansions, source cusp orders and decay estimates remain before the actual peaked auxiliary exists. Reduced field action, degree/genus preservation, integral parabolic transfer, characteristic-zero realization, automorphy and literal higher continuation remain required. This is a scratch scope pending production promotion and assembled verification.
''')
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher continuation -> automorphy -> original all-weight characteristic-zero association -> original Gamma1 degree/genus preservation -> reduced field action -> level-power slash integrality -> actual peaked auxiliary -> exact integral finite Siegel product expansion.',reuseChecked=[dict(path=str(s/n),sha256=sha(s/n)) for n in ['siegel-finite-product-route-review-1596.json',report]],shorterRoute='Use explicit actual coefficients for every residue pair and handle the zero pair by exponent zero. Reuse native q-series multiplication/cusp limits and audited trace coefficient algebra. Split literal phase, leading inverse and exact source assembly with default proof limits.',assumptionsToDischarge=['Actual finite Siegel product has the exact normalized series with integral coefficients.','Its specified constant coefficient is nonzero from e(0,0)=0.','The specified level power times its leading inverse is integral.','The literal constant phase has Nth power one.','The normalized actual finite product tends to its leading coefficient at the cusp.'],remaining='Discriminant adjustment, exact auxiliary q-expansions, cusp order/decay estimates and actual peaked auxiliary existence. Reduced field action, degree/genus preservation, integral parabolic transfer, characteristic-zero realization, automorphy and literal higher continuation remain. Acceptance remains 16/20; DUB-17--20 OPEN.',externalBuild=False,externalImport=False,rootPinsChanged=False,proofLimitsChanged=False)
rf='source-siegel-finite-product-audit-route-1608.json';write(rf,json.dumps(route,indent=2)+'\n')
c=(s/'record_siegel_function_1580.py').read_text(encoding='utf-8')
for a,b in [('source-siegel-function-1',stem),('SourceSiegelFunctionAudit1','SourceSiegelFiniteProductAudit1'),('SourceSiegelFunctionDependencyAudit1','SourceSiegelFiniteProductDependencyAudit1'),('SourceSiegelFunctionScratchOwnership1580','SourceSiegelFiniteProductScratchOwnership1608'),('source-siegel-function-audit-route-1580',rf[:-5]),('SIEGEL FUNCTION','SIEGEL FINITE PRODUCT')]:c=c.replace(a,b)
nm,nq,ne=len(mods),len(cfg['queries']),len(cfg['proofEdges'])
c=c.replace('(19, 101, 110)',str((nm,nq,ne))).replace('modules=19',f'modules={nm}').replace('queries=101',f'queries={nq}').replace('linterScopes=19',f'linterScopes={nm}').replace("text.count('with 16 linters') == 19",f"text.count('with 16 linters') == {nm}").replace('all 110 required',f'all {ne} required').replace('requiredProofValueEdges=110',f'requiredProofValueEdges={ne}').replace('proofEdges=110',f'proofEdges={ne}')
ast.parse(c);write('record_siegel_expansion_1608.py',c)
c=(s/'audit_siegel_function_1580.ps1').read_text(encoding='utf-8')
for a,b in [('SourceSiegelFunctionAudit1','SourceSiegelFiniteProductAudit1'),('SourceSiegelFunctionDependencyAudit1','SourceSiegelFiniteProductDependencyAudit1'),('SourceSiegelFunctionScratchOwnership1580','SourceSiegelFiniteProductScratchOwnership1608'),('record_siegel_function_1580','record_siegel_expansion_1608')]:c=c.replace(a,b)
write('audit_siegel_expansion_1608.ps1',c)
c=(s/'build_siegel_function_canonical_1580.ps1').read_text(encoding='utf-8')
c=re.sub(r'\$names=@\([^\n]+\)',"$names=@("+','.join(repr(m) for m in mods)+')',c).replace("$ev=$base+'-1580'","$ev=$base+'-1608'").replace('audit_siegel_function_1580','audit_siegel_expansion_1608')
write('build_siegel_expansion_canonical_1608.ps1',c)
print(json.dumps(dict(modules=nm,queries=nq,edges=ne,status='Canonical mathematical bodies and comments frozen.')))
