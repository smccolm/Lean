from pathlib import Path
from datetime import datetime,timezone
import ast,json,re,hashlib
s=Path(__file__).parent;sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
old=json.loads((s/'actual-peaked-auxiliary-versions-1624.json').read_text(encoding='utf-8'))
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
write('actual-peaked-auxiliary-versions-1625.json',json.dumps(versions,indent=2)+'\n')
cfg=json.loads((s/'actual-peaked-auxiliary-preflight-config-1624.json').read_text(encoding='utf-8'))
cfg.update(modules=mods,queries=cfg['theorems']+cfg['constructions'],localModules=mods,separatelyAxiomChecked=[],compileEvidence={m:m+'-1625' for m in mods})
stem='source-actual-peaked-auxiliary-1';write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
for a,b in [('SourceActualPeakedAuxiliaryPreflight1624','SourceActualPeakedAuxiliaryAudit1'),('SourceActualPeakedAuxiliaryValuePreflight1624','SourceActualPeakedAuxiliaryDependencyAudit1')]:
 c=(s/(a+'.lean')).read_text(encoding='utf-8')
 for n,v in old.items():c=c.replace(n+v,n)
 for key in ['theorems','constructions','roots']:
  c=re.sub(r'let '+key+r' : Array Name := #\[[^\n]*\]','let '+key+' : Array Name := '+arr(cfg[key]),c)
 c=re.sub(r'let required : Array Name := #\[[^\n]*\]','let required : Array Name := '+arr(cfg['proofEdges']),c)
 c=c.replace('ACTUAL PEAKED AUXILIARY PREFLIGHT','ACTUAL PEAKED AUXILIARY');write(b+'.lean',c)
c=(s/'SourceIntegralTraceScratchOwnership1532.lean').read_text(encoding='utf-8')
c='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+c[c.index('\nopen Lean'):]
c=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),c)
write('SourceActualPeakedAuxiliaryScratchOwnership1625.lean',c)
report='Dubon Actual Peaked Auxiliary Assessment 2026-10-28.md'
write(report,'''# Actual peaked auxiliary — 28 October 2026

The exact unresolved chain is DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 → literal higher continuation → automorphy → original all-weight characteristic-zero association → original Gamma1 degree/genus preservation → reduced field action → level-power slash integrality → even-weight trace. This scope discharges the actual peaked-auxiliary existence input to that trace route. Acceptance remains 16/20; DUB-17–20 OPEN.

The final exists_gamma1_peaked_auxiliary_form_twelve_dvd constructs an actual Gamma1 modular form for every N≥2. It proves weight divisible by twelve, strict weight/leading-order gap, positive decay gap, level-cleared integral slash-S and width-one coefficients, vanishing below the exact leading order, a nonzero leading coefficient with level-cleared integral inverse, and the source exponential decay away from the two exceptional signed cusp classes. These properties are conclusions of the construction, not an auxiliary certificate or theorem-equivalent premise.

The [pinned even-weight source](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_SiegelUnit_exists_gamma1_peaked_auxiliary_form_twelve_dvd.lean) is shortened without changing its existential endpoint. Multiplying the already constructed separating exponent family by N makes its infinity order a visible multiple of N, avoiding the candidate's additive-orbit divisibility theory. A finite sum of absolute cusp orders supplies the discriminant power. Its nonnegative shifted orders allow the actual translated series to be identified directly with native coefficient uniqueness and conjugate strict periods, avoiding a separate GammaS construction and negative-order argument. The resulting source theorem has no nonnegative-order or exponent-existence premise.

The existing integral discriminant expansion, sparse series reindexing, coefficient width change and Gamma1 periods are reused. The actual normalized discriminant has an integral series with constant coefficient one. The actual shifted Siegel/discriminant series is identified with the original modular form, so width-one vanishing and leading inverse statements concern its real Fourier coefficients. Strict integer cusp separation gives the exact positive gap 1/N. The candidate's duplicate Eisenstein divisibility and absolute-convergence frameworks are omitted. No source attribute suppression or raised proof limit is adopted.

All ten versioned modules passed exhaustive axiom checks, sixteen linters each and value-only dependency checks rooted in the complete actual auxiliary theorem. Canonical scratch ownership, axiom and dependency evidence are recorded separately. No external build/direct import or changed root pin is claimed.

The auxiliary must still be applied to the already proved even-weight trace theorem on the correct conjugate subgroup. Uniform level-power slash integrality, reduced field action, signed-index lower bound, degree/genus preservation, integral parabolic transfer, characteristic-zero realization, automorphy and literal higher continuation remain open. This scope awaits production promotion and assembled verification; it closes the auxiliary-existence input, not a Dubon acceptance gate.
''')
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher continuation -> automorphy -> original all-weight characteristic-zero association -> original Gamma1 degree/genus preservation -> reduced field action -> level-power slash integrality -> even-weight trace -> constructed actual peaked auxiliary.',reuseChecked=[dict(path=str(s/n),sha256=sha(s/n)) for n in ['peaked-qexp-reuse-review-1610.json','peaked-cusp-shorter-route-1619.json',report]],shorterRoute='Scale the actual separating exponent family by N to obtain source order divisibility; choose a finite absolute-order bound for the discriminant power. Use native integral discriminant expansion, sparse reindexing, width change and conjugate periods to identify actual shifted coefficients. Nonnegative orders are derived before translated series assembly. The exact source existential endpoint is preserved.',assumptionsToDischarge=['The actual separating exponent family has level-multiple positive infinity order and retains strict separation.','A concrete discriminant power makes every actual cusp order nonnegative.','The actual width-one expansion has the exact leading order, nonzero leading coefficient and level-cleared inverse.','The actual translated Fourier coefficients are integral, yielding the required slash-S coefficients.','The actual Gamma1 modular form has weight divisible by twelve, strict weight/order gap and separated decay with positive gap 1/N.','The source peaked-auxiliary existence premise is completely discharged.'],remaining='Apply the constructed auxiliary to the even-weight trace theorem on the correct conjugate subgroup. Uniform level-power slash integrality, reduced field action, signed-index lower bound, degree/genus preservation, integral parabolic transfer, characteristic-zero realization, automorphy and literal higher continuation remain open. Acceptance remains 16/20; DUB-17--20 OPEN.',externalBuild=False,externalImport=False,rootPinsChanged=False,proofLimitsChanged=False)
rf='source-actual-peaked-auxiliary-audit-route-1625.json';write(rf,json.dumps(route,indent=2)+'\n')
c=(s/'record_siegel_function_1580.py').read_text(encoding='utf-8')
for a,b in [('source-siegel-function-1',stem),('SourceSiegelFunctionAudit1','SourceActualPeakedAuxiliaryAudit1'),('SourceSiegelFunctionDependencyAudit1','SourceActualPeakedAuxiliaryDependencyAudit1'),('SourceSiegelFunctionScratchOwnership1580','SourceActualPeakedAuxiliaryScratchOwnership1625'),('source-siegel-function-audit-route-1580',rf[:-5]),('SIEGEL FUNCTION','ACTUAL PEAKED AUXILIARY')]:c=c.replace(a,b)
nm,nq,ne=len(mods),len(cfg['queries']),len(cfg['proofEdges'])
c=c.replace('(19, 101, 110)',str((nm,nq,ne))).replace('modules=19',f'modules={nm}').replace('queries=101',f'queries={nq}').replace('linterScopes=19',f'linterScopes={nm}').replace("text.count('with 16 linters') == 19",f"text.count('with 16 linters') == {nm}").replace('all 110 required',f'all {ne} required').replace('requiredProofValueEdges=110',f'requiredProofValueEdges={ne}').replace('proofEdges=110',f'proofEdges={ne}')
ast.parse(c);write('record_actual_peaked_auxiliary_1625.py',c)
c=(s/'audit_siegel_function_1580.ps1').read_text(encoding='utf-8')
for a,b in [('SourceSiegelFunctionAudit1','SourceActualPeakedAuxiliaryAudit1'),('SourceSiegelFunctionDependencyAudit1','SourceActualPeakedAuxiliaryDependencyAudit1'),('SourceSiegelFunctionScratchOwnership1580','SourceActualPeakedAuxiliaryScratchOwnership1625'),('record_siegel_function_1580','record_actual_peaked_auxiliary_1625')]:c=c.replace(a,b)
write('audit_actual_peaked_auxiliary_1625.ps1',c)
c=(s/'build_siegel_function_canonical_1580.ps1').read_text(encoding='utf-8')
c=re.sub(r'\$names=@\([^\n]+\)',"$names=@("+','.join(repr(m) for m in mods)+')',c).replace("$ev=$base+'-1580'","$ev=$base+'-1625'").replace('audit_siegel_function_1580','audit_actual_peaked_auxiliary_1625')
write('build_actual_peaked_auxiliary_canonical_1625.ps1',c)
print(json.dumps(dict(modules=nm,queries=nq,edges=ne,status='Canonical mathematical bodies and comments frozen.')))
