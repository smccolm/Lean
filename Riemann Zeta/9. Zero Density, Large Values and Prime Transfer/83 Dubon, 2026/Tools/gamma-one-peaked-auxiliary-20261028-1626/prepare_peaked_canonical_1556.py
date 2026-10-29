from pathlib import Path
from datetime import datetime,timezone
import ast,hashlib,json,re
s=Path(__file__).parent;sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
versions=json.loads((s/'peaked-exponent-versions-1555.json').read_text(encoding='utf-8'))
mods=list(versions);ths=[];defs=[]
def write(n,t):
 f=s/n;assert not f.exists(),f;f.write_text(t,encoding='utf-8')
for m,v in versions.items():
 f=s/(m+v+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 c=f.read_text(encoding='utf-8')
 for nm,ver in versions.items():c=c.replace('import '+nm+ver+'\n','import '+nm+'\n')
 write(m+'.lean',c)
 code=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',c,flags=re.S));ns=re.search(r'^namespace (\S+)',code,re.M)[1]+'.'
 ths += [ns+x for x in re.findall(r'^theorem\s+([\w.\x27]+)',code,re.M)]
 defs += [ns+x for x in re.findall(r'^(?:noncomputable )?def\s+([\w.\x27]+)',code,re.M)]
ns='Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.'
roots=[ns+'exists_peaked_exponent_on_actual_cusps']
edges=ths+defs+['hasSum_one_div_nat_pow_mul_cos','DirichletCharacter.LSeries_ne_zero_of_one_lt_re','ZMod.dft','LinearEquiv.map_eq_zero_iff','ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq','Dubon2026.SourceFunctionField.GammaOne.mem_plusMinus_iff']
assert len(set(edges))==len(edges)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,roots=roots,proofEdges=edges,localModules=mods,separatelyAxiomChecked=[],compileEvidence={m:m+'-1556' for m in mods})
stem='source-peaked-exponent-1';write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
for a,b in [('SourceIntegralTraceAudit1','SourcePeakedExponentAudit1'),('SourceIntegralTraceDependencyAudit1','SourcePeakedExponentDependencyAudit1'),('SourceIntegralTraceScratchOwnership1532','SourcePeakedExponentScratchOwnership1556')]:
 c=(s/(a+'.lean')).read_text(encoding='utf-8')
 c='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+c[c.index('\nopen Lean'):]
 if a=='SourceIntegralTraceAudit1':
  c=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in cfg['queries']),c,count=1)
  for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:c=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),c)
  c=re.sub(r'#lint in [^\n]+\n','',c).rstrip()+'\n\n'+''.join('#lint in '+m+'\n' for m in mods)
 elif a=='SourceIntegralTraceDependencyAudit1':
  for k,v in [('roots',roots),('localModules',mods),('required',edges)]:c=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),c)
  start=c.index(' occur in the ');end=c.index('; DUB17--20 OPEN.',start)
  c=c[:start]+' occur in the proof value closure of the actual Gamma1 cusp exponent construction. Analytic Siegel product construction, integral expansions and the leading unit remain open'+c[end:]
 else:c=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),c)
 c=c.replace('INTEGRAL TRACE','PEAKED EXPONENT').replace('Frobenius Normalization','Peaked exponent')
 write(b+'.lean',c)
report='Dubon Peaked Auxiliary Exponent Assessment 2026-10-28.md'
write(report,'''# Peaked auxiliary exponent assessment — 28 October 2026

The exact unresolved targets are DUB-17 Theorem 2.6 and DUB-18 Corollary 8.2. The selected chain is literal higher symmetric-power continuation → arithmetic automorphy → original all-weight characteristic-zero association → original Gamma1 Tate/Frobenius realization → degree/genus preservation → signed-index lower bound → reduced field action → level-power slash integrality → actual even-weight peaked auxiliary. Acceptance remains 16/20; DUB-17–20 are OPEN.

The finite prerequisite for that auxiliary is now constructed: for every N ≥ 2, an actual nonnegative integer exponent family m(r,s), invariant under s ↦ s+r, has m(0,0)=0. Its literal integer Bernoulli cusp order is positive at (1,0) and strictly larger on primitive columns outside the two source exceptional classes. The endpoint consumes actual SL(2,Z) matrices; determinant one supplies primitivity and the original signed Gamma1 classification supplies both exclusions. No exponent-existence or order-separation premise remains.

The rational Bernoulli dilates span the even residue functions. This is proved with the pinned Mathlib Bernoulli Fourier formula, existing Dirichlet L-series nonvanishing at 2, native character orthogonality, finite Fourier inversion and finite-dimensional linear algebra. Native Moebius inversion proves the totient-weighted mean cancellation, which forces the zero coefficient of the chosen profile to vanish. Clearing rational denominators and a proved nonnegative correction give the integer family. The affine-sum bound uses a direct pointwise quadratic estimate instead of the longer source gcd estimate.

The [pinned exponent construction](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_SiegelUnit_exists_peaked_exponent.lean), [Bernoulli spanning proof](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_SiegelUnit_mem_span_levelBernoulliWeight_dilate_iff_even.lean) and exact source dependencies are recorded as inert texts in peaked-auxiliary-route-review-1539.json. Apache-2.0 attribution is retained. Upstream proof-limit changes and linter suppression are not adopted; no external build or full upstream audit is claimed.

An initial versioned preflight passed the exhaustive axiom check but found one unused NeZero binder in the even-function subspace definition. It was removed. A value-dependency preflight also identified two unused helpers; both were deferred. All original source versions and failed evidence are preserved. Revised versioned modules compile without diagnostics. Canonical scratch audits and promotion evidence are separate; this report makes no production PASS claim for this scope.

The exponent theorem does not construct the analytic Siegel product. Its holomorphy, transformation law, integral Fourier expansion, leading unit and decay remain required to instantiate the proved trace endpoint. Existing SourcePowerSeriesProduct.Realized.hasSum_qParam_mul and SourceRealizedPowerSeries.Realized.tendsto_atImInfty provide exact native reuse for the next analytic branch. The complete reduced field action, degree/genus preservation, finite-modulus integral parabolic transfer, two-dimensional characteristic-zero realization, remaining arithmetic inputs, automorphy and literal higher continuation remain open.
''')
src=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
mathlib=Path(r'E:\Lean\Riemann Zeta\.lake\packages\mathlib\Mathlib')
reuse=[s/'peaked-auxiliary-route-review-1539.json',s/'peaked-exponent-trim-review-1555.json',s/report,src/'SourceGammaOnePlusMinus.lean',src/'SourcePowerSeriesProduct.lean',src/'SourceRealizedPowerSeries.lean',mathlib/'NumberTheory/ZetaValues.lean',mathlib/'NumberTheory/LSeries/Dirichlet.lean',mathlib/'Analysis/Fourier/ZMod.lean',mathlib/'NumberTheory/ArithmeticFunction/Moebius.lean']
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> original Gamma1 Tate/Frobenius realization -> degree/genus preservation -> signed-index lower bound -> reduced field action -> level-power slash integrality -> even-weight peaked auxiliary existence -> actual integer exponent family and cusp-order separation.',reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],shorterRoute='Use existing Fourier inversion, Bernoulli expansion, character orthogonality and Dirichlet L(2,chi) nonvanishing. Use a pointwise bound for the affine sum. Defer two unused helpers and remove an unnecessary NeZero parameter. Existing exact power-series multiplication and cusp limits are reserved for the next analytic branch.',assumptionsToDischarge=['Bernoulli dilates span the actual even rational residue functions.','The totient-weighted mean vanishes for every nonzero Bernoulli dilate.','An actual nonnegative integer exponent family exists with zero (0,0) exponent, translation invariance and positive strictly separated source cusp orders.','Determinant-one columns are primitive and the source exceptional residue conditions coincide with the original signed Gamma1 cusp classes.'],remaining='Actual analytic Siegel product construction, its integral expansions, leading unit and decay; level-power slash integrality; reduced field action; degree/genus preservation; integral parabolic transfer; two-dimensional characteristic-zero realization; arithmetic automorphy and literal higher continuation. Acceptance remains 16/20; DUB-17--20 OPEN.',externalBuild=False,externalImport=False,rootPinsChanged=False,proofLimitsChanged=False)
rf='source-peaked-exponent-audit-route-1556.json';write(rf,json.dumps(route,indent=2)+'\n')
c=(s/'record_integral_trace_1532.py').read_text(encoding='utf-8')
for a,b in [('source-integral-trace-1',stem),('SourceIntegralTraceAudit1','SourcePeakedExponentAudit1'),('SourceIntegralTraceDependencyAudit1','SourcePeakedExponentDependencyAudit1'),('SourceIntegralTraceScratchOwnership1532','SourcePeakedExponentScratchOwnership1556'),('source-integral-trace-audit-route-1532',rf[:-5]),('INTEGRAL TRACE','PEAKED EXPONENT')]:c=c.replace(a,b)
nm,nq,ne=len(mods),len(cfg['queries']),len(edges)
c=c.replace('(21, 44, 54)',str((nm,nq,ne))).replace('modules=21',f'modules={nm}').replace('queries=44',f'queries={nq}').replace('linterScopes=21',f'linterScopes={nm}').replace("text.count('with 16 linters') == 21",f"text.count('with 16 linters') == {nm}").replace('all 54 required',f'all {ne} required').replace('requiredProofValueEdges=54',f'requiredProofValueEdges={ne}').replace('proofEdges=54',f'proofEdges={ne}')
ast.parse(c);write('record_peaked_exponent_1556.py',c)
c=(s/'audit_integral_trace_1532.ps1').read_text(encoding='utf-8')
for a,b in [('SourceIntegralTraceAudit1','SourcePeakedExponentAudit1'),('SourceIntegralTraceDependencyAudit1','SourcePeakedExponentDependencyAudit1'),('SourceIntegralTraceScratchOwnership1532','SourcePeakedExponentScratchOwnership1556'),('record_integral_trace_1532','record_peaked_exponent_1556')]:c=c.replace(a,b)
write('audit_peaked_exponent_1556.ps1',c)
c=(s/'build_integral_trace_canonical_1531.ps1').read_text(encoding='utf-8')
c=re.sub(r'\$names=@\([^\n]+\)',"$names=@("+','.join(repr(m) for m in mods)+')',c).replace("$ev=$base+'-1531'","$ev=$base+'-1556'")
c+="\n& powershell -NoProfile -ExecutionPolicy Bypass -File 'E:\\Lean\\.tmp\\dubon83\\audit_peaked_exponent_1556.ps1'\nexit $LASTEXITCODE\n"
write('build_peaked_exponent_canonical_1556.ps1',c)
print(json.dumps(dict(modules=nm,theorems=len(ths),constructions=len(defs),queries=nq,proofEdges=ne,status='Canonical mathematical bodies and comments now frozen.')))
