from pathlib import Path
from datetime import datetime,timezone
import ast,json,re,hashlib
s=Path(__file__).parent;sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
old=json.loads((s/'even-weight-fricke-trace-versions-1638.json').read_text(encoding='utf-8'))
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
write('even-weight-fricke-trace-versions-1643.json',json.dumps(versions,indent=2)+'\n')
cfg=json.loads((s/'even-weight-fricke-trace-preflight-config-1638.json').read_text(encoding='utf-8'))
cfg.update(modules=mods,queries=cfg['theorems']+cfg['constructions'],localModules=mods,separatelyAxiomChecked=[],compileEvidence={m:m+'-1643' for m in mods})
stem='source-even-weight-fricke-trace-1';write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
for a,b in [('SourceEvenWeightFrickeTracePreflight1638','SourceEvenWeightFrickeTraceAudit1'),('SourceEvenWeightFrickeTraceValuePreflight1638','SourceEvenWeightFrickeTraceDependencyAudit1')]:
 c=(s/(a+'.lean')).read_text(encoding='utf-8')
 for n,v in old.items():c=c.replace(n+v,n)
 for key in ['theorems','constructions','roots']:
  c=re.sub(r'let '+key+r' : Array Name := #\[[^\n]*\]','let '+key+' : Array Name := '+arr(cfg[key]),c)
 c=re.sub(r'let required : Array Name := #\[[^\n]*\]','let required : Array Name := '+arr(cfg['proofEdges']),c)
 c=c.replace('EVEN WEIGHT FRICKE TRACE PREFLIGHT','EVEN WEIGHT FRICKE TRACE');write(b+'.lean',c)
c=(s/'SourceIntegralTraceScratchOwnership1532.lean').read_text(encoding='utf-8')
c='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+c[c.index('\nopen Lean'):]
c=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),c)
write('SourceEvenWeightFrickeTraceScratchOwnership1643.lean',c)
report='Dubon Even Weight Fricke Trace Assessment 2026-10-28.md'
write(report,'''# Even-weight Fricke trace — 28 October 2026

The exact unresolved chain is DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 → literal higher continuation → automorphy → original all-weight characteristic-zero association → original Gamma1 degree/genus preservation → reduced field action → uniform level-power slash integrality. This scope applies the constructed actual peaked auxiliary to the even-weight trace on the correct conjugate subgroup. Acceptance remains 16/20; DUB-17–20 OPEN.

The theorem even_weight_coeff_slash_fricke_mem_RN proves that every actual Fricke Fourier coefficient becomes an algebraic integer after multiplication by some power of N, for every N≥2 and every even-weight Gamma1 modular form whose original Fourier coefficients have a common level-clearing power. Its proof constructs the actual translated forms, proves their required congruence invariance and coefficient identities, and consumes exists_gamma1_peaked_auxiliary_form_twelve_dvd. There is no remaining auxiliary, decay, leading-unit or trace-decomposition premise.

The exponent in that theorem may depend on the coefficient. The separately conditional even_weight_level_power_fricke_of_common_denominator proves that a supplied nonzero common integer denominator D gives the single level exponent D for every coefficient. The Bezout/factorization argument is proved. Construction of that common integer denominator remains required; the uniform theorem is not yet unconditional.

The [pinned source](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_isIntegral_level_pow_mul_qExpansion_slash_fricke_coeff.lean) is adapted using the repository's actual frickeMatrix, triangular Hecke slash formula, subgroup restriction, S-square identity, strict periods, coefficient uniqueness and even-weight negation. The conjugate subgroup is defined directly by the SL2 conjugation comap, with its literal membership identity proved. The original integral-ratio field admits even-weight representatives, so odd-weight auxiliary machinery is not needed on this dependency chain.

All six versioned modules passed exhaustive axiom checks, sixteen linters each and all 44 required proof-value dependency checks. Canonical scratch ownership, axiom and dependency receipts are recorded separately. The checked scope has 25 public theorems and seven definitions. No proof limits, root pins or source contract changed; no external build or direct import is claimed.

This scope awaits production promotion and assembled verification. A common denominator, the uniform full slash theorem, reduced field action on every rational relation, the signed-index lower bound and original degree/genus preservation remain open. Integral parabolic transfer, characteristic-zero realization, automorphy and literal higher continuation remain required. No Dubon acceptance gate is claimed closed.
''')
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain='DUB-17 Theorem2.6 / DUB-18 Cor8.2 -> literal higher continuation -> automorphy -> original characteristic-zero association -> original Gamma1 degree/genus -> reduced field action -> uniform level-power slash integrality -> actual even-weight Fricke trace.',reuseChecked=[dict(path=str(s/n),sha256=sha(s/n)) for n in ['fricke-trace-reuse-review-1630.json','fricke-trace-minimality-review-1636.json',report]],shorterRoute='Reuse actual Fricke and triangular Hecke matrices, native subgroup restriction, S-square identity, strict periods and even-weight negation. Direct SL2 conjugation comap avoids a GL-injectivity detour. Apply the constructed twelve-divisible auxiliary; the original even-weight ratio theorem removes any need for an odd-weight branch.',assumptionsToDischarge=['The actual trace subgroup has finite index and both required translations.','The original transformed forms have the exact Fourier normalization and slash identities.','The constructed actual auxiliary discharges all auxiliary inputs in the even-weight Fricke trace.','Every actual Fricke coefficient is integral after a coefficient-dependent level power.','A common nonzero integer denominator implies one common level exponent by proved Bezout and factorization.'],remaining='Construct the common integer denominator and assemble uniform full slash integrality. Reduced field action, signed-index lower bound, original degree/genus preservation, integral parabolic transfer, characteristic-zero realization, automorphy and literal higher continuation remain open. Acceptance remains 16/20; DUB-17--20 OPEN.',externalBuild=False,externalImport=False,rootPinsChanged=False,proofLimitsChanged=False)
rf='source-even-weight-fricke-trace-audit-route-1643.json';write(rf,json.dumps(route,indent=2)+'\n')
c=(s/'record_siegel_function_1580.py').read_text(encoding='utf-8')
for a,b in [('source-siegel-function-1',stem),('SourceSiegelFunctionAudit1','SourceEvenWeightFrickeTraceAudit1'),('SourceSiegelFunctionDependencyAudit1','SourceEvenWeightFrickeTraceDependencyAudit1'),('SourceSiegelFunctionScratchOwnership1580','SourceEvenWeightFrickeTraceScratchOwnership1643'),('source-siegel-function-audit-route-1580',rf[:-5]),('SIEGEL FUNCTION','EVEN WEIGHT FRICKE TRACE')]:c=c.replace(a,b)
nm,nq,ne=len(mods),len(cfg['queries']),len(cfg['proofEdges'])
c=c.replace('(19, 101, 110)',str((nm,nq,ne))).replace('modules=19',f'modules={nm}').replace('queries=101',f'queries={nq}').replace('linterScopes=19',f'linterScopes={nm}').replace("text.count('with 16 linters') == 19",f"text.count('with 16 linters') == {nm}").replace('all 110 required',f'all {ne} required').replace('requiredProofValueEdges=110',f'requiredProofValueEdges={ne}').replace('proofEdges=110',f'proofEdges={ne}')
ast.parse(c);write('record_even_weight_fricke_trace_1643.py',c)
c=(s/'audit_siegel_function_1580.ps1').read_text(encoding='utf-8')
for a,b in [('SourceSiegelFunctionAudit1','SourceEvenWeightFrickeTraceAudit1'),('SourceSiegelFunctionDependencyAudit1','SourceEvenWeightFrickeTraceDependencyAudit1'),('SourceSiegelFunctionScratchOwnership1580','SourceEvenWeightFrickeTraceScratchOwnership1643'),('record_siegel_function_1580','record_even_weight_fricke_trace_1643')]:c=c.replace(a,b)
write('audit_even_weight_fricke_trace_1643.ps1',c)
c=(s/'build_siegel_function_canonical_1580.ps1').read_text(encoding='utf-8')
c=re.sub(r'\$names=@\([^\n]+\)',"$names=@("+','.join(repr(m) for m in mods)+')',c).replace("$ev=$base+'-1580'","$ev=$base+'-1643'").replace('audit_siegel_function_1580','audit_even_weight_fricke_trace_1643')
write('build_even_weight_fricke_trace_canonical_1643.ps1',c)
print(json.dumps(dict(modules=nm,queries=nq,edges=ne,status='Canonical mathematical bodies and comments frozen.')))
