from pathlib import Path
from datetime import datetime,timezone
import ast,json,re,hashlib
s=Path(__file__).parent;sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
old=json.loads((s/'peaked-modular-form-versions-1609.json').read_text(encoding='utf-8'))
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
write('peaked-modular-form-versions-1612.json',json.dumps(versions,indent=2)+'\n')
cfg=json.loads((s/'peaked-modular-form-preflight-config-1609.json').read_text(encoding='utf-8'))
cfg.update(modules=mods,queries=cfg['theorems']+cfg['constructions'],localModules=mods,separatelyAxiomChecked=[],compileEvidence={m:m+'-1612' for m in mods})
stem='source-peaked-modular-form-1';write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
for a,b in [('SourcePeakedModularFormPreflight1609','SourcePeakedModularFormAudit1'),('SourcePeakedModularFormValuePreflight1609','SourcePeakedModularFormDependencyAudit1')]:
 c=(s/(a+'.lean')).read_text(encoding='utf-8')
 for n,v in old.items():c=c.replace(n+v,n)
 for key in ['theorems','constructions','roots']:
  c=re.sub(r'let '+key+r' : Array Name := #\[[^\n]*\]','let '+key+' : Array Name := '+arr(cfg[key]),c)
 c=re.sub(r'let required : Array Name := #\[[^\n]*\]','let required : Array Name := '+arr(cfg['proofEdges']),c)
 c=c.replace('PEAKED MODULAR FORM PREFLIGHT','PEAKED MODULAR FORM');write(b+'.lean',c)
c=(s/'SourceIntegralTraceScratchOwnership1532.lean').read_text(encoding='utf-8')
c='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+c[c.index('\nopen Lean'):]
c=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),c)
write('SourcePeakedModularFormScratchOwnership1612.lean',c)
report='Dubon Siegel Modular Form and Cusp Bounds Assessment 2026-10-28.md'
write(report,'''# Siegel modular form and cusp bounds — 28 October 2026

The exact unresolved chain is DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 → literal higher continuation → automorphy → original all-weight characteristic-zero association → original Gamma1 degree/genus preservation → reduced field action → level-power slash integrality → actual peaked auxiliary. Acceptance remains 16/20; DUB-17–20 OPEN.

This scope constructs the actual discriminant-adjusted finite Siegel product as a Gamma1 modular form under the explicit source hypotheses: the zero-pair exponent is zero, the exponent family is translation invariant, and every shifted cusp order is nonnegative. Holomorphy follows from the audited literal Siegel holomorphy and native discriminant cusp form. An actual invertible residue-row permutation transports the product at every SL2 cusp, preserving the original exponent family and exact Bernoulli order. The proved finite-product cusp limit and native discriminant decay yield the source exponential bound at every cusp. Those bounds supply boundedness in the actual ModularForm constructor.

The [pinned source proof](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_coe_eq_prod_siegelFun_pow_mul_discriminant_pow.lean) is split into five modules at default proof limits. Existing native Gamma0 holomorphic quotient lifting was inspected; it does not supply the explicit Gamma1 Siegel product or the required Bernoulli cusp rates. Native discriminant decay and the already proved Siegel transformation/expansion statements are reused directly.

All five versioned modules passed exhaustive axiom checks, sixteen linters each and value-only dependency checks. Canonical scratch ownership, axiom and dependency evidence are recorded separately. No external build/direct import or changed root pin is claimed.

The nonnegative shifted-order hypothesis still needs a proved choice of discriminant power for the constructed separating exponent family. Exact integral width-one coefficients, leading inverse and the comparison with separated decay also remain before actual peaked auxiliary existence. Reduced field action, degree/genus preservation, integral parabolic transfer, characteristic-zero realization, automorphy and literal higher continuation remain open. This scope is conditional where stated and awaits production promotion and assembled verification.
''')
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher continuation -> automorphy -> original all-weight characteristic-zero association -> original Gamma1 degree/genus preservation -> reduced field action -> level-power slash integrality -> actual peaked auxiliary -> literal discriminant-adjusted Gamma1 modular form and exact cusp bounds.',reuseChecked=[dict(path=str(s/n),sha256=sha(s/n)) for n in ['peaked-modular-form-route-review-1603.json',report]],shorterRoute='Reuse actual Siegel holomorphy, SL2/Gamma1 product transport, exact finite-product cusp limit and native discriminant cusp-form decay. Prove only the finite residue-row permutation, literal slash identity and actual ModularForm assembly.',assumptionsToDischarge=['Actual Siegel product times the discriminant power is holomorphic and Gamma1 invariant.','Every actual transformed product has the exact original Bernoulli cusp order.','The source exponential estimate holds at every SL2 cusp.','Explicit nonnegative shifted orders imply boundedness at every cusp and supply an actual ModularForm.'],remaining='The nonnegative shifted-order hypothesis must be discharged by selecting the discriminant power. Exact integral width-one coefficients, leading inverse and separated decay still need assembly into the actual peaked auxiliary. Reduced field action, degree/genus preservation, integral parabolic transfer, characteristic-zero realization, automorphy and literal higher continuation remain open. Acceptance remains 16/20; DUB-17--20 OPEN.',externalBuild=False,externalImport=False,rootPinsChanged=False,proofLimitsChanged=False)
rf='source-peaked-modular-form-audit-route-1612.json';write(rf,json.dumps(route,indent=2)+'\n')
c=(s/'record_siegel_function_1580.py').read_text(encoding='utf-8')
for a,b in [('source-siegel-function-1',stem),('SourceSiegelFunctionAudit1','SourcePeakedModularFormAudit1'),('SourceSiegelFunctionDependencyAudit1','SourcePeakedModularFormDependencyAudit1'),('SourceSiegelFunctionScratchOwnership1580','SourcePeakedModularFormScratchOwnership1612'),('source-siegel-function-audit-route-1580',rf[:-5]),('SIEGEL FUNCTION','PEAKED MODULAR FORM')]:c=c.replace(a,b)
nm,nq,ne=len(mods),len(cfg['queries']),len(cfg['proofEdges'])
c=c.replace('(19, 101, 110)',str((nm,nq,ne))).replace('modules=19',f'modules={nm}').replace('queries=101',f'queries={nq}').replace('linterScopes=19',f'linterScopes={nm}').replace("text.count('with 16 linters') == 19",f"text.count('with 16 linters') == {nm}").replace('all 110 required',f'all {ne} required').replace('requiredProofValueEdges=110',f'requiredProofValueEdges={ne}').replace('proofEdges=110',f'proofEdges={ne}')
ast.parse(c);write('record_peaked_modular_form_1612.py',c)
c=(s/'audit_siegel_function_1580.ps1').read_text(encoding='utf-8')
for a,b in [('SourceSiegelFunctionAudit1','SourcePeakedModularFormAudit1'),('SourceSiegelFunctionDependencyAudit1','SourcePeakedModularFormDependencyAudit1'),('SourceSiegelFunctionScratchOwnership1580','SourcePeakedModularFormScratchOwnership1612'),('record_siegel_function_1580','record_peaked_modular_form_1612')]:c=c.replace(a,b)
write('audit_peaked_modular_form_1612.ps1',c)
c=(s/'build_siegel_function_canonical_1580.ps1').read_text(encoding='utf-8')
c=re.sub(r'\$names=@\([^\n]+\)',"$names=@("+','.join(repr(m) for m in mods)+')',c).replace("$ev=$base+'-1580'","$ev=$base+'-1612'").replace('audit_siegel_function_1580','audit_peaked_modular_form_1612')
write('build_peaked_modular_form_canonical_1612.ps1',c)
print(json.dumps(dict(modules=nm,queries=nq,edges=ne,status='Canonical mathematical bodies and comments frozen.')))
