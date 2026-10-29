from pathlib import Path
from datetime import datetime,timezone
import ast,json,re,hashlib
s=Path(__file__).parent;sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
oldVersions=json.loads((s/'siegel-function-versions-1577.json').read_text(encoding='utf-8'))
versions=json.loads((s/'siegel-function-versions-1579.json').read_text(encoding='utf-8'));mods=list(versions)
def write(n,t):
 f=s/n;assert not f.exists(),f;f.write_text(t,encoding='utf-8')
for m,v in versions.items():
 f=s/(m+v+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 c=f.read_text(encoding='utf-8')
 for vv in [oldVersions,versions]:
  for n,ver in vv.items():c=c.replace('import '+n+ver+'\n','import '+n+'\n')
 write(m+'.lean',c)
cfg=json.loads((s/'siegel-function-preflight-config-1577.json').read_text(encoding='utf-8'))
cfg.update(modules=mods,queries=cfg['theorems']+cfg['constructions'],localModules=mods,separatelyAxiomChecked=[],compileEvidence={m:m+'-1580' for m in mods})
stem='source-siegel-function-1';write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
for a,b in [('SourceSiegelFunctionPreflight1577','SourceSiegelFunctionAudit1'),('SourceSiegelFunctionValuePreflight1577','SourceSiegelFunctionDependencyAudit1')]:
 c=(s/(a+'.lean')).read_text(encoding='utf-8')
 for n,v in oldVersions.items():c=c.replace(n+v,n)
 c=c.replace('SIEGEL FUNCTION PREFLIGHT','SIEGEL FUNCTION');write(b+'.lean',c)
c=(s/'SourceIntegralTraceScratchOwnership1532.lean').read_text(encoding='utf-8')
c='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+c[c.index('\nopen Lean'):]
c=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),c)
write('SourceSiegelFunctionScratchOwnership1580.lean',c)
report='Dubon Literal Siegel Function Reuse Assessment 2026-10-28.md'
write(report,'''# Literal Siegel function reuse assessment — 28 October 2026

DUB-17 Theorem 2.6 and DUB-18 Corollary 8.2 remain unresolved through the chain: literal higher continuation → arithmetic automorphy → original all-weight characteristic-zero association → original Gamma1 degree/genus preservation → reduced field action → level-power slash integrality → actual peaked auxiliary. This checkpoint removes the analytic and transformation prerequisites for the literal Siegel factors. Acceptance remains 16/20; DUB-17–20 OPEN.

Mathlib's actual two-variable Jacobi theta function is proved equal to the literal source infinite product. The finite Gaussian identity, explicit denominator bounds and dominated finite-sum limit are proved on the pinned toolchain. Existing geometric-product convergence, theta summability, eta nonvanishing and theta/eta transformation laws are reused. No proof limits are raised and no external proof package is imported.

The actual Siegel function is defined by the source exponential infinite product. Its equality with the native analytic theta function divided by the nonvanishing eta product proves holomorphy on the upper half-plane. The S and T identities, followed by native SL(2,Z) generation, derive its twelfth-root transformation multiplier. Literal level shifts give the finite-order correction when integer indices are replaced by residue representatives. The source 12*N exponents remove both multipliers. The final theorem derives the actual finite product's SL2 transport and its Gamma1 invariance from the exponent family's translation condition.

The [Jacobi product proof](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_jacobiTheta_two_eq_tprod.lean), [Siegel transformation proof](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_siegelFun_specialLinearGroup_smul.lean) and exact dependencies are recorded in siegel-jacobi-route-review-1557.json. The pinned Apache-2.0 source is inspected evidence, not a claimed external kernel audit. Duplicate geometric-product and common Siegel identities were reused or omitted. The upstream unused-section-variable suppression was replaced by removing unnecessary parameters.

The nineteen versioned modules passed exhaustive axiom checks and all sixteen linters per module. A value-dependency preflight found that the product factorization unfolded siegelFun directly instead of consuming the public literal-definition theorem; a fresh version now rewrites with that theorem and compiles without diagnostics. Old evidence is retained. Canonical scratch ownership, dependency and axiom evidence are recorded separately. This report makes no production PASS claim for this scope.

The proved exponent construction and the present analytic transformation results still need integral Fourier expansions, the level-cleared leading inverse, the discriminant adjustment and the source decay/order estimates before the actual peaked auxiliary exists. The shorter expansion route is recorded in siegel-expansion-shorter-route-1578.json: use stabilized finite-product coefficients and the existing native discriminant/Taylor method, plus the existing exact power-series product and cusp-limit theorems. Full reduced field action, degree/genus preservation, integral parabolic transfer, characteristic-zero realization, remaining arithmetic inputs, automorphy and literal higher continuation remain required.
''')
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> original Gamma1 degree/genus preservation -> reduced field action -> level-power slash integrality -> peaked auxiliary existence -> actual Siegel holomorphy, SL2 transformation and Gamma1-invariant finite product.',reuseChecked=[dict(path=str(s/n),sha256=sha(s/n)) for n in ['siegel-jacobi-route-review-1557.json','siegel-source-entry-review-1579.json','siegel-expansion-shorter-route-1578.json',report]],shorterRoute='Reuse native theta and eta APIs, native SL2 generators and native geometric-product convergence. Prove only the literal Jacobi product connection, actual Siegel factor identities and the finite product transport. Common facts are shared, and unnecessary nonzero-level parameters and unused source helpers are omitted.',assumptionsToDischarge=['The actual Jacobi theta function equals the literal infinite product.','The source Siegel factor is holomorphic on the upper half-plane.','The actual SL2 transformation multiplier is a twelfth root of unity.','Literal level shifts reduce integer indices to residues with multipliers annihilated by the source exponent.','The actual 12*N exponent product satisfies SL2 transport and Gamma1 invariance from exponent translation invariance.'],remaining='Integral Fourier expansions, level-cleared leading inverse, discriminant adjustment, source decay/order estimates and actual peaked auxiliary existence. Full reduced field action, degree/genus preservation, integral parabolic transfer, characteristic-zero realization, remaining arithmetic inputs, automorphy and literal higher continuation remain. Acceptance remains 16/20; DUB-17--20 OPEN.',externalBuild=False,externalImport=False,rootPinsChanged=False,proofLimitsChanged=False)
rf='source-siegel-function-audit-route-1580.json';write(rf,json.dumps(route,indent=2)+'\n')
c=(s/'record_peaked_exponent_1556.py').read_text(encoding='utf-8')
for a,b in [('source-peaked-exponent-1',stem),('SourcePeakedExponentAudit1','SourceSiegelFunctionAudit1'),('SourcePeakedExponentDependencyAudit1','SourceSiegelFunctionDependencyAudit1'),('SourcePeakedExponentScratchOwnership1556','SourceSiegelFunctionScratchOwnership1580'),('source-peaked-exponent-audit-route-1556',rf[:-5]),('PEAKED EXPONENT','SIEGEL FUNCTION')]:c=c.replace(a,b)
nm,nq,ne=len(mods),len(cfg['queries']),len(cfg['proofEdges'])
c=c.replace('(14, 76, 82)',str((nm,nq,ne))).replace('modules=14',f'modules={nm}').replace('queries=76',f'queries={nq}').replace('linterScopes=14',f'linterScopes={nm}').replace("text.count('with 16 linters') == 14",f"text.count('with 16 linters') == {nm}").replace('all 82 required',f'all {ne} required').replace('requiredProofValueEdges=82',f'requiredProofValueEdges={ne}').replace('proofEdges=82',f'proofEdges={ne}')
ast.parse(c);write('record_siegel_function_1580.py',c)
c=(s/'audit_peaked_exponent_1556.ps1').read_text(encoding='utf-8')
for a,b in [('SourcePeakedExponentAudit1','SourceSiegelFunctionAudit1'),('SourcePeakedExponentDependencyAudit1','SourceSiegelFunctionDependencyAudit1'),('SourcePeakedExponentScratchOwnership1556','SourceSiegelFunctionScratchOwnership1580'),('record_peaked_exponent_1556','record_siegel_function_1580')]:c=c.replace(a,b)
write('audit_siegel_function_1580.ps1',c)
c=(s/'build_integral_trace_canonical_1531.ps1').read_text(encoding='utf-8')
c=re.sub(r'\$names=@\([^\n]+\)',"$names=@("+','.join(repr(m) for m in mods)+')',c).replace("$ev=$base+'-1531'","$ev=$base+'-1580'")
c+="\n& powershell -NoProfile -ExecutionPolicy Bypass -File 'E:\\Lean\\.tmp\\dubon83\\audit_siegel_function_1580.ps1'\nexit $LASTEXITCODE\n"
write('build_siegel_function_canonical_1580.ps1',c)
print(json.dumps(dict(modules=nm,queries=nq,edges=ne,status='Canonical mathematical bodies and comments frozen.')))
