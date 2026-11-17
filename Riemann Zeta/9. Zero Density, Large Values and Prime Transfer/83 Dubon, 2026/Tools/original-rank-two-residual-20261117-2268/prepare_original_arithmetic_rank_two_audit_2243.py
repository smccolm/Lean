from pathlib import Path
from datetime import datetime,timezone
import re,json,hashlib
p=Path(__file__).parent
repo=Path(r'E:\Lean\Riemann Zeta')
src=repo/'9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026/Extension/Dubon2026'
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
premap={}
for n in ['primitive-trace-audit-config-2165.json','original-local-trace-audit-config-2176.json','original-trace-algebra-audit-config-2190c.json']:
 for row in json.loads((p/n).read_text(encoding='utf-8'))['files']:
  premap[row['version']]=premap[row['module']]='Dubon2026.'+row['module']
upstreamCfg=json.loads((p/'original-rank-two-audit-config-2221.json').read_text(encoding='utf-8'))
upstreamG=json.loads((p/'original-unramified-rank-two-audit-config-2235.json').read_text(encoding='utf-8'))
upstreamCfg['files'] += upstreamG['files']
upstreamCfg['modules'] += upstreamG['modules']
for row in upstreamCfg['files']:
 premap[row['version']]=premap[row['module']]=row['module']
seen=set();versions=[];mapping={**premap}
def visit(v):
 if '.' in v or v in premap or v in seen:return
 seen.add(v);f=p/(v+'.lean');assert f.exists(),v
 for dep in re.findall(r'^import (\S+)',f.read_text(encoding='utf-8'),re.M):visit(dep)
 versions.append(v);mapping[v]=re.sub(r'\d+[a-z]$','',v)
visit('SourceGammaOneArithmeticRankTwo2242a')
assert len(versions)==6
assert 'SourceGammaOneSpanningOddTraceAlgebra2210a' not in versions
queries=[];theorems=[];constructions=[];rows=[]
def output(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
for v in versions:
 f=p/(v+'.lean');t=f.read_text(encoding='utf-8');m=mapping[v]
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,v
 assert not (src/(m+'.lean')).exists(),m
 code=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',t,flags=re.S))
 assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by)\b|set_option|nolint|trace_state|push_neg',code),v
 c=re.sub(r'^import (\S+)$',lambda x:'import '+mapping.get(x[1],x[1]),t,flags=re.M)
 assert all(x.startswith(('Dubon2026.','Mathlib.')) or x in mapping.values() for x in re.findall(r'^import (\S+)',c,re.M))
 output(m+'.lean',c)
 assert re.sub(r'^import .*\n','',t,flags=re.M)==re.sub(r'^import .*\n','',c,flags=re.M)
 ns=re.search(r'^namespace (\S+)',t,re.M)[1]+'.'
 qs=re.findall(r'^(?:noncomputable )?(theorem|lemma|def|abbrev|instance)\s+(\S+)',t,re.M)
 assert not any(k=='instance' for k,n in qs)
 queries += [ns+n for k,n in qs]
 theorems += [ns+n for k,n in qs if k in ['theorem','lemma']]
 constructions += [ns+n for k,n in qs if k not in ['theorem','lemma']]
 rows.append(dict(version=v,module=m,path=str(p/(m+'.lean')),sourceSha256=sha(f),canonicalSha256=sha(p/(m+'.lean')),mathematicalBodyIdentical=True))
assert (len(queries),len(theorems),len(constructions))==(9,9,0)
modules=[mapping[v] for v in versions]
ns='Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction.'
roots=[ns+'exists_gammaOne_original_arithmetic_rankTwo']
separate=[]
upstream=['Dubon2026.SourceFunctionField.GammaOne.binaryPrimitiveJointGaloisRep_arithmetic_descent', 'Dubon2026.absolute_continuous_normInertia_arithmetic_descent', 'Dubon2026.SourceFunctionField.GammaOne.binaryPrimitiveJointDeterminant_normInertia', 'Dubon2026.sourceUnitTrace_kernel_translate', 'Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction.exists_gammaOne_primitive_joint_original_character', 'Dubon2026.absolute_continuous_cyclic_eq_of_norm_frobenius', 'Dubon2026.continuous_positive_adic_quotient', 'Dubon2026.positiveAdic_ext', 'Dubon2026.exists_continuous_matrix_of_original_trace_kernel', 'Dubon2026.sourceTraceAction_eq_one_of_translate', 'Dubon2026.exists_continuous_matrix_of_trace_idempotent_kernel', 'Dubon2026.exists_continuous_diagonal_of_scalar_corners_kernel', 'Dubon2026.traceIdempotentPair_matrix_continuous', 'Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction.exists_gammaOne_original_local_trace', 'Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction.originalPrimitiveLocalDeterminant_odd', 'Dubon2026.sourcePrimitiveCoefficient_exists_local_structure', 'Dubon2026.sourceRationalPrimeExtensionResidue_charP']
edges=[n for n in theorems if n not in separate]+constructions+upstream
native=[src/n for n in ['AlgebraIdempotentMatrixAction.lean','AlgebraIdempotentLeftIdeal.lean','SourcePrimitiveWeightParity.lean','SourceAbsoluteCyclotomicCharacter.lean','CyclotomicConjugationPower.lean','SourceRationalLocalValuation.lean','SourceOriginalTateInertia.lean','SourcePrimitiveLocalCoefficients.lean','SourcePrimitiveResidualCharacteristic.lean','SourceGammaOneOriginalLocalTrace.lean','SourceAbsoluteCyclicFrobeniusEquality.lean','CompactSeparatedLocalAdicTopology.lean']]
native += [src/n for n in ['SourceGammaOnePrimitiveJointDescent.lean','SourceGammaOnePrimitiveJointTraceSpecialization.lean','SourceAbsoluteCyclotomicLocal.lean','SourceAbsoluteArithmeticDescent.lean','ArithmeticOriginalSupportDescent.lean']]
native += [src/'SourceAbsoluteArithmeticRestriction.lean']
native += [repo/'.lake/packages/mathlib/Mathlib'/n for n in ['LinearAlgebra/Basis/Defs.lean','Topology/Algebra/Group/Units.lean','Topology/Instances/Matrix.lean','Algebra/MonoidAlgebra/Defs.lean','Topology/Algebra/Ring/Ideal.lean']]
chain='DUB-17 Theorem2.6 / DUB-18 Corollary8.2 -> literal higher symmetric-power continuation -> automorphy -> original all-weight association -> continuous rank-two representation of the prescribed arithmetic group.'
obligations='The original primitive form of weight at least two and prime p greater than three constructs its genuine local coefficient extension and continuous two-dimensional representation of the prescribed arithmetic group, retaining original Fourier norm-Frobenius traces, weight determinants and odd complex conjugation. Finite arithmetic factors give finite trace translation invariance on the original restriction kernel. Frobenius uniqueness and adic separation transfer this to the complete trace; the faithful trace algebra and kernel-retaining matrix construction kill that kernel. Native surjective restriction and compact quotient factorization give actual continuous arithmetic descent. No supplied representation, trace, arithmetic kernel, lattice or continuity certificate remains in this consumer.'
remaining='Remaining local/image/regularity inputs, exceptional-prime scope, full original association, automorphy and literal higher symmetric-power continuation remain unresolved. Acceptance remains 16/20 and DUB-17--20 OPEN. Full scratch and subsequent assembled verification are required.'
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),date='2026-11-17',chain=chain,obligations=obligations,remaining=remaining,reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in native],publicFollowup=dict(path=str(p/'rank-two-public-reuse-followup-2219.json'),sha256=sha(p/'rank-two-public-reuse-followup-2219.json')),route='Reuse finite joint arithmetic descent, discrete determinant descent, original trace Frobenius uniqueness, adic separation and the kernel-retaining matrix consumer. Native surjective restriction and compact quotient factorization provide the actual arithmetic action with its original topology. The stable-lattice route is deferred because it is unnecessary for this descent.',deferred=['Stable-lattice construction solely for arithmetic descent: existing trace-kernel detection gives a shorter rigorous route.'],separatelyChecked=separate,failedVariantsPreserved=True,proofLimitsChanged=False,productionMutation=False)
output('original-arithmetic-rank-two-route-2243.json',json.dumps(route,indent=2)+'\n')
cfg=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),modules=modules,queries=queries,theorems=theorems,constructions=constructions,roots=roots,proofEdges=edges,separatelyAxiomChecked=separate,files=rows,routeAssessment='original-arithmetic-rank-two-route-2243.json',productionMutation=False,scope=obligations+' '+remaining)
output('original-arithmetic-rank-two-audit-config-2243.json',json.dumps(cfg,indent=2)+'\n')
imports='\n'.join('import '+m for m in modules)+'\nimport Mathlib.Tactic\n\nopen Lean\n\n'
def array(t,n,x):
 t,k=re.subn(r'^  let '+n+r' : Array Name := #\[.*$', '  let '+n+' : Array Name := #['+', '.join('`'+v for v in x)+']',t,flags=re.M);assert k==1;return t
for old,new in [('SourceOriginalTraceAlgebraAudit2','SourceOriginalArithmeticRankTwoAudit1'),('SourceOriginalTraceAlgebraDependencyAudit3','SourceOriginalArithmeticRankTwoDependencyAudit1'),('SourceOriginalTraceAlgebraScratchOwnership2190','SourceOriginalArithmeticRankTwoScratchOwnership2243')]:
 t=(p/(old+'.lean')).read_text(encoding='utf-8');t=t[t.index('private def'):]
 t=t.replace('OriginalTraceAlgebra','OriginalArithmeticRankTwo').replace('SOURCE ORIGINAL TRACE ALGEBRA','SOURCE ORIGINAL ARITHMETIC RANK TWO')
 if 'Dependency' in old:
  for n,x in [('roots',roots),('localModules',modules+upstreamCfg['modules']),('required',edges)]:t=array(t,n,x)
  a,b=t.index('  logInfo m!'),t.index('\n\n#eval')
  t=t[:a]+'  logInfo m!"SOURCE ORIGINAL ARITHMETIC RANK TWO DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the VALUE closure of the original cusp-form rank-two consumer. Original finite arithmetic factors, complete trace kernel invariance, faithful matrix-kernel detection, native restriction surjectivity, continuous factorization and original coefficient construction are consumed. Full association and DUB-17--20 remain OPEN."'+t[b:]
 elif 'Ownership' in old:t=array(t,'mods',modules)
 else:
  t=t[:t.index('\n#lint')]
  for n,x in [('modules',modules),('theorems',theorems),('constructions',constructions)]:t=array(t,n,x)
  a,b=t.index('  logInfo m!'),t.index('\n\n#eval')
  t=t[:a]+'  logInfo m!"SOURCE ORIGINAL ARITHMETIC RANK TWO AUDIT PASS: {count} theorems including private/generated declarations. Original continuous arithmetic rank-two matrices with exact Fourier and weight Frobenius values and actual oddness proved for p greater than three. Full local association and source gates remain OPEN."'+t[b:]
  t='\n'.join('#print axioms '+n for n in queries)+'\n\n'+t+'\n'+'\n'.join('#lint in '+m for m in modules)+'\n'
 output(new+'.lean',imports+t)
runner=(p/'build_original_trace_algebra_audit_2190.ps1').read_text(encoding='utf-8')
runner=runner.replace('original-trace-algebra-audit-config-2190.json','original-arithmetic-rank-two-audit-config-2243.json').replace('$taskName-2190','$taskName-2243').replace('SourceOriginalTraceAlgebraAudit1','SourceOriginalArithmeticRankTwoAudit1').replace('SourceOriginalTraceAlgebraDependencyAudit1','SourceOriginalArithmeticRankTwoDependencyAudit1').replace('SourceOriginalTraceAlgebraScratchOwnership2190','SourceOriginalArithmeticRankTwoScratchOwnership2243')
output('build_original_arithmetic_rank_two_audit_2243.ps1',runner)
print(json.dumps(dict(modules=len(modules),queries=len(queries),theorems=len(theorems),constructions=len(constructions),proofEdges=len(edges),productionMutation=False)))
