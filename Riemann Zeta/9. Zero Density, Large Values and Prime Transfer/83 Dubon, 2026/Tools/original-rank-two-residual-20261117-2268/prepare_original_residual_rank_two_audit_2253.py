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
upstreamH=json.loads((p/'original-arithmetic-rank-two-audit-config-2243.json').read_text(encoding='utf-8'))
upstreamCfg['files'] += upstreamH['files']
upstreamCfg['modules'] += upstreamH['modules']
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
visit('SourceGammaOneResidualRankTwo2252g')
assert len(versions)==7
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
assert (len(queries),len(theorems),len(constructions))==(15,12,3)
modules=[mapping[v] for v in versions]
ns='Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction.'
roots=[ns+'exists_gammaOne_original_residual_rankTwo']
separate=[]
upstream=['Dubon2026.stableLattice_integral_residual_realization', 'Dubon2026.fullIntegralLattice_free_finite_rank', 'Dubon2026.stableLatticeGeneralLinearRep_continuous', 'Dubon2026.stableLatticeGeneralLinearRep_field_action', 'Dubon2026.localFieldResidualRep_continuous', 'Dubon2026.localCoefficientResidue_finite_discrete', 'Dubon2026.sourceRationalPrimeExtensionResidue_charP', 'Dubon2026.sourcePrimitiveCoefficient_exists_local_structure', 'Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction.exists_gammaOne_original_local_arithmetic_rankTwo', 'Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction.originalPrimitiveLocalTrace_arithmetic_kernel_translate', 'Dubon2026.exists_continuous_matrix_of_original_trace_kernel', 'Dubon2026.sourceAbsoluteArithmeticRestriction_unique_factor', 'Dubon2026.SourceFunctionField.GammaOne.binaryPrimitiveJointGaloisRep_arithmetic_descent', 'Dubon2026.absolute_continuous_cyclic_eq_of_norm_frobenius', 'Dubon2026.positiveAdic_ext', 'Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction.exists_gammaOne_original_local_trace', 'Dubon2026.commonCoefficientEmbedding', 'Dubon2026.sourcePrimitiveCoefficient_valuation_le_one']
edges=[n for n in theorems if n not in separate]+constructions+upstream
native=[src/n for n in ['AlgebraIdempotentMatrixAction.lean','AlgebraIdempotentLeftIdeal.lean','SourcePrimitiveWeightParity.lean','SourceAbsoluteCyclotomicCharacter.lean','CyclotomicConjugationPower.lean','SourceRationalLocalValuation.lean','SourceOriginalTateInertia.lean','SourcePrimitiveLocalCoefficients.lean','SourcePrimitiveResidualCharacteristic.lean','SourceGammaOneOriginalLocalTrace.lean','SourceAbsoluteCyclicFrobeniusEquality.lean','CompactSeparatedLocalAdicTopology.lean']]
native += [src/n for n in ['SourceGammaOnePrimitiveJointDescent.lean','SourceGammaOnePrimitiveJointTraceSpecialization.lean','SourceAbsoluteCyclotomicLocal.lean','SourceAbsoluteArithmeticDescent.lean','ArithmeticOriginalSupportDescent.lean']]
native += [src/n for n in ['SourceAbsoluteArithmeticRestriction.lean','SourceStableLatticeResidualRealization.lean','SourceStableLatticeContinuity.lean','SourceStableLatticeFieldComparison.lean','SourceIntegralLatticeRank.lean','SourceLocalFieldResidueReduction.lean','CommonCoefficientField.lean']]
native += [repo/'.lake/packages/mathlib/Mathlib'/n for n in ['LinearAlgebra/Basis/Defs.lean','Topology/Algebra/Group/Units.lean','Topology/Instances/Matrix.lean','Algebra/MonoidAlgebra/Defs.lean','Topology/Algebra/Ring/Ideal.lean','Topology/Compactness/Compact.lean','RingTheory/Noetherian/Basic.lean','LinearAlgebra/Trace.lean','LinearAlgebra/Determinant.lean','Topology/Algebra/ValuativeRel/ValuativeTopology.lean']]
chain='DUB-17 Theorem2.6 / DUB-18 Corollary8.2 -> literal higher symmetric-power continuation -> automorphy -> original all-weight association -> actual integral and residual arithmetic rank-two realization.'
obligations='The original primitive form of weight at least two and prime p greater than three constructs a genuine finite local coefficient extension, its actual finite discrete characteristic-p residue field and continuous integral/residual arithmetic representations. The integer span of the two compact basis orbits is proved finite, full, invariant, free and rank two. This discharges every lattice input of the existing integral/residual realization. Native conjugacy invariance proves the exact trace and determinant comparison. Literal entrywise reduction gives original reduced Fourier traces and weight determinants at all original good-prime norm Frobenius elements, and actual complex conjugation remains odd. No lattice, representation, Frobenius, finite-residue or continuity certificate is supplied by the source consumer.'
remaining='Residual irreducibility and large image, remaining local/regularity conditions, exceptional-prime scope, full original association, automorphy and literal higher symmetric-power continuation remain unresolved. Acceptance remains 16/20 and DUB-17--20 OPEN; full scratch and subsequent assembled verification are required.'
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),date='2026-11-17',chain=chain,obligations=obligations,remaining=remaining,reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in native],publicFollowup=dict(path=str(p/'rank-two-public-reuse-followup-2219.json'),sha256=sha(p/'rank-two-public-reuse-followup-2219.json')),route='Reuse the existing continuous integral/residual realization from an invariant lattice. Its weight-two lattice construction does not cover these actual all-weight matrices. Construct only the required compact basis-orbit lattice: native finite subcovers and Noetherianity prove finiteness, the identity proves full span, and group multiplication proves invariance. Native lattice rank/freeness and conjugacy invariance complete exact original reduction. The final concrete embedding is factored into a private generic constructor to stay within unchanged elaboration limits.',deferred=['General compact representation/lattice classifications beyond the required rank-two residue realization.'],separatelyChecked=separate,failedVariantsPreserved=True,proofLimitsChanged=False,productionMutation=False)
output('original-residual-rank-two-route-2253.json',json.dumps(route,indent=2)+'\n')
cfg=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),modules=modules,queries=queries,theorems=theorems,constructions=constructions,roots=roots,proofEdges=edges,separatelyAxiomChecked=separate,files=rows,routeAssessment='original-residual-rank-two-route-2253.json',productionMutation=False,scope=obligations+' '+remaining)
output('original-residual-rank-two-audit-config-2253.json',json.dumps(cfg,indent=2)+'\n')
imports='\n'.join('import '+m for m in modules)+'\nimport Mathlib.Tactic\n\nopen Lean\n\n'
def array(t,n,x):
 t,k=re.subn(r'^  let '+n+r' : Array Name := #\[.*$', '  let '+n+' : Array Name := #['+', '.join('`'+v for v in x)+']',t,flags=re.M);assert k==1;return t
for old,new in [('SourceOriginalTraceAlgebraAudit2','SourceOriginalResidualRankTwoAudit1'),('SourceOriginalTraceAlgebraDependencyAudit3','SourceOriginalResidualRankTwoDependencyAudit1'),('SourceOriginalTraceAlgebraScratchOwnership2190','SourceOriginalResidualRankTwoScratchOwnership2253')]:
 t=(p/(old+'.lean')).read_text(encoding='utf-8');t=t[t.index('private def'):]
 t=t.replace('OriginalTraceAlgebra','OriginalResidualRankTwo').replace('SOURCE ORIGINAL TRACE ALGEBRA','SOURCE ORIGINAL RESIDUAL RANK TWO')
 if 'Dependency' in old:
  for n,x in [('roots',roots),('localModules',modules+upstreamCfg['modules']),('required',edges)]:t=array(t,n,x)
  a,b=t.index('  logInfo m!'),t.index('\n\n#eval')
  t=t[:a]+'  logInfo m!"SOURCE ORIGINAL RESIDUAL RANK TWO DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the VALUE closure of the original cusp-form rank-two consumer. Actual compact basis orbits, finite generation, lattice rank and invariance, native integral/residual realization, trace/determinant conjugacy and original source arithmetic matrices are consumed. Full association and DUB-17--20 remain OPEN."'+t[b:]
 elif 'Ownership' in old:t=array(t,'mods',modules)
 else:
  t=t[:t.index('\n#lint')]
  for n,x in [('modules',modules),('theorems',theorems),('constructions',constructions)]:t=array(t,n,x)
  a,b=t.index('  logInfo m!'),t.index('\n\n#eval')
  t=t[:a]+'  logInfo m!"SOURCE ORIGINAL RESIDUAL RANK TWO AUDIT PASS: {count} theorems including private/generated declarations. Original continuous integral and residual arithmetic rank-two matrices with exact reduced Fourier and weight Frobenius values, finite prime-characteristic coefficients and actual oddness proved for p greater than three. Full local association and source gates remain OPEN."'+t[b:]
  t='\n'.join('#print axioms '+n for n in queries)+'\n\n'+t+'\n'+'\n'.join('#lint in '+m for m in modules)+'\n'
 output(new+'.lean',imports+t)
runner=(p/'build_original_trace_algebra_audit_2190.ps1').read_text(encoding='utf-8')
runner=runner.replace('original-trace-algebra-audit-config-2190.json','original-residual-rank-two-audit-config-2253.json').replace('$taskName-2190','$taskName-2253').replace('SourceOriginalTraceAlgebraAudit1','SourceOriginalResidualRankTwoAudit1').replace('SourceOriginalTraceAlgebraDependencyAudit1','SourceOriginalResidualRankTwoDependencyAudit1').replace('SourceOriginalTraceAlgebraScratchOwnership2190','SourceOriginalResidualRankTwoScratchOwnership2253')
output('build_original_residual_rank_two_audit_2253.ps1',runner)
print(json.dumps(dict(modules=len(modules),queries=len(queries),theorems=len(theorems),constructions=len(constructions),proofEdges=len(edges),productionMutation=False)))
