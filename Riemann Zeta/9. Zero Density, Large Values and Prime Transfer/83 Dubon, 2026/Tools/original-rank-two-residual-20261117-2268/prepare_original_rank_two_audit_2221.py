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
seen=set();versions=[];mapping={**premap}
def visit(v):
 if '.' in v or v in premap or v in seen:return
 seen.add(v);f=p/(v+'.lean');assert f.exists(),v
 for dep in re.findall(r'^import (\S+)',f.read_text(encoding='utf-8'),re.M):visit(dep)
 versions.append(v);mapping[v]=re.sub(r'\d+[a-z]$','',v)
visit('SourceGammaOneContinuousRankTwo2217f')
assert len(versions)==25
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
assert (len(queries),len(theorems),len(constructions))==(40,34,6)
modules=[mapping[v] for v in versions]
ns='Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction.'
roots=[ns+'exists_gammaOne_original_continuous_rankTwo']
separate=['Dubon2026.traceIdempotent_offDiagonal_zero']
upstream=[ns+'exists_gammaOne_original_local_trace',ns+'exists_gammaOne_compatible_original_adic_trace',
 'Dubon2026.sourcePrimitiveCoefficient_exists_local_structure','Dubon2026.sourceRationalPrimeExtensionResidue_charP',
 'Dubon2026.sourcePrimitive_binaryDegree_even','Dubon2026.absolute_continuous_cyclic_eq_of_norm_frobenius',
 'Dubon2026.positiveAdic_ext','Dubon2026.compactSeparatedLocalRing_isAdic',
 'Dubon2026.algebraIdempotentMatrixRepresentation','Module.Basis.ofEquivFun',
 'Units.continuous_iff','Matrix.diagonalRingHom','Submodule.span_induction','MonoidHom.toHomUnits']
edges=[n for n in theorems if n not in separate]+constructions+upstream
native=[src/n for n in ['AlgebraIdempotentMatrixAction.lean','AlgebraIdempotentLeftIdeal.lean','SourcePrimitiveWeightParity.lean','SourceAbsoluteCyclotomicCharacter.lean','CyclotomicConjugationPower.lean','SourceRationalLocalValuation.lean','SourceOriginalTateInertia.lean','SourcePrimitiveLocalCoefficients.lean','SourcePrimitiveResidualCharacteristic.lean','SourceGammaOneOriginalLocalTrace.lean','SourceAbsoluteCyclicFrobeniusEquality.lean','CompactSeparatedLocalAdicTopology.lean']]
native += [repo/'.lake/packages/mathlib/Mathlib'/n for n in ['LinearAlgebra/Basis/Defs.lean','Topology/Algebra/Group/Units.lean','Topology/Instances/Matrix.lean','Algebra/MonoidAlgebra/Defs.lean','Topology/Algebra/Ring/Ideal.lean']]
chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> automorphy -> original all-weight characteristic-zero association -> genuine continuous rank-two realization with exact original Frobenius values.'
obligations='For every original PrimitiveCuspForm Q k with k at least two and prime p greater than three, construct the actual finite local coefficient field, residue characteristic p and original coefficient embedding, then a continuous representation of the original rational absolute Galois group in GL2 of that field. Every original good-prime norm Frobenius has exactly the original Fourier coefficient as trace and q^(k-1) as determinant. Actual complex conjugation has trace zero and determinant minus one. The group action, rank-two basis, spanning trace algebra, matrix continuity, oddness and Frobenius values are derived, not supplied.'
remaining='The new matrices still need the full required original unramified/local/image/regularity association bridges. Primes two and three, full original all-weight association, automorphy and literal higher symmetric-power continuation remain required. Acceptance remains 16/20 and DUB-17--20 OPEN. Focused compilation does not replace the exhaustive audits or subsequent assembled verification.'
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),date='2026-11-17',chain=chain,obligations=obligations,remaining=remaining,reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in native],publicFollowup=dict(path=str(p/'rank-two-public-reuse-followup-2219.json'),sha256=sha(p/'rank-two-public-reuse-followup-2219.json')),route='Native quotient topology and adic separation derive actual cyclotomic conjugation. Original weight parity supplies oddness. Native group-algebra induction proves group-image spanning; original trace translates prove matrix-entry continuity. Reuse the existing idempotent-left-ideal matrix action with a proved two-vector basis. Native diagonal matrices cover the other branch. Recover determinant from the 2x2 trace identity, avoiding a separate Cayley-Hamilton reconstruction. A local-field theorem followed by the existing coefficient-field construction resolves concrete elaboration timeouts without increased limits.',deferred=['SourceGammaOneSpanningOddTraceAlgebra2210a: focused PASS but not needed by the shorter final source consumer; preserved outside this production-candidate closure.'],separatelyChecked=separate,failedVariantsPreserved=True,proofLimitsChanged=False,productionMutation=False)
output('original-continuous-rank-two-route-2221.json',json.dumps(route,indent=2)+'\n')
cfg=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),modules=modules,queries=queries,theorems=theorems,constructions=constructions,roots=roots,proofEdges=edges,separatelyAxiomChecked=separate,files=rows,routeAssessment='original-continuous-rank-two-route-2221.json',productionMutation=False,scope=obligations+' '+remaining)
output('original-rank-two-audit-config-2221.json',json.dumps(cfg,indent=2)+'\n')
imports='\n'.join('import '+m for m in modules)+'\nimport Mathlib.Tactic\n\nopen Lean\n\n'
def array(t,n,x):
 t,k=re.subn(r'^  let '+n+r' : Array Name := #\[.*$', '  let '+n+' : Array Name := #['+', '.join('`'+v for v in x)+']',t,flags=re.M);assert k==1;return t
for old,new in [('SourceOriginalTraceAlgebraAudit2','SourceOriginalRankTwoAudit1'),('SourceOriginalTraceAlgebraDependencyAudit3','SourceOriginalRankTwoDependencyAudit1'),('SourceOriginalTraceAlgebraScratchOwnership2190','SourceOriginalRankTwoScratchOwnership2221')]:
 t=(p/(old+'.lean')).read_text(encoding='utf-8');t=t[t.index('private def'):]
 t=t.replace('OriginalTraceAlgebra','OriginalRankTwo').replace('SOURCE ORIGINAL TRACE ALGEBRA','SOURCE ORIGINAL RANK TWO')
 if 'Dependency' in old:
  for n,x in [('roots',roots),('localModules',modules),('required',edges)]:t=array(t,n,x)
  a,b=t.index('  logInfo m!'),t.index('\n\n#eval')
  t=t[:a]+'  logInfo m!"SOURCE ORIGINAL RANK TWO DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the VALUE closure of the original cusp-form rank-two consumer. Actual local coefficients, original traces, cyclotomic oddness, group-image spanning, both matrix cases, native coordinates and matrix continuity are consumed. Full association and DUB-17--20 remain OPEN."'+t[b:]
 elif 'Ownership' in old:t=array(t,'mods',modules)
 else:
  t=t[:t.index('\n#lint')]
  for n,x in [('modules',modules),('theorems',theorems),('constructions',constructions)]:t=array(t,n,x)
  a,b=t.index('  logInfo m!'),t.index('\n\n#eval')
  t=t[:a]+'  logInfo m!"SOURCE ORIGINAL RANK TWO AUDIT PASS: {count} theorems including private/generated declarations. Original continuous rank-two matrices with exact Fourier and weight Frobenius values and actual oddness proved for p greater than three. Full local association and source gates remain OPEN."'+t[b:]
  t='\n'.join('#print axioms '+n for n in queries)+'\n\n'+t+'\n'+'\n'.join('#lint in '+m for m in modules)+'\n'
 output(new+'.lean',imports+t)
runner=(p/'build_original_trace_algebra_audit_2190.ps1').read_text(encoding='utf-8')
runner=runner.replace('original-trace-algebra-audit-config-2190.json','original-rank-two-audit-config-2221.json').replace('$taskName-2190','$taskName-2221').replace('SourceOriginalTraceAlgebraAudit1','SourceOriginalRankTwoAudit1').replace('SourceOriginalTraceAlgebraDependencyAudit1','SourceOriginalRankTwoDependencyAudit1').replace('SourceOriginalTraceAlgebraScratchOwnership2190','SourceOriginalRankTwoScratchOwnership2221')
output('build_original_rank_two_audit_2221.ps1',runner)
print(json.dumps(dict(modules=len(modules),queries=len(queries),theorems=len(theorems),constructions=len(constructions),proofEdges=len(edges),productionMutation=False)))
