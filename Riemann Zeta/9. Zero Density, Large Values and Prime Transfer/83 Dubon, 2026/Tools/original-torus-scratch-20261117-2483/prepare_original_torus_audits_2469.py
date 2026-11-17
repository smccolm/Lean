from pathlib import Path
import ast,json,re
s=Path(__file__).parent
versions=['SourceOriginalDistinctEigenbasis2432b','SourceOriginalDiagonalConjugacy2433a','SourceOriginalMappedDistinctRoots2439e','SourcePrimeSubfieldSL2Image2440b','SourceOriginalMappedTorusConjugacy2442c','SourceOriginalSymmetricTorusRoots2444a','SourceOriginalSymmetricTorusConjugacy2445a','SourceFiniteLinearOriginalTorusDetection2443b','SourceOriginalArithmeticTorusCocycle2446b','SourceOriginalTorusPrimeLocalProperties2459a','SourceOriginalTorusPrimePredicates2447b','SourceOriginalTorusDetectionPredicate2453b','SourceOriginalPrimeTorusDimension2448a','SourceOriginalAffineTorusDimension2458a','SourceOriginalTorusDetectionAssembly2454c','SourceOriginalTorusPrimeDimensions2455e','SourceOriginalTorusPrimeAssembly2449e','SourceOriginalArithmeticTorusPrimes2450b','SourceOriginalArithmeticTorusPrimeProperty2451b','SourceGammaOneOriginalTorusPrimes2452b','SourceOriginalTorusClassPredicates2461a','SourceOriginalTorusCocycleClass2462a','SourceOriginalTorusClassPrimes2463a','SourceOriginalTorusFamilyProperty2464a','SourceOriginalTorusDetectingFamily2465a','SourceOriginalArithmeticTorusFamilies2466b','SourceGammaOneOriginalTorusFamilies2467b']
pairs=[(n,re.sub(r'\d{4}[a-z]$','',n)) for n in versions]
assert len(pairs)==len({b for _,b in pairs})==27
t=(s/'prepare_original_unramified_dimension_audits_2434.py').read_text(encoding='utf-8')
start=t.index('pairs=');end=t.index('\n\nc=dict',start)
t=t[:start]+'pairs='+repr(pairs)+t[end:]
t=t.replace("old=json.loads((s/'source-original-detecting-family-audit-config-2427.json').read_text())","old=json.loads((s/'source-original-unramified-dimension-audit-config-2434.json').read_text())")
scope=('Same original residual representation: original split-torus detecting primes with exact unramified trace-zero adjoint H1 dimension equal to the symmetric degree, and bounded jointly detecting families with that dimension at every selected prime. The explicit small-image alternative and every earlier original arithmetic, symmetric and cohomological conclusion are retained.')
review=('The actual finite linear subfield lower bound contains the canonical prime-field SL2. Its regular torus has order p-1 and eigenvalues already in the original residue field. Native distinct-eigenvector independence and basis construction produce the original diagonalizer without a general scalar-extension theorem for H1 or invariant kernels. The original root-fixing cocycle and native conjugate Chebotarev preserve one actual finite factor and local Frobenius. Native cyclic-image generation, symmetric trace invariants and the proved original-field unramified H1 comparison give exact local dimension n. Original H1 finiteness and native finite detecting families then give the bounded family. All apply to the same actual original modular-form residual witness. Small-image exclusions, remaining local deformation conditions, automorphy and literal higher continuation remain open. Default proof limits, pins and all linters are unchanged.')
t=re.sub(r" scope='[^']*'\)",lambda _: ' scope='+repr(scope)+')',t,count=1)
t=t.replace('==(5,7,6,1)','==(27,34,23,11)')
a=t.index("c['proofEdges']=");b=t.index("c['sourceAssemblyReview']=",a)
t=t[:a]+"c['proofEdges']=list(dict.fromkeys(old['proofEdges']+c['queries']+[\n 'Dubon2026.matrixTrace_invariants_finrank_of_symmetric_generator',\n 'Dubon2026.rationalArithmetic_local_frobenius_generates_representation_image',\n 'Dubon2026.rationalArithmetic_exists_conjugate_detecting_cocycle',\n 'Module.End.eigenvectors_linearIndependent\'',\n]))\n"+t[b:]
a=t.index("c['sourceAssemblyReview']=");b=t.index('\n\narr=',a)
t=t[:a]+"c['sourceAssemblyReview']="+repr(review)+t[b:]
for a,b in [
 ('SourceOriginalDetectingFamilyAudit2','SourceOriginalUnramifiedDimensionAudit2'),
 ('SourceOriginalUnramifiedDimensionAudit1','SourceOriginalTorusAudit1'),
 ('SourceOriginalDetectingFamilyDependencyAudit2','SourceOriginalUnramifiedDimensionDependencyAudit1'),
 ('SourceOriginalUnramifiedDimensionDependencyAudit1\'),','SourceOriginalTorusDependencyAudit1\'),'),
 ('SourceOriginalDetectingFamilyDeclarations2427','SourceOriginalUnramifiedDimensionDeclarations2434'),
 ('SourceOriginalUnramifiedDimensionDeclarations2434\')','SourceOriginalTorusDeclarations2469\')'),
 ('SourceOriginalDetectingFamilyScratchSemantic2428','SourceOriginalUnramifiedDimensionScratchSemantic2435'),
 ('SourceOriginalUnramifiedDimensionScratchSemantic2435.lean\',t)','SourceOriginalTorusScratchSemantic2470.lean\',t)'),
 ('SourceOriginalUnramifiedDimensionProductionSemantic2435','SourceOriginalTorusProductionSemantic2470'),
 ('source-original-unramified-dimension-audit-config-2434.json\',json.dumps','source-original-torus-audit-config-2469.json\',json.dumps'),
 ('build_original_unramified_dimensions_2434.ps1','build_original_torus_2469.ps1'),
 ("if a.endswith('Audit1') and 'Dependency' not in a:","if 'Audit' in a and 'Dependency' not in a:"),
 ("t=t.replace('SOURCE ORIGINAL DETECTING FAMILY AXIOM AUDIT PASS','SOURCE ORIGINAL UNRAMIFIED DIMENSION AXIOM AUDIT PASS')","t=t.replace('SOURCE ORIGINAL UNRAMIFIED DIMENSION AXIOM AUDIT PASS','SOURCE ORIGINAL TORUS AXIOM AUDIT PASS')"),
 ("t=t.replace('SOURCE ORIGINAL DETECTING FAMILY VALUE AUDIT PASS','SOURCE ORIGINAL UNRAMIFIED DIMENSION VALUE AUDIT PASS')","t=t.replace('SOURCE ORIGINAL UNRAMIFIED DIMENSION VALUE AUDIT PASS','SOURCE ORIGINAL TORUS VALUE AUDIT PASS')"),
 ]:
    assert a in t,a;t=t.replace(a,b)
# Replace the final runner list explicitly; seed names above remain unchanged.
start=t.index("for m in ['SourceOriginalTorusAudit1'");end=t.index(':\n',start)
t=t[:start]+"for m in ['SourceOriginalTorusAudit1','SourceOriginalTorusDependencyAudit1','SourceOriginalTorusDeclarations2469','SourceOriginalTorusScratchSemantic2470']"+t[end:]
t=t.replace('dict(modules=5,publicQueries=7,publicTheorems=6,publicConstructions=1','dict(modules=27,publicQueries=34,publicTheorems=23,publicConstructions=11')
ast.parse(t)
f=s/'generate_original_torus_audits_2469.py';assert not f.exists();f.write_text(t,encoding='utf-8')
print(json.dumps(dict(prepared=str(f),productionMutation=False,modules=27,publicQueries=34,sourceScope=scope)))
