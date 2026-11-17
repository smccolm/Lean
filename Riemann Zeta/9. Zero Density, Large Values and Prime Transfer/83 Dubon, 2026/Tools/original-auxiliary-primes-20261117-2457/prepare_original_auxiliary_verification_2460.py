from pathlib import Path
import ast,json,re

p=Path(__file__).parent
def write(name,text):
    f=p/name;assert not f.exists(),name
    if f.suffix=='.py':ast.parse(text)
    f.write_text(text,encoding='utf-8')
def rename(t):
    for a,b in [('9725','PRIOR_SCOPE'),('9755','9783'),('PRIOR_SCOPE','9755'),
        ('source-original-symmetric-residual','source-original-auxiliary-primes'),
        ('SourceOriginalSymmetricResidual','SourceOriginalAuxiliaryPrimes'),
        ('source-original-symmetric-semantic','source-original-auxiliary-semantic'),
        ('original_symmetric_residual','original_auxiliary_primes'),
        ('original_symmetric_semantics','original_auxiliary_semantics'),
        ('appliedSourceOriginalSymmetricResidual','NEXT_APPLICATION'),
        ('appliedSourceProjectiveResidualImage','appliedSourceOriginalSymmetricResidual'),
        ('NEXT_APPLICATION','appliedSourceOriginalAuxiliaryPrimes')]:t=t.replace(a,b)
    return t
for stem in ['production_ownership','global_ownership']:
    t=rename((p/f'prepare_original_symmetric_residual_{stem}_9755.py').read_text(encoding='utf-8'))
    write(f'prepare_original_auxiliary_primes_{stem}_9783.py',t)
t=rename((p/'compare_original_symmetric_residual_9755.py').read_text(encoding='utf-8'))
t=t.replace('len(certs)==4','len(certs)==3').replace('==30','==28').replace('==126','==122').replace('All 30 mathematical source bodies','All 28 mathematical source bodies')
write('compare_original_auxiliary_primes_9783.py',t)
names=['SourceOriginalRegularPrimeDeclarations2405','SourceOriginalDetectingFamilyDeclarations2427','SourceOriginalUnramifiedDimensionDeclarations2434']
write('source-original-auxiliary-primes-scratch-ownership-9783.json',json.dumps(names,indent=2)+'\n')
pairs=[('SourceOriginalRegularPrimeScratchSemantic2406','SourceOriginalRegularPrimeProductionSemantic2406',66),('SourceOriginalDetectingFamilyScratchSemantic2428','SourceOriginalDetectingFamilyProductionSemantic2428',51),('SourceOriginalUnramifiedDimensionScratchSemantic2435','SourceOriginalUnramifiedDimensionProductionSemantic2435',30)]
t=rename((p/'compare_original_symmetric_semantics_9755.py').read_text(encoding='utf-8'))
t=re.sub(r'for left,right,count in \[.*?\]:',lambda _: 'for left,right,count in '+repr(pairs)+':',t,count=1)
t=t.replace('178','147')
write('compare_original_auxiliary_semantics_9783.py',t)
t=rename((p/'record_source_original_symmetric_residual_9755b.py').read_text(encoding='utf-8'))
t=t.replace('== 126','== 122').replace('== 178','== 147').replace('== 30','== 28')
t=t.replace('"incrementModules": 30','"incrementModules": 28').replace('"linterScopes": 30','"linterScopes": 28').replace('"scratchExhaustiveTheorems": 126','"scratchExhaustiveTheorems": 122')
t=t.replace('== 4\n','== 3\n')
t=t.replace('SOURCE ORIGINAL SYMMETRIC RESIDUAL AUDIT PASS','SOURCE ORIGINAL AUXILIARY PRIMES AUDIT PASS')
t=t.replace('SOURCE ORIGINAL (?:SYMMETRIC|SYMMETRIC ADJOINT|TWISTED KERNEL|SYMMETRIC JOINT) VALUE AUDIT PASS:', 'SOURCE ORIGINAL (?:REGULAR PRIME|DETECTING FAMILY|UNRAMIFIED DIMENSION) VALUE AUDIT PASS:')
t=t.replace('9,755','9,783').replace('original symmetric residual and cohomology inputs','original regular auxiliary primes and local comparison')
t=t.replace('Four declaration-value audits verify 258 required dependency checks; a separate final-original-consumer audit verifies 26 more.','Three declaration-value audits verify 123, 138 and 151 required dependency checks, respectively.')
t=t.replace('all four source scopes','all three source scopes')
t=t.replace('Dubon Original Symmetric Residual Assessment 2026-11-17.md','Dubon Original Auxiliary Primes Assessment 2026-11-17.md')
start=t.index("    extra = p / 'SourceOriginalResidueConsumerProductionAudit")
end=t.index('    receipt = {"proofDependencyAudits": deps,',start)
t=t[:start]+t[end:]
t=t.replace(' "separateOriginalConsumerAudit": extraReceipt,','')
write('record_source_original_auxiliary_primes_9783.py',t)
t=rename((p/'preflight_original_symmetric_residual_9755.py').read_text(encoding='utf-8'))
t=t.replace('integrate_source_original_auxiliary_primes_9783b.py','integrate_source_original_auxiliary_primes_9783.py')
t=t.replace("len(scope['pending'])==30","len(scope['pending'])==28")
t=t.replace('publicQueries=44, scratchTheorems=126,scratchOtherDeclarations=52','publicQueries=40, scratchTheorems=122,scratchOtherDeclarations=25')
t=t.replace('theoremRegistrations=37,constructionRegistrations=7','theoremRegistrations=30,constructionRegistrations=10')
t=t.replace('projective-residual-image-20261117-2326','original-symmetric-residual-20261117-2388')
write('preflight_original_auxiliary_primes_9783.py',t)
t=rename((p/'archive_original_symmetric_residual_canonical_9755b.py').read_text(encoding='utf-8'))
t=t.replace('original-symmetric-residual-20261117-2388','original-auxiliary-primes-20261117-2457')
start=t.index('extra=');end=t.index('for f in sorted',start)
extra=['prepare_original_auxiliary_promotion_2457.py','prepare_original_auxiliary_verification_2460.py']
extra += [right+ext for _,right,_ in pairs for ext in ['.lean','.log','.exit']]
t=t[:start]+'extra=[p/n for n in '+repr(extra)+']\n'+t[end:]
t=t.replace('Canonical PASS of symmetric spanning, absolute irreducibility, trace-zero adjoint vanishing and arithmetic twisted-cohomology detection for the same original residual representation, retaining its integral origin and all arithmetic data and the explicit small-image alternative.','Canonical PASS of regular auxiliary-prime detection, bounded detecting families and original-field local unramified H1/invariant dimension comparison for the same original residual representation. All prior original data and the explicit small-image alternative are retained.')
write('archive_original_auxiliary_primes_canonical_9783.py',t)
t=rename((p/'verify_original_symmetric_residual_9755b.ps1').read_text(encoding='utf-8'))
t=t.replace("Invoke-TaskLean 'SourceOriginalResidueConsumerProductionAudit9783'\n",'')
start=t.index("Invoke-TaskLean 'SourceOriginalSymmetricProductionSemantic2360'")
end=t.index("python (Join-Path $taskScratch 'compare_original_auxiliary_semantics_9783.py')",start)
t=t[:start]+''.join("Invoke-TaskLean '"+right+"'\n" for _,right,_ in pairs)+t[end:]
t=t.replace('record_source_original_auxiliary_primes_9783b.py','record_source_original_auxiliary_primes_9783.py')
write('verify_original_auxiliary_primes_9783.ps1',t)
print(json.dumps(dict(prepared=True,productionMutation=False,modules=28,theorems=122,otherDeclarations=25,semanticDeclarations=147,requiredProofValueEdges=[123,138,151])))
