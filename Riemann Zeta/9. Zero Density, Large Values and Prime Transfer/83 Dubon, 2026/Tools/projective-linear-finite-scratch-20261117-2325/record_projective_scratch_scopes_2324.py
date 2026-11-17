from pathlib import Path
import json,re,hashlib,datetime
s=Path(__file__).parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
stamp=datetime.datetime.now(datetime.timezone.utc).isoformat()
whole=json.loads((s/'source-projective-finite-audit-config-2321.json').read_text())
base=json.loads((s/'source-projective-linear-audit-config-2313.json').read_text())
renames={f'Dubon2026.SourceDickson.instFactPrimeOfNatNat_sourceDicksonPGLBasic{x}':
         f'Dubon2026.SourceDickson.instFactPrimeOfNatNat_dubon2026{x}' for x in ['', '_1', '_2']}
probe=s/'SourceDicksonQualifiedNames2322.log'
assert probe.with_suffix('.exit').read_text().strip()=='0'
assert set(re.findall(r'^QUALIFIED NAME (\S+)$',probe.read_text('utf-16'),re.M))==set(renames.values())
specs=[('source-projective-linear-normalized-1',base['modules'],base['files'],base['queries'],
        base['theorems'],base['constructions'],base['roots'],base['proofEdges'],
        'SourceProjectiveLinearAudit2','SourceProjectiveLinearDependencyAudit2','SourceProjectiveLinearDeclarations2311'),
       ('source-projective-finite-normalized-1',whole['modules'][23:],whole['files'][23:],whole['queries'][425:],
        [n for n in whole['theorems'] if n not in base['theorems']],
        [n for n in whole['constructions'] if n not in base['constructions']],whole['roots'],whole['proofEdges'],
        'SourceProjectiveFiniteAudit1','SourceProjectiveFiniteDependencyAudit1','SourceProjectiveFiniteDeclarations2321')]
summary=[]
for tag,mods,files,queries,theorems,defs,roots,edges,an,dn,on in specs:
 for n in [an,dn,on]:
  assert (s/(n+'.exit')).read_text().strip()=='0'
  t=(s/(n+'.log')).read_text('utf-16')
  assert not re.search(r'(warning:|error:|sorryAx|Found [1-9]|Try this:)',t)
 audit=(s/(an+'.log')).read_text('utf-16');ownership=(s/(on+'.log')).read_text('utf-16')
 counts=re.search(r'AXIOM AUDIT PASS: (\d+) theorems and (\d+) other declarations',audit);assert counts
 owners=re.findall(r'^OWNER (\S+): (\S+)$',ownership,re.M)
 public=re.findall(r'^PUBLIC (THEOREM|CONSTRUCTION) (\S+): (\S+)$',ownership,re.M)
 assert len(owners)==len({n for _,n in owners})==int(counts[1])
 assert set(queries)=={n for _,_,n in public}
 assert set(theorems)=={n for k,_,n in public if k=='THEOREM'}
 assert set(defs)=={n for k,_,n in public if k=='CONSTRUCTION'}
 assert len(re.findall(r'with 16 linters',audit))==len(mods)
 rows=[]
 for row in files:
  n=row['module'];f=s/(n+'.lean');assert sha(f)==row['canonicalSha256']
  idx=whole['modules'].index(n)
  suffix='-2321' if idx>=23 else '-2311' if idx>=15 else '-2299' if n=='SourceGammaOneProjectiveResidual' else '-2294'
  log=s/(n+suffix+'.log');ex=log.with_suffix('.exit')
  assert ex.read_text().strip()=='0' and log.stat().st_size==0
  rows.append(dict(path=str(f),sha256=sha(f),oleanSha256=sha(f.with_suffix('.olean')),compileLog=str(log),compileExit=str(ex)))
 review=s/(tag+'-reuse-review-2324.json');assert not review.exists()
 review.write_text(json.dumps(dict(recordedUTC=stamp,dependency=whole['routeAssessment'],
  pinnedDickson='ImperialCollegeLondon/FLT@478c1013cd29c27d72f57aa8b691fa46083664b3',
  nativeReuse=['fieldSL2_isPerfect','fieldSL2_mem_of_unipotents','symmetricMatrixThreeOperators_submodule_eq_top (next downstream candidate, not consumed here)',
   'IntermediateField.finiteDimensional_adjoin','Module.finite_of_finite','RingHom.codRestrict',
   'primitive_satoTate_of_entire_symmetric_continuation (existing final analytic criterion)'],
  shorterRoute='Extract the proved intermediate subgroup equalities from Dickson; native perfect SL2 lifts projective containment. Adjoin only the finitely many coefficient and conjugating-matrix entries, then descend the literal lower and upper bounds. Do not assume full SL2 over the original residue field or import a broad geometry library.',
  remaining='Six arithmetic small-image exclusions and the required original local deformation/regularity comparison; automorphy and literal higher continuation. The inspected Ribet proofs are weight-two candidates, not an all-weight substitute.',
  researchEvidence=['Tools/proof-reuse-refresh-20261117-2298/manifest.json','Tools/ribet-image-reuse-review-20261117-2314/manifest.json'],
  proofLimitsChanged=False,rootPinsChanged=False),indent=2)+'\n',encoding='utf-8')
 receipt=dict(recordedUTC=stamp,date='2026-11-17',modules=mods,files=rows,queries=queries,
  theoremRegistrations=theorems,constructionRegistrations=defs,separatelyAxiomChecked=[],
  log=str(s/(an+'.log')),logSha256=sha(s/(an+'.log')),auditSha256=sha(s/(an+'.lean')),
  exit=0,diagnostics=0,ownershipLog=str(s/(on+'.log')),ownershipSha256=sha(s/(on+'.log')),
  exhaustiveTheorems=int(counts[1]),exhaustiveOtherDeclarations=int(counts[2]),
  linterScopes=len(mods),lintersPerScope=16,requiredProofValueEdges=len(edges),
  dependencyAuditLog=str(s/(dn+'.log')),dependencyAuditSha256=sha(s/(dn+'.log')),
  dependencyAuditSourceSha256=sha(s/(dn+'.lean')),consumers=roots,
  reuseReview=str(review),reuseReviewSha256=sha(review),dependency=whole['routeAssessment'],
  boundary='Scratch PASS; production promotion, ownership/type/value comparison and full assembled verification remain pending. 16/20 accepted; DUB-17--20 OPEN.',
  productionDeclarationRenames={a:b for a,b in renames.items() if a in queries},
  qualifiedNameProbe=dict(log=str(probe),sha256=sha(probe)),rootPinsChanged=False,proofLimitsChanged=False)
 out=s/(tag+'-scratch-receipt.json');assert not out.exists();out.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
 summary.append(dict(receipt=out.name,sha256=sha(out),modules=len(mods),queries=len(queries),exhaustiveTheorems=int(counts[1]),other=int(counts[2]),requiredValueEdges=len(edges)))
out=s/'source-projective-28-scratch-summary-2324.json';assert not out.exists()
out.write_text(json.dumps(dict(scopes=summary,productionDeclarationRenames=renames,all28ModulesPass=True,
  finalConsumerRequiredValueEdges=45,distinctFinalGatesClosed=0,productionMutation=False),indent=2)+'\n',encoding='utf-8')
print(json.dumps(summary))
