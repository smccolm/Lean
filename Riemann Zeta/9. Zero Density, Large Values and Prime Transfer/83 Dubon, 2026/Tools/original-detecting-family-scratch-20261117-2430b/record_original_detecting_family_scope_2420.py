from pathlib import Path
import json,re,hashlib,datetime
p=Path(__file__).parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
stamp=datetime.datetime.now(datetime.timezone.utc).isoformat()
specs=[('source-original-detecting-family-1','source-original-detecting-family-audit-config-2418.json','SourceOriginalDetectingFamilyAudit1','SourceOriginalDetectingFamilyDependencyAudit1','SourceOriginalDetectingFamilyDeclarations2418')]
summary=[]
for tag,config,an,dn,on in specs:
 c=json.loads((p/config).read_text())
 for n in [an,dn,on]:
  assert (p/(n+'.exit')).read_text().strip()=='0',n
  t=(p/(n+'.log')).read_text('utf-16')
  assert not re.search(r'(warning:|error:|sorryAx|Found [1-9]|Try this:)',t),n
 audit=(p/(an+'.log')).read_text('utf-16');ownership=(p/(on+'.log')).read_text('utf-16')
 counts=re.search(r'AXIOM AUDIT PASS: (\d+) theorems and (\d+) other declarations',audit);assert counts
 owners=re.findall(r'^OWNER (\S+): (\S+)$',ownership,re.M)
 public=re.findall(r'^PUBLIC (THEOREM|CONSTRUCTION) (\S+): (\S+)$',ownership,re.M)
 assert len(owners)==len({n for _,n in owners})==int(counts[1])
 assert set(c['queries'])=={n for _,_,n in public}
 assert set(c['theorems'])=={n for k,_,n in public if k=='THEOREM'}
 assert set(c['constructions'])=={n for k,_,n in public if k=='CONSTRUCTION'}
 assert len(re.findall(r'with 16 linters',audit))==len(c['modules'])
 assert 'all '+str(len(c['proofEdges']))+' required proof dependencies' in (p/(dn+'.log')).read_text('utf-16')
 rows=[]
 for row in c['files']:
  f=p/(row['module']+'.lean');assert sha(f)==row['canonicalSha256']
  src=Path(row['source']);assert sha(src)==row['sourceSha256']
  # Canonicalization must preserve the entire non-import source body exactly.
  body=lambda t:'\n'.join(x for x in t.splitlines() if not x.startswith('import '))
  assert body(src.read_text('utf-8'))==body(f.read_text('utf-8'))
  log=f.with_suffix('.log');ex=f.with_suffix('.exit')
  assert ex.read_text().strip()=='0' and log.stat().st_size==0
  rows.append(dict(path=str(f),sha256=sha(f),oleanSha256=sha(f.with_suffix('.olean')),compileLog=str(log),compileExit=str(ex)))
 review=p/'original-detecting-family-reuse-review-2420.json'
 receipt=dict(recordedUTC=stamp,date='2026-11-17',modules=c['modules'],files=rows,queries=c['queries'],
  theoremRegistrations=c['theorems'],constructionRegistrations=c['constructions'],separatelyAxiomChecked=[],
  log=str(p/(an+'.log')),logSha256=sha(p/(an+'.log')),auditSha256=sha(p/(an+'.lean')),
  exit=0,diagnostics=0,ownershipLog=str(p/(on+'.log')),ownershipSha256=sha(p/(on+'.log')),
  exhaustiveTheorems=int(counts[1]),exhaustiveOtherDeclarations=int(counts[2]),
  linterScopes=len(c['modules']),lintersPerScope=16,requiredProofValueEdges=len(c['proofEdges']),
  dependencyAuditLog=str(p/(dn+'.log')),dependencyAuditSha256=sha(p/(dn+'.log')),
  dependencyAuditSourceSha256=sha(p/(dn+'.lean')),consumers=c['roots'],
  reuseReview=str(review),reuseReviewSha256=sha(review),
  dependency='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> automorphy -> actual residual deformation inputs -> actual dimension-bounded jointly detecting regular-prime families for the same residual representation and original twisted cohomology subspaces. The large-image branch is constructed as an alternative, not assumed for the actual source form.',
  boundary='Scratch PASS; production promotion, exact ownership/type/value reconciliation and full assembled verification remain pending. 16/20 accepted; DUB-17--20 OPEN.',
  productionDeclarationRenames={},rootPinsChanged=False,proofLimitsChanged=False)
 if len(c['modules']) == 18:
  extra='SourceOriginalResidueConsumerAudit2361'
  assert (p/(extra+'.exit')).read_text().strip()=='0'
  extraText=(p/(extra+'.log')).read_text('utf-16')
  assert not re.search(r'(warning:|error:|sorryAx|Found [1-9]|Try this:)',extraText)
  assert 'all 26 required proof dependencies' in extraText
  receipt['singleOriginalConsumerAudit']={'source':str(p/(extra+'.lean')),'sourceSha256':sha(p/(extra+'.lean')),'log':str(p/(extra+'.log')),'logSha256':sha(p/(extra+'.log')),'requiredEdges':26,'edgeManifest':str(p/'source-original-residue-consumer-edges-2361.json'),'edgeManifestSha256':sha(p/'source-original-residue-consumer-edges-2361.json')}
 out=p/(tag+'-scratch-receipt.json');assert not out.exists();out.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
 summary.append(dict(receipt=out.name,sha256=sha(out),modules=len(c['modules']),queries=len(c['queries']),exhaustiveTheorems=int(counts[1]),other=int(counts[2]),requiredValueEdges=len(c['proofEdges'])))
out=p/'source-original-detecting-family-scratch-summary-2420.json';assert not out.exists()
out.write_text(json.dumps(dict(scopes=summary,overlappingScopes=False,distinctFinalGatesClosed=0,productionMutation=False),indent=2)+'\n')
print(json.dumps(summary))
