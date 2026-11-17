from pathlib import Path
import json,re,hashlib,datetime
p=Path(__file__).parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
stamp=datetime.datetime.now(datetime.timezone.utc).isoformat()
specs=[('source-original-noncm-bounded-1','source-original-noncm-bounded-audit-config-2568.json','SourceOriginalNonCMBoundedAudit1','SourceOriginalNonCMBoundedDependencyAudit1','SourceOriginalNonCMBoundedDeclarations2568')]
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
 focusedSource=(p/(an+'.lean')).read_text(encoding='utf-8')
 linted=re.findall(r'^#lint in (\S+)$',focusedSource,re.M)
 explicit=re.findall(r'`([\w.]+)',re.search(r'let modules : Array Name := #\[(.*)\]',focusedSource)[1])
 assert set(linted)==set(explicit)==set(c['modules']) and len(linted)==len(c['modules'])
 semantic=p/'SourceOriginalNonCMBoundedScratchSemantic2569.log'
 assert semantic.with_suffix('.exit').read_text().strip()=='0'
 semanticText=semantic.read_text(encoding='utf-16')
 assert not re.search(r'(warning:|error:|sorryAx|Found [1-9]|Try this:)',semanticText)
 fingerprints=re.findall(r'^SEMANTIC (\S+) (\S+): (\d+) (\d+|NONE)$',semanticText,re.M)
 assert len(fingerprints)==len({n for _,n,_,_ in fingerprints})==int(counts[1])+int(counts[2])
 assert {owner for owner,_,_,_ in fingerprints}=={'Dubon2026.'+m for m in c['modules']}

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
 review=p/'original-noncm-bounded-reuse-review-2568.json'
 receipt=dict(recordedUTC=stamp,date='2026-11-17',modules=c['modules'],files=rows,queries=c['queries'],
  theoremRegistrations=c['theorems'],constructionRegistrations=c['constructions'],separatelyAxiomChecked=[],
  log=str(p/(an+'.log')),logSha256=sha(p/(an+'.log')),auditSha256=sha(p/(an+'.lean')),
  exit=0,diagnostics=0,ownershipLog=str(p/(on+'.log')),ownershipSha256=sha(p/(on+'.log')),
  exhaustiveTheorems=int(counts[1]),exhaustiveOtherDeclarations=int(counts[2]),
  linterScopes=len(c['modules']),lintersPerScope=16,requiredProofValueEdges=len(c['proofEdges']),
  dependencyAuditLog=str(p/(dn+'.log')),dependencyAuditSha256=sha(p/(dn+'.log')),
  dependencyAuditSourceSha256=sha(p/(dn+'.lean')),consumers=c['roots'],
  reuseReview=str(review),reuseReviewSha256=sha(review),
  dependency='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> automorphy -> eventual original residual large image -> dihedral exclusion -> original nonzero inert Frobenius traces for every source primitive nontrivial quadratic character of bounded conductor. The same complete original integral/residual pair and all prior arithmetic and CM conclusions are retained. The actual dihedral-character comparison and an independent uniform conductor bound remain open.',
  boundary='Scratch PASS; production promotion, exact ownership/type/value reconciliation and full assembled verification remain pending. 16/20 accepted; DUB-17--20 OPEN.',
  productionDeclarationRenames={},rootPinsChanged=False,proofLimitsChanged=False,
  semanticFingerprints=dict(source=str(semantic.with_suffix('.lean')),sourceSha256=sha(semantic.with_suffix('.lean')),log=str(semantic),sha256=sha(semantic),declarations=len(fingerprints)))
 out=p/(tag+'-scratch-receipt.json');assert not out.exists();out.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
 summary.append(dict(receipt=out.name,sha256=sha(out),modules=len(c['modules']),queries=len(c['queries']),exhaustiveTheorems=int(counts[1]),other=int(counts[2]),requiredValueEdges=len(c['proofEdges'])))
out=p/'source-original-noncm-bounded-scratch-summary-2570.json';assert not out.exists()
out.write_text(json.dumps(dict(scopes=summary,overlappingScopes=False,distinctFinalGatesClosed=0,productionMutation=False),indent=2)+'\n')
print(json.dumps(summary))
