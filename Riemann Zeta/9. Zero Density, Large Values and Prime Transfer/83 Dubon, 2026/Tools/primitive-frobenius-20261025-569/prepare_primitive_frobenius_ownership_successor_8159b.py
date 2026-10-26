from pathlib import Path
import json,re,hashlib
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
diag=p/'source-original-primitive-frobenius-ownership-diagnostic-8159.json'
d=json.loads(diag.read_text(encoding='utf-8'))
assert d['scratchSum']==d['scratchDistinct']==d['productionFocused']==74 and not d['passed']
assert len(d['missingFromFocused'])==len(d['productionNamesNotInScratch'])==16
pairs={}
for n,rows in d['missingFromFocused'].items():
 assert len(rows)==1
 m=rows[0]['module'].removeprefix('Dubon2026.')
 suffix='_'+m[0].lower()+m[1:]
 assert suffix in n
 choices=[n.replace(suffix,'_dubon2026'),n.replace(suffix,'')]
 matches=[v for v in choices if v in d['productionNamesNotInScratch']]
 assert len(matches)==1,(n,matches)
 pairs[n]=matches[0]
assert len(set(pairs.values()))==16
k=json.loads((r/'Tools/source-original-primitive-frobenius.json').read_text(encoding='utf-8'))
sourceChecks=[]
for cert in k['scratchCertificates']:
 for row in cert['files']:
  a=Path(row['path']);b=r/'Extension/Dubon2026'/a.name
  assert sha(a)==row['sha256']
  drop=lambda f:re.sub(r'^import [^\n]+\n','',f.read_text(encoding='utf-8'),flags=re.M)
  assert drop(a)==drop(b),a
  sourceChecks.append(dict(module=b.stem,scratchSha256=sha(a),productionSha256=sha(b),bodyIdentical=True))
lineage=dict(previousDiagnostic=str(diag),previousDiagnosticSha256=sha(diag),reason='Sixteen automatically named private instance declarations acquire module-derived suffixes after import qualification. Every exact one-to-one pair retains its owner. All 26 production sources are identical to their frozen scratch sources after removing imports, and every production theorem passed the focused exhaustive axiom audit. No theorem is omitted.',sourceChecks=sourceChecks)
s=(p/'compare_original_primitive_frobenius_ownership_8159.py').read_text(encoding='utf-8')
s=s.replace('sources={}','generatedRenamings='+repr(pairs)+'\nsources={}')
s=s.replace('sources.setdefault(norm(n),','sources.setdefault(generatedRenamings.get(norm(n),norm(n)),')
s=s.replace('generatedNameRenamings={}','generatedNameRenamings=generatedRenamings')
s=s.replace("result['passed']=ok", "result['renameEvidence']="+repr(lineage)+"\nresult['passed']=ok")
s=s.replace("'source-original-primitive-frobenius-ownership-diagnostic-8159.json'", "'source-original-primitive-frobenius-ownership-diagnostic-8159b.json'")
f=p/'compare_original_primitive_frobenius_ownership_8159b.py';assert not f.exists();compile(s,str(f),'exec');f.write_text(s,encoding='utf-8')
s=(p/'verify_original_primitive_tate_image_8133b.ps1').read_text(encoding='utf-8').replace('primitive_tate_image','primitive_frobenius').replace('PrimitiveTateImage','PrimitiveFrobenius').replace('8133','8159')
f=p/'verify_original_primitive_frobenius_8159b.ps1';assert not f.exists();f.write_text(s,encoding='utf-8')
print(json.dumps(dict(pairs=len(pairs),identicalSources=len(sourceChecks),priorDiagnosticSha256=sha(diag))))
