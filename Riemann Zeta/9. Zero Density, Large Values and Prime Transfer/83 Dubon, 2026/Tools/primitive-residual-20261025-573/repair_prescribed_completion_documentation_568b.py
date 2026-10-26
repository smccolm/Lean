from pathlib import Path
import re,json,hashlib
p=Path(__file__).parent
cfg=json.loads((p/'source-original-prescribed-completion-11-audit-config.json').read_text(encoding='utf-8'))
old=p/'SourceOriginalPrescribedCompletionAudit11'
assert old.with_suffix('.exit').read_text().strip()=='1'
t=old.with_suffix('.log').read_text(encoding='utf-16')
assert t.count('definition missing documentation string')==4
assert 'SOURCE ORIGINAL PRESCRIBED COMPLETION AUDIT PASS: 77 theorems' in t
assert not (p/'SourceOriginalPrescribedCompletionDependencyAudit11.log').exists()
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
archive=p/'prescribed-completion-568-pre-doc-audit';assert not archive.exists();archive.mkdir()
rows=[]
for name in cfg['modules']:
 for ext in ['.lean','.olean','.log','.exit']:
  source=p/(name+ext);target=archive/(source.name+('.txt' if ext=='.lean' else ''))
  target.write_bytes(source.read_bytes());rows.append(dict(source=str(source),snapshot=str(target),sha256=sha(source)))
changes={
 'SourcePrescribedReductionPrime':('sourceReductionPrime','The genuine Fourier-integer prime given by the kernel of the prescribed reduction.'),
 'SourceAdicCoefficientResidueComparison':('sourceAdicCoefficientResidueEquiv','The original integer quotient identified with the norm-valuation residue field of its completion.'),
 'SourcePrescribedCompletionResidue':('sourcePrescribedCompletionResidueMap','The actual completion residue embedding induced by the prescribed integer reduction.'),
 'SourceReductionCompletionPadicMap':('sourceReductionCompletionPadicMap','The original Tate-prime field map into the completion chosen by the reduction kernel.')}
strip=lambda s:re.sub(r'\s+','',re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',s,flags=re.S)))
for name,(decl,doc) in changes.items():
 source=p/(name+'.lean');before=source.read_text(encoding='utf-8');needle='def '+decl
 assert before.count(needle)==1
 after=before.replace(needle,'/-- '+doc+' -/\n'+needle)
 assert strip(before)==strip(after)
 source.write_text(after,encoding='utf-8')
lineage=dict(reason='Four public definition docstrings were missing. Preserve all original source, olean, compile and failed audit evidence. Add only the four required documentation comments; stripped mathematical source is identical. Fresh public and declaration-value audits will check the revised snapshots.',previousAuditSourceSha256=sha(old.with_suffix('.lean')),previousAuditLogSha256=sha(old.with_suffix('.log')),sourceSnapshots=rows,changes=changes)
f=p/'prescribed-completion-documentation-successor-568b.json';assert not f.exists();f.write_text(json.dumps(lineage,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(docstrings=4,snapshots=len(rows),lineage=str(f))))
