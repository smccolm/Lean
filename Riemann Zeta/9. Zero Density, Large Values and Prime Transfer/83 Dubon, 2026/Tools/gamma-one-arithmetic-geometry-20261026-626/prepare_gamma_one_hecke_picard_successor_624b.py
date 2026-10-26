from pathlib import Path
import json,re,hashlib
p=Path(r'E:\Lean\.tmp\dubon83');sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
old='gamma1-actual-picard-hecke-route-624.json';new='gamma1-actual-picard-hecke-route-624b.json'
r=json.loads((p/old).read_text());r.pop('scratchImportClosure')
r['auditSuccessor']=dict(reason='The public/exhaustive axiom and all sixteen-per-module linters passed. The value-only dependency audit correctly found that the specialized wrapper names heckeDivisor and heckePicard occur in consumer types, while the proof values call the actual generic correspondence directly. Audit their construction values as explicit additional roots, as well as all three consumer proofs. This checks the actual operator bodies without traversing types, excluding declarations, adding premises or changing source.',failedAudit=str(p/'SourceGammaOneHeckePicardDependencyAudit2.log'),failedAuditSha256=sha(p/'SourceGammaOneHeckePicardDependencyAudit2.log'),sourceUnchanged=True)
def out(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
out(new,json.dumps(r,indent=2)+'\n')
s=(p/'prepare_gamma_one_hecke_picard_audit_624.py').read_text(encoding='utf-8')
roots=json.loads((p/'source-gamma-one-hecke-picard-2-audit-config.json').read_text())['roots']+['Dubon2026.SourceFunctionField.GammaOne.heckeDivisor','Dubon2026.SourceFunctionField.GammaOne.heckePicard']
s=re.sub(r'^roots=.+$',lambda _:'roots='+repr(roots),s,flags=re.M)
s=s.replace('source-gamma-one-hecke-picard-2','source-gamma-one-hecke-picard-2b').replace('SourceGammaOneHeckePicardAudit2','SourceGammaOneHeckePicardAudit2b').replace('SourceGammaOneHeckePicardDependencyAudit2','SourceGammaOneHeckePicardDependencyAudit2b').replace(old,new)
s=s.replace('occur in degree-zero and principal-divisor preservation or the representative evaluation of the actual Gamma1 Picard Hecke operator.','occur in the actual Gamma1 divisor/Picard operator construction values, degree-zero and principal-divisor preservation, or representative evaluation. Construction roots are checked explicitly because definitional wrapper names in consumer types do not count as proof-value edges.')
out('prepare_gamma_one_hecke_picard_audit_624b.py',s)
s=(p/'record_gamma_one_hecke_picard_624.py').read_text(encoding='utf-8').replace('source-gamma-one-hecke-picard-2','source-gamma-one-hecke-picard-2b').replace('SourceGammaOneHeckePicardAudit2','SourceGammaOneHeckePicardAudit2b').replace('SourceGammaOneHeckePicardDependencyAudit2','SourceGammaOneHeckePicardDependencyAudit2b').replace(old,new)
out('record_gamma_one_hecke_picard_624b.py',s)
