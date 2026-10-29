from pathlib import Path
from datetime import datetime,timezone
import ast,json,hashlib
s=Path(__file__).parent
assert not (s/'source-gamma-one-diamond-quotient-production-build-9161.log').exists()
assert not (s/'SourceGammaOneDiamondQuotientOwnership9161.log').exists()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest().upper()
rows=[]
for n,old,new in [
 ('record_source_gamma_one_diamond_quotient_9161.py','assert len(filenames) == len(k["scratchCertificates"]) == len(ownershipComparison["scopes"]) == 3','assert len(filenames) == len(k["scratchCertificates"]) == len(ownershipComparison["scopes"]) == 2'),
 ('compare_gamma_one_diamond_quotient_ownership_9161.py','assert len(names)==len(certs)==3','assert len(names)==len(certs)==2')]:
 f=s/n;t=f.read_text(encoding='utf-8');assert t.count(old)==1
 before=sha(f);t=t.replace(old,new);ast.parse(t);f.write_text(t,encoding='utf-8')
 rows.append(dict(path=str(f),beforeSha256=before,afterSha256=sha(f)))
with (s/'gamma-one-diamond-scope-preexecution-correction-1475.json').open('x',encoding='utf-8') as h:json.dump(dict(recordedUTC=datetime.now(timezone.utc).isoformat(),reason='The audited diamond quotient and transfer promotion has exactly two scopes, not the predecessor three. Corrected both UNUSED verification scripts before preflight or integration.',scopeCount=2,productionMutation=False,scripts=rows),h,indent=2);h.write('\n')
print(json.dumps(rows))
