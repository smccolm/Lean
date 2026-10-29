from pathlib import Path
import re,json,hashlib
from datetime import datetime,timezone
s=Path(__file__).parent
pairs=[('SourceSiegelLeadingUnit1589a','SourceSiegelLeadingUnit1589b'),('SourceSiegelNormalizedProduct1590b','SourceSiegelNormalizedProduct1590c'),('SourceSiegelCoefficientSeries1591b','SourceSiegelCoefficientSeries1591c'),('SourceSiegelIntegralExpansion1592b','SourceSiegelIntegralExpansion1592c')]
records=[]
for a,b in pairs:
 src=s/(a+'.lean');dst=s/(b+'.lean');assert not dst.exists()
 c=src.read_text(encoding='utf-8')
 if a.endswith('1589a'):
  c,n=re.subn(r'^theorem zeta_ne_zero[^\n]*\n\n','',c,flags=re.M);assert n==1
 for x,y in pairs:c=c.replace('import '+x+'\n','import '+y+'\n')
 dst.write_text(c,encoding='utf-8')
 records.append(dict(previous=a,new=b,oldSHA256=hashlib.sha256(src.read_bytes()).hexdigest().upper(),newSHA256=hashlib.sha256(dst.read_bytes()).hexdigest().upper()))
r=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),reason='Value-only preflight1594 found zeta_ne_zero unused by the exact source consumer. Remove the incidental helper; preserve all mathematical source conclusions and all failed/superseded evidence. No new hypothesis, audit exception or limit change.',revisions=records)
(s/'siegel-expansion-trim-review-1595.json').write_text(json.dumps(r,indent=2)+'\n',encoding='utf-8')
c="$ErrorActionPreference='Stop'\n"
for a,b in pairs:c+=f"& powershell -NoProfile -ExecutionPolicy Bypass -File 'E:\\Lean\\.tmp\\dubon83\\run_scratch_module_1433.ps1' -Name {b}\nif($LASTEXITCODE -ne 0){{exit $LASTEXITCODE}}\n"
(s/'build_siegel_expansion_revision_1595.ps1').write_text(c,encoding='utf-8')
print('Prepared four fresh versions; old evidence retained.')
