from pathlib import Path
import json
s=Path(__file__).parent
versions={'SourceGammaOneTateTransfer':'1443a','SourceGammaOneDiamondQuotientTransfer':'1444b','SourceGammaOneDiamondQuotientNonzero':'1445b','SourceGammaOneDiamondQuotientAssembly':'1448b'}
prior=json.loads((s/'gamma-one-diamond-versions-1441.json').read_text(encoding='utf-8'))
pending=[]
for m,v in versions.items():
 f=s/(m+v+'.lean')
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 c=f.read_text(encoding='utf-8')
 for nm,ver in (prior|versions).items():c=c.replace('import '+nm+ver+'\n','import '+nm+'\n')
 t=s/(m+'.lean');assert not t.exists(),t;pending.append((t,c))
t=s/'gamma-one-transfer-versions-1446.json';assert not t.exists();pending.append((t,json.dumps(versions,indent=2)+'\n'))
runner=(s/'build_gamma_one_arithmetic_orbit_canonical_1429.ps1').read_text(encoding='utf-8-sig')
a=runner.index('$names=@(');b=runner.index('\nforeach',a)
runner=runner[:a]+"$names=@("+','.join(repr(n) for n in versions)+')'+runner[b:]
runner=runner.replace("$ev=$base+'-1429'","$ev=$base+'-1446'")
t=s/'build_gamma_one_transfer_canonical_1446.ps1';assert not t.exists();pending.append((t,runner))
for t,c in pending:t.write_text(c,encoding='utf-8')
print(json.dumps(dict(modules=len(versions),status='Prepared actual transfer/nonzero consumers; bodies/comments retained.')))
