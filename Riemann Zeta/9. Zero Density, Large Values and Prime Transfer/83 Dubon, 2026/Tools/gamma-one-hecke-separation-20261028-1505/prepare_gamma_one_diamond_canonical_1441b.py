from pathlib import Path
import json
s=Path(__file__).parent
versions={'SourceTateDualArithmeticDiamond':'1433a','SourceGammaOneArithmeticDiamondPolynomial':'1434b','SourceGammaOneGeometricDiamond':'1435b','SourceGammaOneGaloisDiamondPolynomial':'1436c','SourceGammaOneTateDiamondRelations':'1437e','SourceGammaOneDiamondQuotientGalois':'1438h','SourceGammaOneDiamondQuotientPolynomial':'1439j','SourceGammaOneDiamondQuotientHecke':'1440k'}
aliases={'SourceGammaOneArithmeticDiamondPolynomial':'SourceGammaOneArithmeticDiamond'}
pending=[]
for m,v in versions.items():
 f=s/(aliases.get(m,m)+v+'.lean')
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 c=f.read_text(encoding='utf-8')
 for nm,ver in versions.items():c=c.replace('import '+aliases.get(nm,nm)+ver+'\n','import '+nm+'\n')
 t=s/(m+'.lean');assert not t.exists(),t;pending.append((t,c))
t=s/'gamma-one-diamond-version-aliases-1441.json';assert not t.exists();pending.append((t,json.dumps(aliases,indent=2)+'\n'))
t=s/'gamma-one-diamond-versions-1441.json';assert not t.exists();pending.append((t,json.dumps(versions,indent=2)+'\n'))
runner=(s/'build_gamma_one_arithmetic_orbit_canonical_1429.ps1').read_text(encoding='utf-8-sig')
a=runner.index('$names=@(');b=runner.index('\nforeach',a)
runner=runner[:a]+"$names=@("+','.join(repr(n) for n in versions)+')'+runner[b:]
runner=runner.replace("$ev=$base+'-1429'","$ev=$base+'-1441'")
t=s/'build_gamma_one_diamond_canonical_1441.ps1';assert not t.exists();pending.append((t,runner))
for t,c in pending:t.write_text(c,encoding='utf-8')
print(json.dumps(dict(modules=len(versions),status='Prepared scratch canonical imports; all mathematical bodies/comments retained.')))
