from pathlib import Path
import json
s=Path(__file__).parent
versions={'SourceIntegralEisensteinRows':'1473a','SourceIntegralEisensteinHolomorphic':'1474c',
'SourceIntegralEisensteinModular':'1478b','SourceGammaOneEisensteinSum':'1479c',
'SourceGammaOneEisensteinLattice':'1484d','SourceGammaOneEisensteinPositive':'1488b',
'SourceGammaOneEisensteinCoefficients':'1491b','SourceGammaOneIntegralEisenstein':'1493b',
'SourceGammaOneEisensteinSeparation':'1497b'}
src=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
pending=[]
for m,v in versions.items():
 f=s/(m+v+'.lean')
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert not (src/(m+'.lean')).exists(),m
 c=f.read_text(encoding='utf-8')
 for nm,ver in versions.items():c=c.replace('import '+nm+ver+'\n','import '+nm+'\n')
 t=s/(m+'.lean');assert not t.exists(),t;pending.append((t,c))
t=s/'gamma-one-integral-eisenstein-versions-1500.json';assert not t.exists();pending.append((t,json.dumps(versions,indent=2)+'\n'))
runner=(s/'build_gamma_one_integral_ratio_canonical_1480.ps1').read_text(encoding='utf-8-sig')
a=runner.index('$names=@(');b=runner.index('\nforeach',a)
runner=runner[:a]+"$names=@("+','.join(repr(n) for n in versions)+')'+runner[b:]
runner=runner.replace("$ev=$base+'-1480'","$ev=$base+'-1500'")
t=s/'build_gamma_one_integral_eisenstein_canonical_1500.ps1';assert not t.exists();pending.append((t,runner))
for t,c in pending:t.write_text(c,encoding='utf-8')
print(json.dumps(dict(modules=len(versions),status='Canonical scratch integral Eisenstein modules prepared; mathematical bodies and comments frozen.')))
