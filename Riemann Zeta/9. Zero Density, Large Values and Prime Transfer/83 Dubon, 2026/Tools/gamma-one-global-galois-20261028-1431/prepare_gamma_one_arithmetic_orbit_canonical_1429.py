from pathlib import Path
import json
p=Path(__file__).parent
versions={'SourceGammaOneTwistedNormInertia':'1424b','SourceGammaOneTwistedArithmeticDescent':'1425c','SourceCyclotomicHomogeneousDiamond':'1426a','SourceGammaOneTwistedGaloisDiamond':'1427a','SourceGammaOneParabolicGaloisOrbit':'1428a'}
prior=json.loads((p/'gamma-one-continuity-versions-1422.json').read_text(encoding='utf-8'))
for name,version in versions.items():
    f=p/(name+version+'.lean')
    assert f.with_suffix('.exit').read_text().strip()=='0'
    assert f.with_suffix('.log').stat().st_size==0
    code=f.read_text(encoding='utf-8')
    for m,v in (prior|versions).items():code=code.replace('import '+m+v+'\n','import '+m+'\n')
    t=p/(name+'.lean');assert not t.exists();t.write_text(code,encoding='utf-8')
t=p/'gamma-one-arithmetic-orbit-versions-1429.json';assert not t.exists();t.write_text(json.dumps(versions,indent=2)+'\n',encoding='utf-8')
s=(p/'build_gamma_one_continuity_canonical_1422.ps1').read_text(encoding='utf-8-sig')
a=s.index('$names=@(');b=s.index('\nforeach',a)
s=s[:a]+"$names=@("+','.join(repr(n) for n in versions)+')'+s[b:]
s=s.replace("$ev=$base+'-1422'","$ev=$base+'-1429'")
t=p/'build_gamma_one_arithmetic_orbit_canonical_1429.ps1';assert not t.exists();t.write_text(s,encoding='utf-8-sig')
print(json.dumps(dict(modules=len(versions),runner=str(t))))
