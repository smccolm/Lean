from pathlib import Path
import json
p=Path(__file__).parent
versions={'SourceTwistedCoefficientDualAction':'1398a','SourceCyclotomicHomogeneousAction':'1399b','SourceAbsoluteCyclotomicCharacter':'1400b','SourceGammaOneTwistedGalois':'1401e','SourceCyclotomicHomogeneousHecke':'1403b','SourceGammaOneTwistedGaloisHecke':'1404b','SourceAbsoluteCyclotomicLocal':'1405a','SourceGammaOneTwistedGaloisFrobenius':'1406d','SourceTwistedCoefficientDualTrivial':'1407a','SourceGammaOneTwistedGaloisInertia':'1408a','SourceGammaOneParabolicTateLift':'1409a','SourceGammaOneParabolicGaloisFrobenius':'1410b'}
prior={}
for name in ['gamma-one-inertia-versions-1367.json','gamma-one-frobenius-versions-1394.json','gamma-one-arithmetic-versions-1396.json']:
    prior.update(json.loads((p/name).read_text(encoding='utf-8')))
for name,version in versions.items():
    f=p/(name+version+'.lean')
    assert f.with_suffix('.exit').read_text().strip()=='0'
    assert f.with_suffix('.log').stat().st_size==0
    code=f.read_text(encoding='utf-8')
    for m,v in (prior|versions).items():code=code.replace('import '+m+v+'\n','import '+m+'\n')
    t=p/(name+'.lean');assert not t.exists();t.write_text(code,encoding='utf-8')
t=p/'gamma-one-twisted-versions-1411.json';assert not t.exists();t.write_text(json.dumps(versions,indent=2)+'\n',encoding='utf-8')
s=(p/'build_gamma_one_specialization_1333.ps1').read_text(encoding='utf-8-sig')
a=s.index('$names=@(');b=s.index('\nforeach',a)
s=s[:a]+"$names=@("+','.join(repr(n) for n in versions)+')'+s[b:]
s=s.replace("$ev=$base+'-1333'","$ev=$base+'-1411'")
t=p/'build_gamma_one_twisted_canonical_1411.ps1';assert not t.exists();t.write_text(s,encoding='utf-8-sig')
print(json.dumps(dict(modules=len(versions),runner=str(t))))
