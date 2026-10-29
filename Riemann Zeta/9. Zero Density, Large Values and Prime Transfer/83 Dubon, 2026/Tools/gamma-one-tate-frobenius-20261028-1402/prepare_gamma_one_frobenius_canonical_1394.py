from pathlib import Path
import json
p=Path(__file__).parent
versions={'SourceGammaOneHeckePrincipalNorm':'1369b','SourceGammaOneResidueDivisors':'1370a','SourceGammaOneHeckeResidueNorm':'1371a','SourceGammaOneIntegralDivisorReduction':'1372a','SourceGammaOneHeckeIntegralAgreement':'1373a','SourceGammaOneHeckeTorsionDivisors':'1374a','SourceGammaOneResiduePicard':'1375a','SourceGammaOneReductionPicardEquivariance':'1376c','SourceGammaOneNormDiamondOrientation':'1377b','SourceGammaOneHeckePicardDescent':'1381f','SourceGammaOneHeckeTorsionPicard':'1378h','SourceTorsionReductionDiamond':'1389b','SourceGammaOnePicardFrobeniusRelation':'1379n','SourceTateTorsionQuadratic':'1390a','SourceGammaOneTateFrobeniusRelation':'1380n'}
for name,version in versions.items():
    f=p/(name+version+'.lean')
    assert f.with_suffix('.exit').read_text().strip()=='0'
    assert f.with_suffix('.log').stat().st_size==0
    s=f.read_text(encoding='utf-8')
    for m,v in versions.items():s=s.replace('import '+m+v+'\n','import '+m+'\n')
    t=p/(name+'.lean');assert not t.exists();t.write_text(s,encoding='utf-8')
t=p/'gamma-one-frobenius-versions-1394.json';assert not t.exists();t.write_text(json.dumps(versions,indent=2)+'\n',encoding='utf-8')
s=(p/'build_gamma_one_specialization_1333.ps1').read_text(encoding='utf-8-sig')
a=s.index('$names=@(');b=s.index('\nforeach',a)
s=s[:a]+"$names=@("+','.join(repr(n) for n in versions)+')'+s[b:]
s=s.replace("$ev=$base+'-1333'","$ev=$base+'-1394'")
t=p/'build_gamma_one_frobenius_canonical_1394.ps1';assert not t.exists();t.write_text(s,encoding='utf-8-sig')
print(json.dumps(dict(modules=len(versions),runner=str(t))))
