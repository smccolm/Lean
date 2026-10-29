from pathlib import Path
import json
s=Path(r'E:\Lean\.tmp\dubon83')
versions={
'SourceReductionCoordinateAutomorphism':'1350b',
'SourceGammaOneDiamondGauss':'1351a',
'SourceReductionMapReflection':'1355a',
'SourceGammaOneHeckeGaussReflection':'1352f',
'SourceGammaOneHeckeFractionProduct':'1353b',
'SourceGammaOneHeckeGaussNorm':'1354c'}
for n,v in versions.items():
 p=s/(n+v+'.lean')
 assert p.with_suffix('.exit').read_text().strip()=='0'
 assert p.with_suffix('.log').stat().st_size==0
 t=p.read_text(encoding='utf-8')
 for m,w in versions.items():t=t.replace('import '+m+w+'\n','import '+m+'\n')
 target=s/(n+'.lean');assert not target.exists();target.write_text(t,encoding='utf-8')
p=s/'gamma-one-gauss-norm-versions-1356.json';assert not p.exists();p.write_text(json.dumps(versions,indent=2)+'\n',encoding='utf-8')
t=(s/'build_gamma_one_specialization_1333.ps1').read_text(encoding='utf-8-sig')
a=t.index('$names=@(');b=t.index('\nforeach',a)
t=t[:a]+"$names=@("+','.join("'"+n+"'" for n in versions)+")"+t[b:]
t=t.replace("$ev=$base+'-1333'","$ev=$base+'-1356'")
p=s/'build_gamma_one_gauss_norm_1356.ps1';assert not p.exists();p.write_text(t,encoding='utf-8-sig')
print(json.dumps(dict(modules=len(versions),runner=str(p))))
