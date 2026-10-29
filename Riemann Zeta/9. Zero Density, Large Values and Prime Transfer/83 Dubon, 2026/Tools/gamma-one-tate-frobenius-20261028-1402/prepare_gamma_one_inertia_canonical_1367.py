from pathlib import Path
import json
p=Path(__file__).parent
versions={'SourceGammaOneArithmeticCharts':'1359a','SourceGammaOneSpecializationCharts':'1360a','SourceGammaOneDecompositionCharts':'1361b','SourceGammaOneConstantReductionCharts':'1362a','SourceGammaOneSpecializationEquivariance':'1363b','SourceGammaOneInertiaPlaceReduction':'1364b','SourceGammaOneInertiaPicard':'1365c','SourceGammaOneTateInertia':'1366c'}
for n,v in versions.items():
 f=p/(n+v+'.lean')
 assert f.with_suffix('.exit').read_text().strip()=='0'
 assert f.with_suffix('.log').stat().st_size==0
 s=f.read_text(encoding='utf-8')
 for m,w in versions.items():s=s.replace('import '+m+w+'\n','import '+m+'\n')
 t=p/(n+'.lean');assert not t.exists();t.write_text(s,encoding='utf-8')
f=p/'gamma-one-inertia-versions-1367.json';assert not f.exists();f.write_text(json.dumps(versions,indent=2)+'\n',encoding='utf-8')
s=(p/'build_gamma_one_specialization_1333.ps1').read_text(encoding='utf-8-sig')
a=s.index('$names=@(');b=s.index('\nforeach',a)
s=s[:a]+"$names=@("+','.join("'"+n+"'" for n in versions)+")"+s[b:]
s=s.replace("$ev=$base+'-1333'","$ev=$base+'-1367'")
f=p/'build_gamma_one_inertia_canonical_1367.ps1';assert not f.exists();f.write_text(s,encoding='utf-8-sig')
print(json.dumps(dict(modules=len(versions),runner=str(f))))
