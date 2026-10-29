from pathlib import Path
import json
s=Path(r'E:\Lean\.tmp\dubon83')
versions={
'SourceGammaOneKummerDegree':'1335a',
'SourceGammaOneKummerGenus':'1336a',
'SourceJointSeparableFiniteOverlap':'1338a',
'SourceJointSeparableConstants':'1340b',
'SourceJointSeparableChartDimension':'1341a',
'SourceJointSeparablePoleDimension':'1342b',
'SourceJointSeparableGenus':'1343a',
'SourceGammaOneKummerResidueGenus':'1344e',
'SourceGammaOneKummerPowerLifting':'1347b',
'SourceGammaOnePicardPrimeKernel':'1345b',
'SourceGammaOnePicardTorsion':'1346a'}
for n,v in versions.items():
 p=s/(n+v+'.lean')
 assert p.with_suffix('.exit').read_text().strip()=='0'
 assert p.with_suffix('.log').stat().st_size==0
 t=p.read_text(encoding='utf-8')
 for m,w in versions.items():t=t.replace('import '+m+w+'\n','import '+m+'\n')
 target=s/(n+'.lean');assert not target.exists();target.write_text(t,encoding='utf-8')
p=s/'gamma-one-kummer-versions-1348.json';assert not p.exists();p.write_text(json.dumps(versions,indent=2)+'\n',encoding='utf-8')
t=(s/'build_gamma_one_specialization_1333.ps1').read_text(encoding='utf-8-sig')
a=t.index('$names=@(');b=t.index('\nforeach',a)
t=t[:a]+"$names=@("+','.join("'"+n+"'" for n in versions)+")"+t[b:]
t=t.replace("$ev=$base+'-1333'","$ev=$base+'-1348'")
p=s/'build_gamma_one_kummer_1348.ps1';assert not p.exists();p.write_text(t,encoding='utf-8-sig')
# The superseded joint-chart wrappers are not required by the shorter generic route.
p=s/'SourceGammaOneJointChartSpaces1339a.lean'
assert p.with_suffix('.log').stat().st_size==0 and p.with_suffix('.exit').read_text().strip()=='0'
p.rename(p.with_suffix('.lean.txt'))
print(json.dumps(dict(modules=len(versions),runner=str(s/'build_gamma_one_kummer_1348.ps1'))))
