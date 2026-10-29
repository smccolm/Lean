from pathlib import Path
p=Path(__file__).parent
routes=[('SourceGammaOnePicardFrobeniusRelation1379g','SourceGammaOnePicardFrobeniusRelation1379h',{'SourceGammaOneHeckeTorsionPicard1378f':'SourceGammaOneHeckeTorsionPicard1378h'}),('SourceGammaOneTateFrobeniusRelation1380d','SourceGammaOneTateFrobeniusRelation1380e',{'SourceGammaOnePicardFrobeniusRelation1379g':'SourceGammaOnePicardFrobeniusRelation1379h'})]
for old,new,changes in routes:
    f=p/(old+'.lean');s=f.read_text(encoding='utf-8')
    for a,b in changes.items():assert a in s;s=s.replace(a,b)
    t=p/(new+'.lean');assert not t.exists();t.write_text(s,encoding='utf-8')
    target=f.with_suffix('.lean.txt');assert not target.exists();f.rename(target)
s=(p/'build_gamma_one_inertia_1359.ps1').read_text(encoding='utf-8')
s=s.replace("@('SourceGammaOneArithmeticCharts1359a','SourceGammaOneSpecializationCharts1360a')",'@('+','.join(repr(x[1]) for x in routes)+')')
t=p/'build_gamma_one_frobenius_consumers_1387.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
