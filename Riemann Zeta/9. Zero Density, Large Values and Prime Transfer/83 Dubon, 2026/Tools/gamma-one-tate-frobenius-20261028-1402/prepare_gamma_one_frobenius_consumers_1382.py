from pathlib import Path
p=Path(__file__).parent
routes=[('SourceGammaOneHeckeTorsionPicard1378e','SourceGammaOneHeckeTorsionPicard1378f',{'SourceGammaOneHeckePicardDescent1381b':'SourceGammaOneHeckePicardDescent1381f'}),('SourceGammaOnePicardFrobeniusRelation1379f','SourceGammaOnePicardFrobeniusRelation1379g',{'SourceGammaOneHeckeTorsionPicard1378e':'SourceGammaOneHeckeTorsionPicard1378f'}),('SourceGammaOneTateFrobeniusRelation1380c','SourceGammaOneTateFrobeniusRelation1380d',{'SourceGammaOnePicardFrobeniusRelation1379f':'SourceGammaOnePicardFrobeniusRelation1379g'})]
for old,new,changes in routes:
    f=p/(old+'.lean');s=f.read_text(encoding='utf-8')
    for a,b in changes.items():assert a in s;s=s.replace(a,b)
    t=p/(new+'.lean');assert not t.exists();t.write_text(s,encoding='utf-8')
    target=f.with_suffix('.lean.txt');assert not target.exists();f.rename(target)
s=(p/'build_gamma_one_inertia_1359.ps1').read_text(encoding='utf-8')
s=s.replace("@('SourceGammaOneArithmeticCharts1359a','SourceGammaOneSpecializationCharts1360a')",'@('+','.join(repr(x[1]) for x in routes)+')')
t=p/'build_gamma_one_frobenius_consumers_1382.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
