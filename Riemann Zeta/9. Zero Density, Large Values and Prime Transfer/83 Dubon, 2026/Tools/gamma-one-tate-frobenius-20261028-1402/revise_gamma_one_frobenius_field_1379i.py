from pathlib import Path
p=Path(__file__).parent
routes=[('SourceGammaOnePicardFrobeniusRelation1379h','SourceGammaOnePicardFrobeniusRelation1379i'),('SourceGammaOneTateFrobeniusRelation1380e','SourceGammaOneTateFrobeniusRelation1380f')]
for old,new in routes:
    f=p/(old+'.lean');s=f.read_text(encoding='utf-8')
    s=s.replace('local notation "FF" => functionFieldOver Γ Qbar','local notation "FF" => laurentBaseChange Qbar (x1FunctionField M)')
    s=s.replace('SourceGammaOnePicardFrobeniusRelation1379h','SourceGammaOnePicardFrobeniusRelation1379i')
    t=p/(new+'.lean');assert not t.exists();t.write_text(s,encoding='utf-8')
    target=f.with_suffix('.lean.txt');assert not target.exists();f.rename(target)
s=(p/'build_gamma_one_frobenius_consumers_1387.ps1').read_text(encoding='utf-8').replace('1379h','1379i').replace('1380e','1380f')
t=p/'build_gamma_one_frobenius_field_1379i.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
