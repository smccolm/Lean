from pathlib import Path
p=Path(__file__).parent
routes=[('SourceTorsionReductionDiamond1389a','SourceTorsionReductionDiamond1389b'),('SourceGammaOnePicardFrobeniusRelation1379m','SourceGammaOnePicardFrobeniusRelation1379n'),('SourceGammaOneTateFrobeniusRelation1380i','SourceGammaOneTateFrobeniusRelation1380j')]
for old,new in routes:
    f=p/(old+'.lean');s=f.read_text(encoding='utf-8')
    s=s.replace('  rw [hhecke, hcomm, he, hinv, map_add, map_nsmul, he]','  simp only [hhecke, hcomm, he, hinv, map_add, map_nsmul]')
    for a,b in routes:s=s.replace('import '+a+'\n','import '+b+'\n')
    t=p/(new+'.lean');assert not t.exists();t.write_text(s,encoding='utf-8')
    t=f.with_suffix('.lean.txt');assert not t.exists();f.rename(t)
s=(p/'build_gamma_one_picard_relation_1379m.ps1').read_text(encoding='utf-8')
for a,b in routes:s=s.replace(a,b)
t=p/'build_gamma_one_picard_relation_1389b.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
