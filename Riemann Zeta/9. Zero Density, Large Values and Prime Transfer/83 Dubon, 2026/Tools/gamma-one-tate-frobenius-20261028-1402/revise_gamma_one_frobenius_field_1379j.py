from pathlib import Path
p=Path(__file__).parent
routes=[('SourceGammaOnePicardFrobeniusRelation1379i','SourceGammaOnePicardFrobeniusRelation1379j'),('SourceGammaOneTateFrobeniusRelation1380f','SourceGammaOneTateFrobeniusRelation1380g')]
for old,new in routes:
    f=p/(old+'.lean');s=f.read_text(encoding='utf-8')
    s=s.replace('Module.finrank Qbar⟮jCoordinateOver Γ Qbar⟯ FF','Module.finrank Qbar⟮jCoordinateOver Γ Qbar⟯ (functionFieldOver Γ Qbar)')
    s=s.replace('  rw [map_add, map_nsmul,','  erw [map_add, map_nsmul,')
    s=s.replace('SourceGammaOnePicardFrobeniusRelation1379i','SourceGammaOnePicardFrobeniusRelation1379j')
    t=p/(new+'.lean');assert not t.exists();t.write_text(s,encoding='utf-8')
    target=f.with_suffix('.lean.txt');assert not target.exists();f.rename(target)
s=(p/'build_gamma_one_frobenius_field_1379i.ps1').read_text(encoding='utf-8').replace('1379i','1379j').replace('1380f','1380g')
t=p/'build_gamma_one_frobenius_field_1379j.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
