from pathlib import Path
p=Path(__file__).parent
f=p/'SourceGammaOneReductionPicardEquivariance1376b.lean';s=f.read_text(encoding='utf-8')
s=s.replace('  | zero => erw [map_zero, map_zero, map_zero, map_zero]','  | zero => erw [map_zero]')
t=p/'SourceGammaOneReductionPicardEquivariance1376c.lean';assert not t.exists();t.write_text(s,encoding='utf-8')
assert not f.with_suffix('.lean.txt').exists();f.rename(f.with_suffix('.lean.txt'))
s=(p/'build_gamma_one_picard_actions_1376b.ps1').read_text(encoding='utf-8').replace('SourceGammaOneReductionPicardEquivariance1376b','SourceGammaOneReductionPicardEquivariance1376c')
t=p/'build_gamma_one_picard_actions_1376c.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
f=p/'SourceGammaOnePicardFrobeniusRelation1379a.lean'
s=f.read_text(encoding='utf-8').replace('SourceGammaOneReductionPicardEquivariance1376b','SourceGammaOneReductionPicardEquivariance1376c')
t=p/'SourceGammaOnePicardFrobeniusRelation1379b.lean';assert not t.exists();t.write_text(s,encoding='utf-8')
assert not f.with_suffix('.lean.txt').exists();f.rename(f.with_suffix('.lean.txt'))
s=(p/'build_gamma_one_picard_frobenius_1378.ps1').read_text(encoding='utf-8').replace('SourceGammaOnePicardFrobeniusRelation1379a','SourceGammaOnePicardFrobeniusRelation1379b')
t=p/'build_gamma_one_picard_frobenius_1378b.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
