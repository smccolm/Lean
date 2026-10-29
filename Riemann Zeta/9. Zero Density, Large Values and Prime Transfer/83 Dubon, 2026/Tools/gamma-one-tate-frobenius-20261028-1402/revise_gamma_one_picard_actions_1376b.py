from pathlib import Path
p=Path(__file__).parent
f=p/'SourceGammaOneReductionPicardEquivariance1376a.lean';s=f.read_text(encoding='utf-8')
s=s.replace('  | zero => simp only [map_zero]','  | zero => erw [map_zero, map_zero, map_zero, map_zero]')
s=s.replace('    simp only [map_add, ih]','    erw [map_add, map_add, map_add, map_add, ih]')
t=p/'SourceGammaOneReductionPicardEquivariance1376b.lean';assert not t.exists();t.write_text(s,encoding='utf-8')
assert not f.with_suffix('.lean.txt').exists();f.rename(f.with_suffix('.lean.txt'))
s=(p/'build_gamma_one_picard_actions_1376.ps1').read_text(encoding='utf-8').replace('SourceGammaOneReductionPicardEquivariance1376a','SourceGammaOneReductionPicardEquivariance1376b')
t=p/'build_gamma_one_picard_actions_1376b.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
