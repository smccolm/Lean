from pathlib import Path
s=Path(__file__).parent
old=s/'SourceSiegelResidueReduction1574a.lean';assert not old.with_suffix('.lean.txt').exists()
t=old.read_text(encoding='utf-8')
for name in ['dS_ne_zero','dR_ne_zero','siegelFun_add_nat_mul_snd','siegelFun_add_int_mul_snd','siegelFun_add_nat_mul_fst','siegelFun_add_int_mul_fst','pow_twelve_mul_eq_one']:
 t=t.replace('theorem '+name+' ', 'omit [NeZero N] in\ntheorem '+name+' ',1)
old.rename(old.with_suffix('.lean.txt'))
f=s/'SourceSiegelResidueReduction1574b.lean';assert not f.exists();f.write_text(t,encoding='utf-8')
old=s/'SourceSiegelProductTransformation1575a.lean';assert not old.with_suffix('.lean.txt').exists()
t=old.read_text(encoding='utf-8').replace('import SourceSiegelResidueReduction1574a','import SourceSiegelResidueReduction1574b')
old.rename(old.with_suffix('.lean.txt'))
f=s/'SourceSiegelProductTransformation1575b.lean';assert not f.exists();f.write_text(t,encoding='utf-8')
