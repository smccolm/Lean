from pathlib import Path
s=Path(__file__).parent
a=s/'SourceSiegelProductCoefficients1597a.lean';b=s/'SourceSiegelProductCoefficients1597b.lean';assert not b.exists()
c=a.read_text(encoding='utf-8').replace('  rw [series, PowerSeries.coeff_mk, EulerExpansion.coef_zero, ZMod.val_eq_zero]','  simp only [series, PowerSeries.coeff_mk, EulerExpansion.coef_zero, ZMod.val_eq_zero]')
b.write_text(c,encoding='utf-8');a.rename(a.with_suffix('.lean.txt'))
