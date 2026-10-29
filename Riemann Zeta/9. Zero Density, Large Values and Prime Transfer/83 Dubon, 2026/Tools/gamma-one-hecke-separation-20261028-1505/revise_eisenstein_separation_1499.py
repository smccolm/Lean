from pathlib import Path
s=Path(r'E:\Lean\.tmp\dubon83');a=s/'SourceGammaOneEisensteinSeparation1497a.lean';b=s/'SourceGammaOneEisensteinSeparation1497b.lean'
assert a.exists() and not b.exists() and not a.with_suffix('.lean.txt').exists()
t=a.read_text(encoding='utf-8').replace('  have hz : (1 : K) = 0 := by\n    simpa [intSeriesC, PowerSeries.coeff_coe, eisenstein4] using h0\n  exact one_ne_zero hz','  simp [intSeriesC, PowerSeries.coeff_coe, eisenstein4] at h0')
t=t.replace("  exact hc' (by linear_combination -h)","  exact hc' (by linear_combination h)")
t=t.replace('  have hz : (0 : K) = 1 := by\n    simpa [intSeriesC, PowerSeries.coeff_coe, integralSeries,\n      coefficient_other_class N c hc hc\', coefficient_identity_class N hN] using h1\n  exact zero_ne_one hz','  simp [intSeriesC, PowerSeries.coeff_coe, integralSeries,\n    coefficient_other_class N c hc hc\', coefficient_identity_class N hN] at h1')
b.write_text(t,encoding='utf-8');a.rename(a.with_suffix('.lean.txt'))
