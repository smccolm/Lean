from pathlib import Path
s=Path(r'E:\Lean\.tmp\dubon83');a=s/'SourceGammaOneIntegralEisenstein1493a.lean';b=s/'SourceGammaOneIntegralEisenstein1493b.lean'
assert a.exists() and not b.exists() and not a.with_suffix('.lean.txt').exists()
t=a.read_text(encoding='utf-8').replace('EisensteinSeries.norm_exp_two_pi_I_lt_one','UpperHalfPlane.norm_exp_two_pi_I_lt_one')
t=t.replace('  apply ModularFormClass.qExpansion_coeff_unique (f := normalizedForm N c)\n    zero_lt_one (gammaOne_one_mem_strictPeriods N)', '  refine ModularFormClass.qExpansion_coeff_unique (f := normalizedForm N c)\n    (c := fun m => (coefficient N c m : ℂ))\n    zero_lt_one (SourceFricke.gammaOne_one_mem_strictPeriods N) ?_ n')
b.write_text(t,encoding='utf-8');a.rename(a.with_suffix('.lean.txt'))
