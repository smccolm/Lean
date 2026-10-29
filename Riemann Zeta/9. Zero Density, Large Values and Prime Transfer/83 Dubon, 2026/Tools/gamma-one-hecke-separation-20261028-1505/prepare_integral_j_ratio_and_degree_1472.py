from pathlib import Path
s=Path(__file__).parent
a=s/'SourceGammaOneIntegralJRatio1470a.lean'
t=a.read_text(encoding='utf-8')
t=t.replace('  have ht (p : PowerSeries ℤ) : t p = intSeriesC K p := rfl\n','')
t=t.replace('    exact HahnSeries.single_ne_zero.mpr one_ne_zero','    intro h\n    have hc := congrArg (fun y : LaurentSeries K => y.coeff 1) h\n    exact one_ne_zero (by simpa only [HahnSeries.coeff_single_same, HahnSeries.coeff_zero] using hc)')
a.rename(a.with_suffix('.lean.txt'))
with (s/'SourceGammaOneIntegralJRatio1470b.lean').open('x',encoding='utf-8') as h:h.write(t)
a=s/'SourceGammaOneResidueRatioDegree1469a.lean'
t=a.read_text(encoding='utf-8').replace('import Dubon2026.SourceGammaOneHeckeCoordinateDegree','import SourceGammaOneIntegralJRatio1470b')
t=t.replace('local notation "kk" => IsLocalRing.ResidueField A','local notation "kk" => IsLocalRing.ResidueField A\nprivate local instance : Algebra kk (residueImage A Γ) := (residueImage A Γ).toSubalgebra.algebra')
t=t.replace('exact jq_mem_qExpFunctionField Γ','exact jqModC_mem_integralRatioField kk Γ')
a.rename(a.with_suffix('.lean.txt'))
with (s/'SourceGammaOneResidueRatioDegree1469b.lean').open('x',encoding='utf-8') as h:h.write(t)
