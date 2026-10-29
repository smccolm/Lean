from pathlib import Path
s=Path(__file__).parent
a=s/'SourceGammaOneIntegralRatioResidue1466a.lean'
t=a.read_text(encoding='utf-8')
t=t.replace('exact (coeffMap_injective A.subtype A.subtype_injective) (by simpa using h)', 'apply HahnSeries.ext\n    intro i\n    apply Subtype.val_injective\n    have hc := congrArg (fun t : LaurentSeries L => t.coeff i) h\n    simpa only [coeffMap_coeff, HahnSeries.coeff_zero] using hc')
a.rename(a.with_suffix('.lean.txt'))
with (s/'SourceGammaOneIntegralRatioResidue1466b.lean').open('x',encoding='utf-8') as h:h.write(t)
