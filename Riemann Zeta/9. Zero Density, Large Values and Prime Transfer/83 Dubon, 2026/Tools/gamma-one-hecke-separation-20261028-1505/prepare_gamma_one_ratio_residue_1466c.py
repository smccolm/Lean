from pathlib import Path
s=Path(__file__).parent
a=s/'SourceGammaOneIntegralRatioResidue1466b.lean'
t=a.read_text(encoding='utf-8')
start=t.index('  have hv0 :');end=t.index('  have hgL :',start)
t=t[:start]+'''  have hiv0 : ι A v ≠ 0 := by
    rw [ι_eq_zero_iff]
    exact ϖ_ne_zero_ne_zero hv
'''+t[end:]
a.rename(a.with_suffix('.lean.txt'))
with (s/'SourceGammaOneIntegralRatioResidue1466c.lean').open('x',encoding='utf-8') as h:h.write(t)
