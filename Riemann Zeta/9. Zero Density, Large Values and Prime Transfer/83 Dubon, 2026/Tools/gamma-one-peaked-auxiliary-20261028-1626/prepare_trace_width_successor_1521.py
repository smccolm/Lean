from pathlib import Path
s=Path(__file__).parent;a=s/'SourceIntegralTracePeriodWidth1519a.lean';b=s/'SourceIntegralTracePeriodWidth1519b.lean'
assert not b.exists()
t=a.read_text(encoding='utf-8').replace('hperN : Function.Periodic (f ∘ ofComplex) ((N : ℝ) * h)', 'hperN : Function.Periodic (f ∘ ofComplex) (((N : ℝ) * h : ℝ) : ℂ)')
assert t != a.read_text(encoding='utf-8')
b.write_text(t,encoding='utf-8');a.rename(a.with_suffix('.lean.txt'))
