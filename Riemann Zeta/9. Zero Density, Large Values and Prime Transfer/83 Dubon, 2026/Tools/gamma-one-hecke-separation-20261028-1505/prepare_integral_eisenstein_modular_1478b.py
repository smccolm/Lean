from pathlib import Path
s=Path(__file__).parent
a=s/'SourceIntegralEisensteinModular1478a.lean'
t=a.read_text(encoding='utf-8').replace('import SourceIntegralEisensteinHolomorphic1474c','import SourceIntegralEisensteinHolomorphic1474c\nimport Mathlib.NumberTheory.ModularForms.Basic')
a.rename(a.with_suffix('.lean.txt'))
with (s/'SourceIntegralEisensteinModular1478b.lean').open('x',encoding='utf-8') as h:h.write(t)
