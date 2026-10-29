from pathlib import Path
s=Path(__file__).parent
a=s/'SourceIntegralLevelOneTraceCoefficients1509a.lean'
b=s/'SourceIntegralLevelOneTraceCoefficients1509b.lean'
assert not b.exists()
t=a.read_text(encoding='utf-8').replace('    dsimp [H]\n', '    change qExpansion 1 (⇑((F.mul E).mcast hw) : ℍ → ℂ) = _\n')
t=t.replace('    exact hF p.1 ((Finset.HasAntidiagonal.antidiagonal.fst_le hp).trans hm)', '    have hp\' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp\n    exact hF p.1 (by omega)')
b.write_text(t,encoding='utf-8')
a.rename(a.with_suffix('.lean.txt'))
