from pathlib import Path
s=Path(r'E:\Lean\.tmp\dubon83');a=s/'SourceGammaOneEisensteinLattice1484c.lean';b=s/'SourceGammaOneEisensteinLattice1484d.lean'
assert a.exists() and not b.exists() and not a.with_suffix('.lean.txt').exists()
t=a.read_text(encoding='utf-8').replace('    apply Sigma.ext rfl\n    apply heq_of_eq\n    apply Subtype.ext\n    funext i\n    fin_cases i <;> rfl', '    have hv\' : ![v 0, v 1] = v := by\n      funext i\n      fin_cases i <;> rfl\n    dsimp only\n    simp only [hv\']')
b.write_text(t,encoding='utf-8');a.rename(a.with_suffix('.lean.txt'))
f=s/'SourceGammaOneEisensteinPositive1488a.lean'
# Never compiled: only its import changes before the first run.
assert not f.with_suffix('.log').exists()
f.write_text(f.read_text(encoding='utf-8').replace('import SourceGammaOneEisensteinLattice1484c','import SourceGammaOneEisensteinLattice1484d'),encoding='utf-8')
