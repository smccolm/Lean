from pathlib import Path
s=Path(r'E:\Lean\.tmp\dubon83');a=s/'SourceGammaOneEisensteinLattice1484b.lean';b=s/'SourceGammaOneEisensteinLattice1484c.lean'
assert a.exists() and not b.exists() and not a.with_suffix('.lean.txt').exists()
t=a.read_text(encoding='utf-8').replace('    apply Sigma.ext hb\n    apply Subtype.heq_iff_coe_heq.mpr\n    apply heq_of_eq', '    subst b\n    apply Sigma.ext rfl\n    apply heq_of_eq\n    apply Subtype.ext')
b.write_text(t,encoding='utf-8');a.rename(a.with_suffix('.lean.txt'))
