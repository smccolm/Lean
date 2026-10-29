from pathlib import Path
s=Path(r'E:\Lean\.tmp\dubon83')
a=s/'SourceGammaOneEisensteinSum1479b.lean'; b=s/'SourceGammaOneEisensteinSum1479c.lean'
assert a.exists() and not b.exists() and not a.with_suffix('.lean.txt').exists()
t=a.read_text(encoding='utf-8').replace("    simpa only [principalRowSum_coe] using (principalRowSum N c).bdd_at_cusps' hc'", "    change cusp.IsBoundedAt (rowSum N c) (4 : ℤ)\n    rw [← principalRowSum_coe]\n    exact (principalRowSum N c).bdd_at_cusps' hc'")
b.write_text(t,encoding='utf-8'); a.rename(a.with_suffix('.lean.txt'))
