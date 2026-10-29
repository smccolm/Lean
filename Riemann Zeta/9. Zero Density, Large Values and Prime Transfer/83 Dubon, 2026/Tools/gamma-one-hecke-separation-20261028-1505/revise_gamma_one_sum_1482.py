from pathlib import Path
s = Path(r'E:\Lean\.tmp\dubon83')
a = s / 'SourceGammaOneEisensteinSum1479a.lean'
b = s / 'SourceGammaOneEisensteinSum1479b.lean'
assert a.exists() and not b.exists() and not a.with_suffix('.lean.txt').exists()
t = a.read_text(encoding='utf-8')
t = t.replace("  holo' := by\n    rw", "  holo' := by\n    change MDiff (rowSum N c)\n    rw")
t = t.replace("    rw [← principalRowSum_coe]\n    exact (principalRowSum N c).bdd_at_cusps' hc'", "    simpa only [principalRowSum_coe] using (principalRowSum N c).bdd_at_cusps' hc'")
b.write_text(t, encoding='utf-8')
a.rename(a.with_suffix('.lean.txt'))
