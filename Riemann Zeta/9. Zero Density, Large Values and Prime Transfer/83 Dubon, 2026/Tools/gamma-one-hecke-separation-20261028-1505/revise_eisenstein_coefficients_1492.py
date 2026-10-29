from pathlib import Path
s=Path(r'E:\Lean\.tmp\dubon83');a=s/'SourceGammaOneEisensteinCoefficients1491a.lean';b=s/'SourceGammaOneEisensteinCoefficients1491b.lean'
assert a.exists() and not b.exists() and not a.with_suffix('.lean.txt').exists()
t=a.read_text(encoding='utf-8').replace("  have hs' := sigmaAntidiagonalEquivProd.summable_iff.mpr hs", "  have hs' := sigmaAntidiagonalEquivProd.summable_iff.mpr hs\n  simp only [Function.comp_def] at hs'")
b.write_text(t,encoding='utf-8');a.rename(a.with_suffix('.lean.txt'))
