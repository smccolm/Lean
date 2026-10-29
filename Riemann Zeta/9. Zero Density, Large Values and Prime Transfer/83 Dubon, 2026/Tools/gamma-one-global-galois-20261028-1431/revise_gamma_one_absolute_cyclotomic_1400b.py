from pathlib import Path
p=Path(__file__).parent
f=p/'SourceAbsoluteCyclotomicCharacter1400a.lean';s=f.read_text(encoding='utf-8')
s=s.replace('''    (Qbar ≃ₐ[ℚ] Qbar) →ₜ* (ZMod N)ˣ := by
''','''    (Qbar ≃ₐ[ℚ] Qbar) →ₜ* (ZMod N)ˣ := by
  haveI : Algebra.IsAlgebraic ℚ Qbar := AlgebraicClosure.isAlgebraic ℚ
''')
t=p/'SourceAbsoluteCyclotomicCharacter1400b.lean';assert not t.exists();t.write_text(s,encoding='utf-8')
t=f.with_suffix('.lean.txt');assert not t.exists();f.rename(t)
f=p/'SourceGammaOneTwistedGalois1401b.lean';s=f.read_text(encoding='utf-8').replace('1400a','1400b')
t=p/'SourceGammaOneTwistedGalois1401c.lean';assert not t.exists();t.write_text(s,encoding='utf-8')
t=f.with_suffix('.lean.txt');assert not t.exists();f.rename(t)
s=(p/'build_gamma_one_inertia_1359.ps1').read_text(encoding='utf-8')
s=s.replace("@('SourceGammaOneArithmeticCharts1359a','SourceGammaOneSpecializationCharts1360a')","@('SourceAbsoluteCyclotomicCharacter1400b','SourceGammaOneTwistedGalois1401c')")
t=p/'build_gamma_one_twisted_galois_1401c.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
