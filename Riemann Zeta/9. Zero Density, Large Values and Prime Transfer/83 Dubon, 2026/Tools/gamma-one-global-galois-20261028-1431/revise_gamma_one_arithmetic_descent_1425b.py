from pathlib import Path
p=Path(__file__).parent
f=p/'SourceGammaOneTwistedArithmeticDescent1425a.lean';assert f.with_suffix('.exit').read_text().strip()=='1'
s=f.read_text(encoding='utf-8')
s=s.replace('''    letI : TopologicalSpace (Module.End (ZMod N) (T →ₗ[ℤ_[p]] V)) := ⊥
    ∃ η : rationalArithmeticGaloisGroup ((Q * p : ℕ) : 𝓞 ℚ) →ₜ*
        (Module.End (ZMod N) (T →ₗ[ℤ_[p]] V))ˣ,
      ∀ σ, (η (sourceAbsoluteArithmeticRestriction ((Q * p : ℕ) : 𝓞 ℚ) σ) :
        Module.End (ZMod N) (T →ₗ[ℤ_[p]] V)) = binaryArithmeticTateGaloisRep Q p n w σ := by''','''    let B := Module.End (ZMod N) (T →ₗ[ℤ_[p]] V)
    letI : TopologicalSpace B := ⊥
    ∃ η : rationalArithmeticGaloisGroup ((Q * p : ℕ) : 𝓞 ℚ) →ₜ* Bˣ,
      ∀ σ, (η (sourceAbsoluteArithmeticRestriction ((Q * p : ℕ) : 𝓞 ℚ) σ) : B) =
        binaryArithmeticTateGaloisRep Q p n w σ := by''')
t=p/'SourceGammaOneTwistedArithmeticDescent1425b.lean';assert not t.exists();t.write_text(s,encoding='utf-8')
inert=f.with_suffix('.lean.txt');assert not inert.exists();f.rename(inert)
s=(p/'build_gamma_one_arithmetic_descent_1425.ps1').read_text(encoding='utf-8').replace('1425a','1425b')
t=p/'build_gamma_one_arithmetic_descent_1425b.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
