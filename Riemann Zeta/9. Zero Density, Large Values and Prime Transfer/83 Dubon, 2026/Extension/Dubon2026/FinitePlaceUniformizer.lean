import Dubon2026.RationalPrimePlace
import Mathlib.NumberTheory.Padics.PadicIntegers

/-! # Exact unit-times-prime-power factorization in the original local integer ring -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain

local instance (v : HeightOneSpectrum ℤ) : Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩

/-- Every original nonzero local integer is a genuine unit times a nonnegative power of its actual rational prime. -/
theorem finitePlaceInteger_unit_prime_power (v : HeightOneSpectrum ℤ)
    (x : v.adicCompletionIntegers ℚ) (hx : x ≠ 0) :
    ∃ u : (v.adicCompletionIntegers ℚ)ˣ, ∃ n : ℕ,
      x = (u : v.adicCompletionIntegers ℚ) * (Rat.HeightOneSpectrum.natGenerator v : v.adicCompletionIntegers ℚ) ^ n := by
  letI : Algebra ℤ (v.adicCompletionIntegers ℚ) := Ring.toIntAlgebra _
  let e := Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v
  have hy : e x ≠ 0 := by
    intro h
    exact hx (e.injective (h.trans (map_zero e).symm))
  refine ⟨Units.map e.symm.toRingEquiv.toMonoidHom (PadicInt.unitCoeff hy), (e x).valuation, ?_⟩
  have he := congrArg e.symm (PadicInt.unitCoeff_spec hy)
  change x = e.symm (PadicInt.unitCoeff hy).val *
    (Rat.HeightOneSpectrum.natGenerator v : v.adicCompletionIntegers ℚ) ^ (e x).valuation
  simpa only [map_mul, map_pow, map_natCast, e.symm_apply_apply] using he

/-- At the genuine place of an ordinary prime, the local factorization uses exactly that original prime. -/
theorem rationalPrimePlaceInteger_unit_power (p : ℕ) (hp : p.Prime)
    (x : (rationalPrimePlace p hp).adicCompletionIntegers ℚ) (hx : x ≠ 0) :
    ∃ u : ((rationalPrimePlace p hp).adicCompletionIntegers ℚ)ˣ, ∃ n : ℕ,
      x = (u : (rationalPrimePlace p hp).adicCompletionIntegers ℚ) *
        (p : (rationalPrimePlace p hp).adicCompletionIntegers ℚ) ^ n := by
  have he := finitePlaceInteger_unit_prime_power (rationalPrimePlace p hp) x hx
  rw [rationalPrimePlace_natGenerator] at he
  exact he

end
end Dubon2026
