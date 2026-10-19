import Dubon2026.RationalPrimeUnramifiedDimension

/-! The original rational prime has norm less than one in the same
completion and closure used by the arithmetic restriction. This removes
the norm assumption in the contracted-prime/inertia comparison required
for DUB-17's actual auxiliary local deformation conditions. -/

namespace Dubon2026
noncomputable section
open scoped WithZero

attribute [local instance] rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric
attribute [local instance 1100] rationalPrimeOriginalNormedField

/-- The original adic prime lies in the maximal ideal for the compatible norm. -/
theorem rationalPrimeOriginalNorm_prime_lt_one (p : ℕ) (hp : p.Prime) :
    ‖(p : rationalPrimeLocalField p hp)‖ < 1 := by
  letI : (NormedField.valuation (K := rationalPrimeLocalField p hp)).Compatible :=
    localFieldOriginalNorm_compatible (rationalPrimeLocalField p hp)
  have hm : (p : ℤ) ∈ (rationalPrimePlace p hp).asIdeal :=
    (rationalPrimePlace_nat_mem_iff p hp p).mpr dvd_rfl
  have hb := ((rationalPrimePlace p hp).valuation_lt_one_iff_mem (K := ℚ) (p : ℤ)).mpr hm
  have he := (rationalPrimePlace p hp).valuedAdicCompletion_eq_valuation (K := ℚ) (p : ℤ)
  have hv : (Valued.v (R := rationalPrimeLocalField p hp) (Γ₀ := ℤᵐ⁰))
      (p : rationalPrimeLocalField p hp) < 1 := by
    simpa using he.trans_lt hb
  have hr := (Valuation.vlt_one_iff
    (Valued.v (R := rationalPrimeLocalField p hp) (Γ₀ := ℤᵐ⁰))).mpr hv
  have hn := (Valuation.vlt_one_iff
    (NormedField.valuation (K := rationalPrimeLocalField p hp))).mp hr
  exact_mod_cast hn

/-- The same original prime is still in the maximal ideal after the
spectral extension to its original algebraic closure. -/
theorem rationalPrimeOriginalClosureNorm_prime_lt_one (p : ℕ) (hp : p.Prime) :
    ‖(p : rationalPrimeLocalClosure p hp)‖ < 1 := by
  have he : ‖algebraMap (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)
      (p : rationalPrimeLocalField p hp)‖ = ‖(p : rationalPrimeLocalField p hp)‖ :=
    norm_algebraMap' _ _
  rw [map_natCast] at he
  exact he.trans_lt (rationalPrimeOriginalNorm_prime_lt_one p hp)

end
end Dubon2026
