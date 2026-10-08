import Dubon2026.FiniteAdeleLevelSubgroup

/-! # Actual rational generators with prescribed finite valuations -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped BigOperators

/-- A genuine integral generator of a canonical rational finite prime ideal. -/
def rationalFinitePrimeGenerator (v : HeightOneSpectrum ℤ) : ℤ :=
  Submodule.IsPrincipal.generator v.asIdeal

/-- The actual prime-ideal generator is nonzero. -/
theorem rationalFinitePrimeGenerator_ne_zero (v : HeightOneSpectrum ℤ) :
    rationalFinitePrimeGenerator v ≠ 0 := by
  exact mt (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero _).mpr v.ne_bot

/-- The original generator has its normalized valuation at its own place. -/
theorem rationalFinitePrimeGenerator_valuation_self (v : HeightOneSpectrum ℤ) :
    v.valuation ℚ (rationalFinitePrimeGenerator v : ℚ) = exp (-1 : ℤ) := by
  change v.valuation ℚ (algebraMap ℤ ℚ (rationalFinitePrimeGenerator v)) = _
  rw [valuation_of_algebraMap]
  exact v.intValuation_singleton (rationalFinitePrimeGenerator_ne_zero v)
    (Ideal.span_singleton_generator v.asIdeal).symm

/-- The same original generator is a local unit at every distinct finite prime. -/
theorem rationalFinitePrimeGenerator_valuation_other (v w : HeightOneSpectrum ℤ)
    (hvw : v ≠ w) :
    w.valuation ℚ (rationalFinitePrimeGenerator v : ℚ) = 1 := by
  change w.valuation ℚ (algebraMap ℤ ℚ (rationalFinitePrimeGenerator v)) = _
  rw [valuation_of_algebraMap, intValuation_eq_one_iff]
  intro h
  have hle : v.asIdeal ≤ w.asIdeal := by
    rw [← Ideal.span_singleton_generator v.asIdeal]
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr h)
  exact hvw (HeightOneSpectrum.asIdeal_injective
    ((HeightOneSpectrum.isMaximal v).eq_of_le w.isPrime.ne_top hle))

/-- A finite product of genuine rational prime generators with prescribed signed exponents. -/
def rationalFiniteValuationProduct (S : Finset (HeightOneSpectrum ℤ))
    (n : HeightOneSpectrum ℤ → ℤ) : ℚ :=
  ∏ v ∈ S, (rationalFinitePrimeGenerator v : ℚ) ^ n v

/-- The actual signed prime product never vanishes. -/
theorem rationalFiniteValuationProduct_ne_zero (S : Finset (HeightOneSpectrum ℤ))
    (n : HeightOneSpectrum ℤ → ℤ) : rationalFiniteValuationProduct S n ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro v _
  apply zpow_ne_zero
  exact_mod_cast rationalFinitePrimeGenerator_ne_zero v

open scoped Classical in
/-- The finite product realizes every chosen local valuation and is a unit at all other places. -/
theorem rationalFiniteValuationProduct_valuation (S : Finset (HeightOneSpectrum ℤ))
    (n : HeightOneSpectrum ℤ → ℤ) (w : HeightOneSpectrum ℤ) :
    w.valuation ℚ (rationalFiniteValuationProduct S n) =
      if w ∈ S then exp (-n w) else 1 := by
  classical
  unfold rationalFiniteValuationProduct
  rw [map_prod]
  by_cases hw : w ∈ S
  · rw [if_pos hw, Finset.prod_eq_single w]
    · rw [map_zpow₀, rationalFinitePrimeGenerator_valuation_self, ← exp_zsmul]
      congr 1
      simp
    · intro v _ hvw
      rw [map_zpow₀, rationalFinitePrimeGenerator_valuation_other v w hvw, one_zpow]
    · exact fun h => False.elim (h hw)
  · rw [if_neg hw]
    apply Finset.prod_eq_one
    intro v hv
    have hvw : v ≠ w := by intro h; exact hw (h ▸ hv)
    rw [map_zpow₀, rationalFinitePrimeGenerator_valuation_other v w hvw, one_zpow]

end
end Dubon2026
