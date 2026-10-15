import Dubon2026.RationalNormalizedPrimeProduct

/-! # Signed rational reconstruction from normalized local orders

The existing normalized finite-prime product reconstructs the absolute value
of a rational unit.  Multiplying by its actual real sign reconstructs the
rational unit itself.  This is the exact finite/real factorization needed to
compare the away-from-conductor cyclotomic reciprocity factors with the
ramified rational-unit cancellation.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped BigOperators

/-- The normalized finite-prime product, multiplied by the actual real sign,
is the original rational unit. -/
theorem rationalSignedPrimeProduct_eq
    (S : Finset (HeightOneSpectrum ℤ)) (u : ℚˣ)
    (hS : ∀ v ∉ S, v.valuation ℚ u.val = 1) :
    (if 0 < u.val then (1 : ℚ) else -1) *
      (∏ v ∈ S, (Rat.HeightOneSpectrum.natGenerator v : ℚ) ^
        localFieldUnitOrder
          (rationalPrimeLocalField (Rat.HeightOneSpectrum.natGenerator v)
            (Rat.HeightOneSpectrum.prime_natGenerator v))
          (Additive.ofMul (Units.map (algebraMap ℚ
            (rationalPrimeLocalField (Rat.HeightOneSpectrum.natGenerator v)
              (Rat.HeightOneSpectrum.prime_natGenerator v))).toMonoidHom u))) = u.val := by
  rw [rationalPositivePrimeProduct_normalized_order S u hS]
  by_cases hu : 0 < u.val
  · simp [hu, abs_of_pos hu]
  · have hneg : u.val < 0 := lt_of_le_of_ne (le_of_not_gt hu) u.ne_zero
    simp [hu, abs_of_neg hneg]

/-- Every rational unit has a finite normalized-prime support whose product,
together with its real sign, is exactly that unit. -/
theorem rationalSignedPrimeProduct_exists_support (u : ℚˣ) :
    ∃ S : Finset (HeightOneSpectrum ℤ),
      (∀ v ∉ S, v.valuation ℚ u.val = 1) ∧
      (if 0 < u.val then (1 : ℚ) else -1) *
        (∏ v ∈ S, (Rat.HeightOneSpectrum.natGenerator v : ℚ) ^
          localFieldUnitOrder
            (rationalPrimeLocalField (Rat.HeightOneSpectrum.natGenerator v)
              (Rat.HeightOneSpectrum.prime_natGenerator v))
            (Additive.ofMul (Units.map (algebraMap ℚ
              (rationalPrimeLocalField (Rat.HeightOneSpectrum.natGenerator v)
                (Rat.HeightOneSpectrum.prime_natGenerator v))).toMonoidHom u))) = u.val := by
  obtain ⟨S, hS, _⟩ := rationalPositivePrimeProduct_exists_support u
  exact ⟨S, hS, rationalSignedPrimeProduct_eq S u hS⟩

end
end Dubon2026
