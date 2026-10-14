import Dubon2026.RationalFinitePrimeProduct
import Dubon2026.RationalPrimeNormalizedValuation

/-! # The rational prime product with the original normalized local orders

The actual local reciprocity exponent equals the original finite valuation
exponent. Its support is proved finite, and the corresponding positive prime
product equals the absolute value of the same rational unit. These are the
rational normalization and support obligations in DUB-17's cyclotomic
principal product; the ramified reciprocity factor remains separate.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped BigOperators

/-- The actual positive prime generator returns its original finite place. -/
theorem rationalPrimePlace_of_natGenerator (v : HeightOneSpectrum ℤ) :
    rationalPrimePlace (Rat.HeightOneSpectrum.natGenerator v)
      (Rat.HeightOneSpectrum.prime_natGenerator v) = v := by
  exact Rat.HeightOneSpectrum.primesEquiv.symm_apply_apply v

/-- The positive rational prime product has exactly the original normalized local reciprocity exponents. -/
theorem rationalPositivePrimeProduct_normalized_order
    (S : Finset (HeightOneSpectrum ℤ)) (u : ℚˣ)
    (hS : ∀ v ∉ S, v.valuation ℚ u.val = 1) :
    (∏ v ∈ S, (Rat.HeightOneSpectrum.natGenerator v : ℚ) ^
      localFieldUnitOrder
        (rationalPrimeLocalField (Rat.HeightOneSpectrum.natGenerator v)
          (Rat.HeightOneSpectrum.prime_natGenerator v))
        (Additive.ofMul (Units.map (algebraMap ℚ
          (rationalPrimeLocalField (Rat.HeightOneSpectrum.natGenerator v)
            (Rat.HeightOneSpectrum.prime_natGenerator v))).toMonoidHom u))) = |u.val| := by
  simp_rw [rationalPrimeLocalField_rational_order, rationalPrimePlace_of_natGenerator]
  exact rationalPositivePrimeProduct_eq_abs S u.val u.ne_zero hS

/-- A rational unit has only finitely many nonunit original finite-place valuations; the support is constructed from the existing integral supports of it and its inverse. -/
theorem rationalFiniteValuation_ne_one_finite (u : ℚˣ) :
    {v : HeightOneSpectrum ℤ | v.valuation ℚ u.val ≠ 1}.Finite := by
  apply ((Support.finite ℤ u.val).union (Support.finite ℤ u.val⁻¹)).subset
  intro v hv
  change v.valuation ℚ u.val ≠ 1 at hv
  change 1 < v.valuation ℚ u.val ∨ 1 < v.valuation ℚ u.val⁻¹
  rcases lt_or_gt_of_ne hv with h | h
  · right
    rw [map_inv₀]
    exact one_lt_inv₀ ((v.valuation ℚ).pos_iff.mpr u.ne_zero) |>.mpr h
  · exact Or.inl h

/-- The required original rational prime product has an actual finite support and no support hypothesis. -/
theorem rationalPositivePrimeProduct_exists_support (u : ℚˣ) :
    ∃ S : Finset (HeightOneSpectrum ℤ),
      (∀ v ∉ S, v.valuation ℚ u.val = 1) ∧
      (∏ v ∈ S, (Rat.HeightOneSpectrum.natGenerator v : ℚ) ^
        localFieldUnitOrder
          (rationalPrimeLocalField (Rat.HeightOneSpectrum.natGenerator v)
            (Rat.HeightOneSpectrum.prime_natGenerator v))
          (Additive.ofMul (Units.map (algebraMap ℚ
            (rationalPrimeLocalField (Rat.HeightOneSpectrum.natGenerator v)
              (Rat.HeightOneSpectrum.prime_natGenerator v))).toMonoidHom u))) = |u.val| := by
  classical
  let S := (rationalFiniteValuation_ne_one_finite u).toFinset
  have hS : ∀ v ∉ S, v.valuation ℚ u.val = 1 := by
    intro v hv
    simpa only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] using hv
  exact ⟨S, hS, rationalPositivePrimeProduct_normalized_order S u hS⟩

end
end Dubon2026
