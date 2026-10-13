import Dubon2026.SUnitLogarithmicProductFormula

/-! # Exact normalization of original finite logarithmic coordinates

The reduced coordinates use the existing valuation exponents. The
normalized absolute values therefore use the positive weights log Nv.
This explicit bridge preserves the original product-formula convention
in the full lattice comparison required by DUB-17's Herbrand quotient.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField
variable (K : Type*) [Field K] [NumberField K]
  (S : Finset (HeightOneSpectrum (𝓞 K)))

/-- The original normalized finite absolute value is the prime norm to its existing valuation exponent. -/
theorem sUnit_adicAbv_eq_zpow_valuation
    (x : (S : Set (HeightOneSpectrum (𝓞 K))).unit K) (v : S) :
    NumberField.HeightOneSpectrum.adicAbv K v.val x.val.val =
      (Ideal.absNorm v.val.asIdeal : ℝ) ^
        (sUnitValuationLinearMap (R := 𝓞 K) (K := K) S (Additive.ofMul x) v) := by
  change NumberField.HeightOneSpectrum.adicAbv K v.val x.val.val =
    (Ideal.absNorm v.val.asIdeal : ℝ) ^ (v.val.valuationOfNeZero x.val).toAdd
  rw [NumberField.HeightOneSpectrum.adicAbv_def, ← HeightOneSpectrum.valuationOfNeZero_eq,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.coe_ne_zero, WithZero.unzero_coe]
  norm_cast

/-- The original finite logarithm is the existing valuation coordinate times its positive prime-norm weight. -/
theorem sUnit_log_adicAbv_eq_coordinate
    (x : (S : Set (HeightOneSpectrum (𝓞 K))).unit K) (v : S) :
    Real.log (NumberField.HeightOneSpectrum.adicAbv K v.val x.val.val) =
      (sUnitValuationLinearMap (R := 𝓞 K) (K := K) S (Additive.ofMul x) v : ℝ) *
        Real.log (Ideal.absNorm v.val.asIdeal : ℝ) := by
  rw [sUnit_adicAbv_eq_zpow_valuation, Real.log_zpow]

/-- Every original finite-place logarithmic normalization weight is nonzero. -/
theorem sUnit_finiteLogWeight_ne_zero (v : S) :
    Real.log (Ideal.absNorm v.val.asIdeal : ℝ) ≠ 0 := by
  have h : (1 : ℝ) < (Ideal.absNorm v.val.asIdeal : ℝ) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v.val
  exact (Real.log_pos h).ne'

end
end Dubon2026
