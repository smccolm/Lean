import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Algebraic.Integral

/-! # One positive rational-integer denominator for a fixed number-field matrix

This supplies the uniform scalar for the specified CM Hermitian form in
DUB-17's trace-lattice argument. The scalar depends only on its finitely
many original coefficients, not on an adelic matrix or attached lattice.
-/

namespace Dubon2026

noncomputable section

open NumberField

/-- A finite family of original number-field elements has one positive integer integral multiple. -/
theorem numberField_exists_positive_integral_multiple
    {K ι : Type*} [Field K] [NumberField K] [Fintype ι] (x : ι → K) :
    ∃ d : ℤ, 0 < d ∧ ∀ i, IsIntegral ℤ (d • x i) := by
  classical
  letI := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  letI := Algebra.IsAlgebraic.trans ℤ ℚ K
  obtain ⟨d, hd, hi⟩ := Algebra.IsAlgebraic.exists_integral_multiples ℤ (Finset.univ.image x)
  refine ⟨d * d, mul_self_pos.mpr hd, ?_⟩
  intro i
  have h := (hi (x i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)).smul d
  simpa only [smul_smul] using h

end
end Dubon2026
