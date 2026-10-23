import Dubon2026.SourceModularFiniteCoefficientSpan

/-! DUB-17/18 -> original Frobenius/inertia -> good/place reduction ->
actual coefficient valuation on the modular function field. An integral Laurent
fraction has a denominator with nonzero literal coefficient reduction. Primitive
normalization of finite integer coefficient spans puts every actual modular
function or its inverse in this ring. This constructs the valuation ring; its
residue map and good-reduction properties still require their own consumers.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, constant-reduction construction.
Native finite-span selection replaces the external finite-subset argument. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open Polynomial IntermediateField
open scoped Classical

variable {L : Type*} [Field L] (A : ValuationSubring L) (N : ℕ)

local notation "FF" => modularFunctionFieldCoeff N L

theorem exists_frac_form (f : FF) (hf : f ≠ 0) :
    ∃ c : L, c ≠ 0 ∧ ∃ x₀ y₀ : LaurentSeries A, ϖ A x₀ ≠ 0 ∧ ϖ A y₀ ≠ 0 ∧
      ι A x₀ ∈ FF ∧ ι A y₀ ∈ FF ∧
      (f : LaurentSeries L) * ι A y₀ = algebraMap L (LaurentSeries L) c * ι A x₀ := by
  have hfF : (f : LaurentSeries L) ∈ adjoin L (divisorExpansionsCoeff N L) := f.2
  obtain ⟨r, hr, s, hs, hrs⟩ := (mem_adjoin_iff_div (F := L)).mp hfF
  have hf0' : (f : LaurentSeries L) ≠ 0 := fun h => hf (Subtype.ext h)
  have hr0 : r ≠ 0 := by rintro rfl; exact hf0' (by rw [hrs, zero_div])
  have hs0 : s ≠ 0 := by rintro rfl; exact hf0' (by rw [hrs, div_zero])
  obtain ⟨Mr, hMr, hrM⟩ := exists_fg_coeff_mem L N hr
  obtain ⟨Ms, hMs, hsM⟩ := exists_fg_coeff_mem L N hs
  obtain ⟨cr, hcr, r₀, hr₀, hr'⟩ := exists_primitive_form A hr0 Mr hMr hrM
  obtain ⟨cs, hcs, s₀, hs₀, hs'⟩ := exists_primitive_form A hs0 Ms hMs hsM
  have hmem {x : LaurentSeries L} (hx : x ∈ Algebra.adjoin L (divisorExpansionsCoeff N L))
      {c : L} (hc : c ≠ 0) {z : LaurentSeries A}
      (hz : x = algebraMap L (LaurentSeries L) c * ι A z) : ι A z ∈ FF := by
    have he : ι A z = algebraMap L (LaurentSeries L) c⁻¹ * x := by
      rw [hz, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
    rw [he]
    exact mul_mem ((modularFunctionFieldCoeff N L).algebraMap_mem _)
      (IntermediateField.algebra_adjoin_le_adjoin L _ hx)
  have hιs : ι A s₀ ≠ 0 := by rw [Ne, ι_eq_zero_iff]; exact ϖ_ne_zero_ne_zero hs₀
  refine ⟨cr / cs, div_ne_zero hcr hcs, r₀, s₀, hr₀, hs₀,
    hmem hr hcr hr', hmem hs hcs hs', ?_⟩
  rw [hrs, hr', hs', map_div₀]
  field_simp

end
end Dubon2026.SourceFunctionField.GaussReduction
