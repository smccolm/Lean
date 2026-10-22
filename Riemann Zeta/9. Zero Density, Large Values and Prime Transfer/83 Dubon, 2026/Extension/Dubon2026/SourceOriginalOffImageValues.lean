import Dubon2026.SourceOriginalComplexTranslations
import Dubon2026.SourceOriginalPlaceEvaluation
import Dubon2026.SourceCurveCoordinateValues

/-! DUB-17/18 -> torsion surjectivity -> exclusion of nonarithmetic support.
Every complex place outside the arithmetic image has a finite j-value outside
Qbar. Existing exact orders off the image and the original residue-value
bijection prove both assertions; no generic-place specification is introduced.
-/
namespace Dubon2026.SourceFunctionField.OriginalConstantField
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ) [NeZero N]
local notation "FQ" => modularFunctionFieldOver N Qbar
local notation "FC" => modularFunctionFieldOver N ℂ

theorem off_image_exists_nonarithmetic_j_value (W : Place ℂ FC)
    (hW : ∀ P, W ≠ liftPlace N P) :
    ∃ t : ℂ, t ∉ Set.range sigma ∧ 0 < W.ord (jOver N ℂ - algebraMap ℂ FC t) := by
  have hj : W.ord (jOver N ℂ) = 0 := by
    rw [← fieldMap_j N]
    exact ord_phi_of_forall_ne N hW (jOver N Qbar)
  obtain ⟨t, ht, _⟩ := W.exists_unique_coordinate_value
    (original_place_residue_algebraMap_bijective N ℂ W).surjective
    (transcendental_jOver N ℂ) (W.mem_of_ord_nonneg hj.ge)
  refine ⟨t, ?_, ht⟩
  rintro ⟨a, rfl⟩
  have he : jOver N ℂ - algebraMap ℂ FC (sigma a) =
      fieldMap N (jOver N Qbar - algebraMap Qbar FQ a) := by
    rw [map_sub, fieldMap_j, fieldMap_constants]
  rw [he, ord_phi_of_forall_ne N hW] at ht
  exact (lt_irrefl 0) ht

theorem original_j_value_arithmetic (τ : ℂ ≃ₐ[ℚ] ℂ) (W : Place ℂ FC) {t : ℂ}
    (ht : 0 < W.ord (jOver N ℂ - algebraMap ℂ FC t)) :
    originalPlaceEval N ℂ (originalArithmeticPlace N τ W) (jOver N ℂ) = τ t := by
  apply originalPlaceEval_eq_of_ord_sub_pos
  have h := originalArithmeticPlace_ord_action N τ W (jOver N ℂ - algebraMap ℂ FC t)
  rw [map_sub, originalArithmeticRingAut_j, originalArithmeticRingAut_constants] at h
  rw [h]
  exact ht

end
end Dubon2026.SourceFunctionField.OriginalConstantField
