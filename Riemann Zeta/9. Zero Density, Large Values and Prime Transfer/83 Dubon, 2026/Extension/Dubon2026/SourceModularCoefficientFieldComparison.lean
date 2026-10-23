import Dubon2026.SourceModularFunctionFieldCoefficients
import Dubon2026.SourceOriginalFieldGeneration

/-! DUB-17/18 -> original Frobenius/inertia compatibility -> reduction
of the exact original curve. The coefficient-field definition recovers
the existing rational scalar-extension field verbatim in characteristic
zero. This identifies the entry into the reduction chain; no new or
unrelated modular curve is substituted. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open IntermediateField
variable (N : ℕ) (K : Type*) [Field K] [Algebra ℚ K]

theorem divisorExpansionsCoeff_eq_original_image :
    divisorExpansionsCoeff N K = coeffEmb K '' divisorExpansions N := by
  ext x
  constructor
  · rintro ⟨d, hd0, hd, rfl⟩
    letI := hd0
    refine ⟨qExpand ℚ d jq, ⟨d, hd0, hd, rfl⟩, ?_⟩
    change coeffMap (algebraMap ℚ K) (qExpand ℚ d jq) = qExpand K d (jqModC K)
    rw [coeffMap_qExpand, ← coeffEmb_jq K]
    rfl
  · rintro ⟨y, ⟨d, hd0, hd, rfl⟩, rfl⟩
    letI := hd0
    refine ⟨d, hd0, hd, ?_⟩
    change coeffMap (algebraMap ℚ K) (qExpand ℚ d jq) = qExpand K d (jqModC K)
    rw [coeffMap_qExpand, ← coeffEmb_jq K]
    rfl

theorem modularFunctionFieldCoeff_eq_original :
    modularFunctionFieldCoeff N K = modularFunctionFieldOver N K := by
  rw [modularFunctionFieldCoeff, modularFunctionFieldOver,
    laurentBaseChange_full_eq_adjoin, divisorExpansionsCoeff_eq_original_image]

end
end Dubon2026.SourceFunctionField
