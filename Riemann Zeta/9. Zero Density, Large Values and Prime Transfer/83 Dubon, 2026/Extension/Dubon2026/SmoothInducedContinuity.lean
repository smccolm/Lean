import Dubon2026.SmoothInducedCharacter
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Analysis.Complex.Basic

/-! # Genuine local constancy of the original smooth induced coefficient functions -/

namespace Dubon2026

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The original open right stabilizer makes each actual induced function locally constant on the genuine group. -/
theorem smoothInducedCharacter_isLocallyConstant (B : Subgroup G) (χ : B →* ℂ)
    (f : smoothInducedCharacterSpace B χ) : IsLocallyConstant f.val := by
  obtain ⟨H, hH, hi⟩ := f.property.2
  apply (IsLocallyConstant.iff_exists_open f.val).mpr
  intro g
  refine ⟨(fun x : G => g⁻¹ * x) ⁻¹' (H : Set G),
    hH.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · change g⁻¹ * g ∈ H
    simpa only [inv_mul_cancel] using H.one_mem
  · intro x hx
    have he := hi (g⁻¹ * x) hx g
    simpa only [mul_inv_cancel_left] using he

/-- Every original smooth induced coefficient function is continuous for the actual group topology. -/
theorem smoothInducedCharacter_continuous (B : Subgroup G) (χ : B →* ℂ)
    (f : smoothInducedCharacterSpace B χ) : Continuous f.val :=
  (smoothInducedCharacter_isLocallyConstant B χ f).continuous

end
end Dubon2026
