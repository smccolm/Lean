import Dubon2026.SourceOriginalSimplePoleBounds

/-! DUB-17/18 -> original Abel-Jacobi -> meromorphic loop-period generation.
The finite-family path argument must cover every original differential with
simple poles in the specified finite set. Model precisely that space, reusing
the existing simple-pole bounds and original linear coefficient map.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

/-- Original differentials with at most simple poles, all contained in the given finite set. -/
def originalSimplePoleSpace (S : Finset (Place ℂ F)) : Submodule ℂ Ω[F⁄ℂ] where
  carrier := {θ | ∀ v : Place ℂ F, -1 ≤ v.ordDifferential θ ∧ (v ∉ S → 0 ≤ v.ordDifferential θ)}
  zero_mem' v := by
    refine ⟨original_simple_pole_zero_bound N v, fun _ => ?_⟩
    change 0 ≤ v.ord (originalDifferentialCoeff N v 0)
    rw [map_zero, v.ord_zero]
  add_mem' {θ₁ θ₂} h₁ h₂ v := by
    refine ⟨original_simple_pole_add_bound N v (h₁ v).1 (h₂ v).1, fun hv => ?_⟩
    apply v.ord_nonneg_of_mem
    change originalDifferentialCoeff N v (θ₁ + θ₂) ∈ v.toValuationSubring
    rw [map_add]
    exact add_mem (v.mem_of_ord_nonneg ((h₁ v).2 hv)) (v.mem_of_ord_nonneg ((h₂ v).2 hv))
  smul_mem' c {θ} h v := by
    refine ⟨original_simple_pole_smul_bound N v c (h v).1, fun hv => ?_⟩
    apply v.ord_nonneg_of_mem
    change originalDifferentialCoeff N v (c • θ) ∈ v.toValuationSubring
    rw [map_smul, Algebra.smul_def]
    exact mul_mem (v.algebraMap_mem' c) (v.mem_of_ord_nonneg ((h v).2 hv))

end
end Dubon2026.SourceFunctionField
