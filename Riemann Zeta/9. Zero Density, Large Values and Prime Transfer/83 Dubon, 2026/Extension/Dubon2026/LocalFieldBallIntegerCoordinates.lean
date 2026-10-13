import Dubon2026.NormedFieldSmallUnitGradedQuotient
import Dubon2026.LocalFieldOriginalNorm
import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Actual integer coordinates on original local-field balls

The finite-place power index for DUB-17 reduces to an additive ball quotient.
Multiplication by its actual radius element identifies that ball with the
original integer ring, preserving the scalar quotient needed for its order.
-/

namespace Dubon2026
noncomputable section
open scoped ValuativeRel

variable (K : Type) [Field K] [ValuativeRel K]
  [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K]

/-- The original local-field NontriviallyNormedField structure used for this calculation. -/
local instance localFieldBallIntegerCoordinatesNorm : NontriviallyNormedField K := localFieldOriginalNorm K
/-- The original local-field IsUltrametricDist structure used for this calculation. -/
local instance localFieldBallIntegerCoordinatesUltrametric : IsUltrametricDist K := localFieldOriginalNorm_isUltrametric K

/-- The compatible norm recognizes membership in the actual original
integer ring. -/
theorem localFieldOriginalNorm_integer_iff (x : K) :
    x ∈ (ValuativeRel.valuation K).integer ↔ ‖x‖ ≤ 1 := by
  change ValuativeRel.valuation K x ≤ 1 ↔ ‖x‖ ≤ 1
  simpa only [map_one, norm_one] using (localFieldOriginalNorm_le_iff K x 1).symm

/-- Multiplication by an actual nonzero field element identifies the original
integer ring with the additive closed ball of that element's norm. -/
def localFieldIntegerBallEquiv (a : K) (ha : a ≠ 0) :
    𝒪[K] ≃ₗ[ℤ] normedFieldBallModule K ‖a‖ (norm_pos_iff.mpr ha) where
  toFun x := ⟨a * (x : K), (normedFieldBallModule_mem K ‖a‖ _ _).mpr (by
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) ((localFieldOriginalNorm_integer_iff K x).mp x.property))⟩
  invFun x := ⟨(x : K) / a, (localFieldOriginalNorm_integer_iff K _).mpr (by
    rw [norm_div]
    exact (div_le_one (norm_pos_iff.mpr ha)).mpr
      ((normedFieldBallModule_mem K ‖a‖ _ x).mp x.property))⟩
  left_inv x := by
    apply Subtype.ext
    change a * (x : K) / a = (x : K)
    exact mul_div_cancel_left₀ (x : K) ha
  right_inv x := by
    apply Subtype.ext
    change a * ((x : K) / a) = (x : K)
    exact mul_div_cancel₀ (x : K) ha
  map_add' x y := by
    apply Subtype.ext
    exact mul_add a (x : K) (y : K)
  map_smul' z x := by
    apply Subtype.ext
    change a * (z • (x : K)) = z • (a * (x : K))
    simp only [zsmul_eq_mul]
    ring

/-- The original integer coordinate map retains its literal field value. -/
theorem localFieldIntegerBallEquiv_apply (a : K) (ha : a ≠ 0) (x : 𝒪[K]) :
    (localFieldIntegerBallEquiv K a ha x : K) = a * (x : K) := rfl

end
end Dubon2026
