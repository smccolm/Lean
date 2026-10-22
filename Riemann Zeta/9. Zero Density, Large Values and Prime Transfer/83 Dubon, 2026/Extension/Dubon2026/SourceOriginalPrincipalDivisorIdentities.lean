import Dubon2026.SourceOriginalArithmeticDivisors
import Dubon2026.SourceCurveRiemannRochSpace

/-! DUB-17/18 -> arithmetic torsion surjectivity -> invariant reduced divisors.
Exact identities for the existing original principal divisor and coefficient
action allow the unique reduced Riemann--Roch representative to be transported.
These concern literal normalized orders, not a chosen abstract divisor map.
-/
namespace Dubon2026.SourceFunctionField.OriginalConstantField
noncomputable section
open SourceCurve
variable (N : ℕ) [NeZero N] {L : Type*} [Field L] [Algebra ℚ L]
local notation "F" => modularFunctionFieldOver N L

theorem original_principal_mul {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) :
    originalPrincipalDivisor N L (f * g) = originalPrincipalDivisor N L f + originalPrincipalDivisor N L g := by
  ext v
  exact v.ord_mul hf hg

theorem original_principal_inv (f : F) :
    originalPrincipalDivisor N L f⁻¹ = -originalPrincipalDivisor N L f := by
  ext v
  exact v.ord_inv f

theorem original_principal_smul {a : L} (ha : a ≠ 0) (f : F) :
    originalPrincipalDivisor N L (a • f) = originalPrincipalDivisor N L f := by
  ext v
  change v.ord (a • f) = v.ord f
  rcases eq_or_ne f 0 with rfl | hf
  · rw [smul_zero]
  · rw [Algebra.smul_def, v.ord_mul ((map_ne_zero _).mpr ha) hf, v.ord_algebraMap, zero_add]

theorem original_principal_arithmetic (τ : L ≃ₐ[ℚ] L) (f : F) :
    originalArithmeticDivisorEquiv N τ (originalPrincipalDivisor N L f) =
      originalPrincipalDivisor N L (originalArithmeticRingAut N τ f) := by
  ext w
  obtain ⟨v, rfl⟩ := (originalArithmeticPlaceEquiv N τ).surjective w
  change originalArithmeticDivisorEquiv N τ (originalPrincipalDivisor N L f)
    (originalArithmeticPlace N τ v) = (originalArithmeticPlace N τ v).ord (originalArithmeticRingAut N τ f)
  rw [originalArithmeticDivisorEquiv_apply, originalArithmeticPlace_ord_action]
  rfl

theorem mem_original_lSpace_add_principal_iff {D : Divisor L F} {u f : F} (hu : u ≠ 0) :
    f ∈ LSpace (D + originalPrincipalDivisor N L u) ↔ f * u ∈ LSpace D := by
  rw [mem_lSpace_iff_ord, mem_lSpace_iff_ord]
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · simp only [hf, mul_ne_zero hf hu, false_or]
    constructor <;> intro h v <;> have hv := h v
    all_goals
      simp only [Finsupp.add_apply, originalPrincipalDivisor_apply, v.ord_mul hf hu] at *
      omega

omit [NeZero N] in
theorem mem_original_lSpace_arithmetic_iff (τ : L ≃ₐ[ℚ] L) {D : Divisor L F} {f : F} :
    originalArithmeticRingAut N τ f ∈ LSpace (originalArithmeticDivisorEquiv N τ D) ↔
      f ∈ LSpace D := by
  rw [mem_lSpace_iff_ord, mem_lSpace_iff_ord, map_eq_zero_iff _ (originalArithmeticRingAut N τ).injective]
  apply or_congr Iff.rfl
  constructor
  · intro h v
    have hv := h (originalArithmeticPlace N τ v)
    rwa [originalArithmeticDivisorEquiv_apply, originalArithmeticPlace_ord_action] at hv
  · intro h w
    obtain ⟨v, rfl⟩ := (originalArithmeticPlaceEquiv N τ).surjective w
    change -(originalArithmeticDivisorEquiv N τ D (originalArithmeticPlace N τ v)) ≤
      (originalArithmeticPlace N τ v).ord (originalArithmeticRingAut N τ f)
    rw [originalArithmeticDivisorEquiv_apply, originalArithmeticPlace_ord_action]
    exact h v

end
end Dubon2026.SourceFunctionField.OriginalConstantField
