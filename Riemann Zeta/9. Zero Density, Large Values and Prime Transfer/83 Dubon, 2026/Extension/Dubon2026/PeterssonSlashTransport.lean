import Dubon2026.ModularGamma0Domain

/-! # Exact determinant factors in Petersson change of variables -/

namespace Dubon2026

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups ModularForm Pointwise

noncomputable section

/-- Hyperbolic integration over a genuine matrix translate is exact change of variables. -/
theorem integral_matrix_translate (A : GL (Fin 2) ℝ) (S : Set ℍ) (F : ℍ → ℂ) :
    ∫ τ in A • S, F τ ∂(volume : Measure ℍ) =
      ∫ τ in S, F (A • τ) ∂(volume : Measure ℍ) :=
  (measurePreserving_smul A (volume : Measure ℍ)).setIntegral_image_emb
    (measurableEmbedding_const_smul A) F S

/-- Slashing both arguments has the actual determinant power dictated by Mathlib's convention. -/
theorem peterssonIntegral_slash_both (k : ℤ) (f g : ℍ → ℂ)
    (A : GL (Fin 2) ℝ) (hA : 0 < A.det.val) (S : Set ℍ) :
    ∫ τ in S, petersson k (f ∣[k] A) (g ∣[k] A) τ ∂(volume : Measure ℍ) =
      (A.det.val : ℂ) ^ (k - 2) * ∫ τ in A • S, petersson k f g τ ∂(volume : Measure ℍ) := by
  have he : petersson k (f ∣[k] A) (g ∣[k] A) =
      fun τ => (A.det.val : ℂ) ^ (k - 2) * petersson k f g (A • τ) := by
    funext τ
    rw [petersson_slash]
    have hdet : 0 < A.val.det := hA
    simp [UpperHalfPlane.σ, hdet, abs_of_pos hdet]
  rw [he, integral_const_mul, integral_matrix_translate]

/-- Moving one genuine slash operator across the integral uses the inverse and the exact factor. -/
theorem peterssonIntegral_slash_left (k : ℤ) (f g : ℍ → ℂ)
    (A : GL (Fin 2) ℝ) (hA : 0 < A.det.val) (S : Set ℍ) :
    ∫ τ in S, petersson k (f ∣[k] A) g τ ∂(volume : Measure ℍ) =
      (A.det.val : ℂ) ^ (k - 2) *
        ∫ τ in A • S, petersson k f (g ∣[k] A⁻¹) τ ∂(volume : Measure ℍ) := by
  have hcancel : (g ∣[k] A⁻¹) ∣[k] A = g := by
    rw [← SlashAction.slash_mul, inv_mul_cancel, SlashAction.slash_one]
  simpa only [hcancel] using peterssonIntegral_slash_both k f (g ∣[k] A⁻¹) A hA S

end
end Dubon2026
