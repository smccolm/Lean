import Dubon2026.PeterssonAdjugate

/-! # Integrability of genuine mixed slash products on finite-volume domains -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane MeasureTheory
open scoped MatrixGroups ModularForm Manifold

noncomputable section

/-- A mixed Petersson product is bounded pointwise by the two diagonal products. -/
theorem norm_petersson_le_self_add (k : ℤ) (f g : ℍ → ℂ) (τ : ℍ) :
    ‖petersson k f g τ‖ ≤ ‖petersson k f f τ‖ + ‖petersson k g g τ‖ := by
  simp only [petersson, norm_mul, Complex.norm_conj]
  have hm : ‖f τ‖ * ‖g τ‖ ≤ ‖f τ‖ * ‖f τ‖ + ‖g τ‖ * ‖g τ‖ := by
    nlinarith [sq_nonneg (‖f τ‖ - ‖g τ‖), mul_nonneg (norm_nonneg (f τ)) (norm_nonneg (g τ))]
  simpa only [add_mul] using mul_le_mul_of_nonneg_right hm (norm_nonneg ((τ.im : ℂ) ^ k))

/-- A genuine slash by any invertible matrix preserves global boundedness of the self-product. -/
theorem cusp_slash_self_bounded {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (A : GL (Fin 2) ℝ) :
    ∃ C : ℝ, ∀ τ : ℍ, ‖petersson k (⇑f ∣[k] A) (⇑f ∣[k] A) τ‖ ≤ C := by
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left k ((Gamma0 Q).map (mapGL ℝ)) f f
  refine ⟨‖((|A.det.val| : ℝ) : ℂ) ^ (k - 2)‖ * C, ?_⟩
  intro τ
  rw [petersson_slash, norm_mul, norm_σ]
  exact mul_le_mul_of_nonneg_left (hC (A • τ)) (norm_nonneg _)

/-- Two independently slashed genuine cusp forms have a globally bounded mixed integrand. -/
theorem cusp_mixed_slash_bounded {Q : ℕ} [NeZero Q] {k : ℤ}
    (f g : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (A B : GL (Fin 2) ℝ) :
    ∃ C : ℝ, ∀ τ : ℍ, ‖petersson k (⇑f ∣[k] A) (⇑g ∣[k] B) τ‖ ≤ C := by
  obtain ⟨C, hC⟩ := cusp_slash_self_bounded f A
  obtain ⟨D, hD⟩ := cusp_slash_self_bounded g B
  exact ⟨C + D, fun τ => (norm_petersson_le_self_add k _ _ τ).trans (add_le_add (hC τ) (hD τ))⟩

/-- Finite hyperbolic volume suffices for actual mixed-slash Petersson integrability. -/
theorem integrableOn_cusp_mixed_slash {Q : ℕ} [NeZero Q] {k : ℤ}
    (f g : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (A B : GL (Fin 2) ℝ)
    (S : Set ℍ) (hS : (volume : Measure ℍ) S < ⊤) :
    IntegrableOn (petersson k (⇑f ∣[k] A) (⇑g ∣[k] B)) S (volume : Measure ℍ) := by
  obtain ⟨C, hC⟩ := cusp_mixed_slash_bounded f g A B
  exact IntegrableOn.of_bound hS
    ((petersson_continuous k (f.holo'.slash k A).continuous
      (g.holo'.slash k B).continuous).aestronglyMeasurable.restrict) C (ae_of_all _ hC)

end
end Dubon2026
