import TaoTrudgianYang2025.RobertSargosNormalizedFrequency
import TaoTrudgianYang2025.RobertSargosPrimitiveCount

/-! Actual unnormalized source fibers are counted by their injective primitive normalization. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem exists_robertSargos_gcd_fiber_count (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset RobertSargosPoint) (R H Q δ : ℝ) (j k : ℕ),
      1 ≤ R → 1 ≤ H → 1 ≤ Q → 0 ≤ δ → R ≤ H/2 →
      (∀ p ∈ S, RobertSargosReducedSystem R H Q δ p) →
      (∀ p ∈ S, j = robertSargosCoefficientGcd p) →
      (∀ p ∈ S, k = robertSargosFrequencyGcd p) →
      (S.card:ℝ) ≤ C*((R/j)*(H/j)*(max 1 (Q/k)))^(1+ε)*
        (1+δ*max 1 (Q/k)) := by
  classical
  obtain ⟨C,hC,hbound⟩ := exists_robertSargos_primitive_count ε hε
  refine ⟨C,hC,?_⟩
  intro S R H Q δ j k hR hH hQ hδ hRH hmem hj hk
  by_cases hs : S.Nonempty
  · obtain ⟨p₀,hp₀⟩ := hs
    have hjp : 0 < j := hj p₀ hp₀ ▸ (hmem p₀ hp₀).coefficient_gcd_pos
    have hjR : (j:ℝ) ≤ R := by
      rw [hj p₀ hp₀]
      exact (hmem p₀ hp₀).coefficient_gcd_le
    have hsc := robertSargos_normalized_scale_conditions (Q := Q) k hjp hjR hRH
    let T := S.image (robertSargosNormalize j k)
    have hcard : T.card = S.card :=
      Finset.card_image_of_injOn (robertSargos_normalize_injective_on_gcd_fiber S hj hk)
    have hT : ∀ p ∈ T, RobertSargosPrimitiveSystem (R/j) (H/j) (max 1 (Q/k)) δ p := by
      intro q hq
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
      exact (hmem p hp).normalized_primitive (by linarith) (by linarith) hδ
        (hj p hp) (hk p hp)
    have hb := hbound T (R/j) (H/j) (max 1 (Q/k)) δ
      hsc.1 hsc.2.1 hsc.2.2.1 hδ hsc.2.2.2 hT
    rwa [hcard] at hb
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    simp only [Finset.card_empty,Nat.cast_zero]
    positivity

end TaoTrudgianYang2025

