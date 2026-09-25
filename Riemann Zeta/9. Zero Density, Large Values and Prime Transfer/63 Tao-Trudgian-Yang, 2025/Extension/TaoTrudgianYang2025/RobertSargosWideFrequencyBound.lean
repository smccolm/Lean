import TaoTrudgianYang2025.RobertSargosWideFrequencyCount

/-! The full primitive six-variable target bound in the regime H <= Q. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem robertSargos_wide_frequency_loss_algebra {R H Q δ ε : ℝ}
    (hR : 1 ≤ R) (hH : 1 ≤ H) (hQ : 1 ≤ Q)
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (hHQ : H ≤ Q) :
    H^ε*(R*H^2+δ*R*H*Q^2) ≤ (R*H*Q)^(1+ε)*(1+δ*Q) := by
  have hHp : 0 < H := by linarith
  have hB : 0 < R*H*Q := by positivity
  have hHB : H ≤ R*H*Q :=
    (le_mul_of_one_le_left hHp.le hR).trans
      (le_mul_of_one_le_right (by positivity : 0 ≤ R*H) hQ)
  have hp := Real.rpow_le_rpow hHp.le hHB hε
  have hs : R*H^2+δ*R*H*Q^2 ≤ (R*H*Q)*(1+δ*Q) := by
    have hm := mul_le_mul_of_nonneg_left hHQ (by positivity : 0 ≤ R*H)
    nlinarith only [hm]
  calc
    _ ≤ (R*H*Q)^ε*((R*H*Q)*(1+δ*Q)) :=
      mul_le_mul hp hs (by positivity) (Real.rpow_nonneg hB.le _)
    _ = _ := by rw [Real.rpow_add hB,Real.rpow_one]; ring

theorem exists_robertSargos_primitive_count_wide_frequency (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset RobertSargosPoint) (R H Q δ : ℝ),
      1 ≤ R → 1 ≤ H → 1 ≤ Q → 0 ≤ δ → R ≤ H/2 → H ≤ Q →
      (∀ p ∈ S, RobertSargosPrimitiveSystem R H Q δ p) →
      (S.card:ℝ) ≤ C*(R*H*Q)^(1+ε)*(1+δ*Q) := by
  obtain ⟨C,hC,hcount⟩ := exists_robertSargos_primitive_count_coefficient_bound ε hε
  refine ⟨C,hC,?_⟩
  intro S R H Q δ hR hH hQ hδ hRH hHQ hmem
  have hb := hcount S R H Q δ hR hH (by linarith) hδ hRH hmem
  calc
    _ ≤ C*H^ε*(R*H^2+δ*R*H*Q^2) := hb
    _ = C*(H^ε*(R*H^2+δ*R*H*Q^2)) := by ring
    _ ≤ C*((R*H*Q)^(1+ε)*(1+δ*Q)) :=
      mul_le_mul_of_nonneg_left (robertSargos_wide_frequency_loss_algebra
        hR hH hQ hδ hε.le hHQ) hC.le
    _ = _ := by ring

end TaoTrudgianYang2025

