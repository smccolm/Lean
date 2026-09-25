import TaoTrudgianYang2025.RobertSargosZeroQPolynomialBudget

/-! Zero-q budgets with the exact source Q and R floors, including their losses. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem robertSargos_zero_q_floor_budgets (M H : ℕ) {lam : ℝ}
    (hlam : 0 < lam) (hsmall : lam ≤ 1/8192)
    (hM : lam^(-(8:ℝ)/13) ≤ M) (hH : (H:ℝ) ≤ lam^(-(2:ℝ)/13)/2) :
    0 < ⌊lam^(-(3:ℝ)/13)⌋₊ ∧ 0 < ⌊lam^(-(1:ℝ)/13)⌋₊ ∧
      (⌊lam^(-(1:ℝ)/13)⌋₊:ℝ) ≤ lam^(-(1:ℝ)/13) ∧
      (H:ℝ)^2 ≤ (M:ℝ)*(⌊lam^(-(3:ℝ)/13)⌋₊:ℝ)/2 ∧
      (H:ℝ)^2*(⌊lam^(-(1:ℝ)/13)⌋₊:ℝ) ≤ (M:ℝ)*(⌊lam^(-(3:ℝ)/13)⌋₊:ℝ)/2 ∧
      (H:ℝ)^2*(2*(⌊lam^(-(1:ℝ)/13)⌋₊:ℝ)*lam)^((1:ℝ)/12) ≤
        (⌊lam^(-(3:ℝ)/13)⌋₊:ℝ) := by
  let T := lam^(-(1:ℝ)/13)
  obtain ⟨hT,hscale⟩ := thirteenth_root_physical_scale hlam hsmall
  have hT1 : 1 ≤ T := by dsimp [T]; linarith
  have h8 : T^8 = lam^(-(8:ℝ)/13) := by
    simpa only [Nat.cast_ofNat] using thirteenth_root_nat_pow hlam 8
  have h2 : T^2 = lam^(-(2:ℝ)/13) := by
    simpa only [Nat.cast_ofNat] using thirteenth_root_nat_pow hlam 2
  have h3 : T^3 = lam^(-(3:ℝ)/13) := by
    simpa only [Nat.cast_ofNat] using thirteenth_root_nat_pow hlam 3
  have hQ1 : 1 ≤ lam^(-(3:ℝ)/13) := by
    rw [← h3]
    exact one_le_pow₀ hT1
  obtain ⟨hQ,hQlo,_⟩ := positive_floor_half_bounds hQ1
  obtain ⟨hR,_,hRhi⟩ := positive_floor_half_bounds hT1
  have hb := zero_q_physical_polynomial_budgets
    (T := T) (M := (M:ℝ)) (H := (H:ℝ))
    (Q := (⌊lam^(-(3:ℝ)/13)⌋₊:ℝ)) (R := (⌊lam^(-(1:ℝ)/13)⌋₊:ℝ))
    hT (by rwa [h8]) (Nat.cast_nonneg H) (by rwa [h2]) (by rwa [h3])
    (Nat.cast_nonneg _) hRhi hlam hscale
  exact ⟨hQ,hR,hRhi,hb⟩

end TaoTrudgianYang2025
