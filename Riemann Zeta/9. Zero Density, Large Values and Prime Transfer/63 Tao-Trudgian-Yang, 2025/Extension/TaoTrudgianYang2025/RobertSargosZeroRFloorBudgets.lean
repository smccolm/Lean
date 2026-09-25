import TaoTrudgianYang2025.RobertSargosZeroRPolynomialBudget
import TaoTrudgianYang2025.ThirteenthRootScales

/-! Every zero-r budget at the actual Q and R floor choices. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem robertSargos_zero_r_floor_budgets
    (M H : ℕ) {lam : ℝ} (hH : 0 < H)
    (hlam : 0 < lam) (hsmall : lam ≤ 1/8192)
    (hM : lam^(-(8:ℝ)/13) ≤ M) (hHmax : (H:ℝ) ≤ lam^(-(2:ℝ)/13)/2) :
    0 < ⌊lam^(-(3:ℝ)/13)⌋₊ ∧ 0 < ⌊lam^(-(1:ℝ)/13)⌋₊ ∧
      4*(H:ℝ)*(⌊lam^(-(3:ℝ)/13)⌋₊:ℝ)*lam ≤ 1 ∧
      (H:ℝ)^2 ≤ (M:ℝ)*(⌊lam^(-(1:ℝ)/13)⌋₊:ℝ) ∧
      (H:ℝ)^5*(⌊lam^(-(3:ℝ)/13)⌋₊:ℝ)*lam ≤ (⌊lam^(-(1:ℝ)/13)⌋₊:ℝ)^2 ∧
      (H:ℝ)^3 ≤ (M:ℝ)^2*(⌊lam^(-(1:ℝ)/13)⌋₊:ℝ)^2*
        (⌊lam^(-(3:ℝ)/13)⌋₊:ℝ)*lam := by
  let T := lam^(-(1:ℝ)/13)
  obtain ⟨hT,hscale⟩ := thirteenth_root_physical_scale hlam hsmall
  have h8 : T^8 = lam^(-(8:ℝ)/13) := by
    dsimp [T]
    simpa only [Nat.cast_ofNat] using thirteenth_root_nat_pow hlam 8
  have h2 : T^2 = lam^(-(2:ℝ)/13) := by
    dsimp [T]
    simpa only [Nat.cast_ofNat] using thirteenth_root_nat_pow hlam 2
  have h3 : T^3 = lam^(-(3:ℝ)/13) := by
    dsimp [T]
    simpa only [Nat.cast_ofNat] using thirteenth_root_nat_pow hlam 3
  have hT1 : 1 ≤ T := by dsimp [T]; linarith
  have hQ1 : 1 ≤ lam^(-(3:ℝ)/13) := by
    rw [← h3]
    exact one_le_pow₀ hT1
  obtain ⟨hQ,hQlo,hQhi⟩ := positive_floor_half_bounds hQ1
  obtain ⟨hR,hRlo,_⟩ := positive_floor_half_bounds hT1
  have hM' : T^8 ≤ (M:ℝ) := by rwa [h8]
  have hH' : (H:ℝ) ≤ T^2/2 := by rwa [h2]
  have hQlo' : T^3/2 ≤ (⌊lam^(-(3:ℝ)/13)⌋₊:ℝ) := by rwa [h3]
  have hQhi' : (⌊lam^(-(3:ℝ)/13)⌋₊:ℝ) ≤ T^3 := by rwa [h3]
  have hb := zero_r_physical_polynomial_budgets
    (T := T) (M := (M:ℝ)) (H := (H:ℝ))
    (Q := (⌊lam^(-(3:ℝ)/13)⌋₊:ℝ)) (R := (⌊lam^(-(1:ℝ)/13)⌋₊:ℝ))
    hT hM' (by exact_mod_cast hH) hH' hQlo' hQhi' hRlo hlam hscale
  exact ⟨hQ,hR,hb⟩

end TaoTrudgianYang2025
