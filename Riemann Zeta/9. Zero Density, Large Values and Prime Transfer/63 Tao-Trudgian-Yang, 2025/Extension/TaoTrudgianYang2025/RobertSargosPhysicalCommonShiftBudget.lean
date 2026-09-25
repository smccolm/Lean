import TaoTrudgianYang2025.RobertSargosPhysicalATimesAParameters

/-! The corrected common-interval boundary charge at N=Q=floor(lambda^(-3/13)). -/

noncomputable section
namespace TaoTrudgianYang2025

theorem robertSargos_physical_common_shift_budget (M H : ℕ) {lam : ℝ}
    (hlam : 0 < lam) (hsmall : lam ≤ 1/8192)
    (hM : lam^(-(8:ℝ)/13) ≤ M) (hHmax : (H:ℝ) ≤ lam^(-(2:ℝ)/13)/2) :
    8*(M:ℝ)*(H:ℝ)^2*(4*(H:ℝ)+6*(⌊lam^(-(3:ℝ)/13)⌋₊:ℝ)) ≤ 16*(M:ℝ)^2 := by
  let T := lam^(-(1:ℝ)/13)
  have hT : 2 ≤ T := (thirteenth_root_physical_scale hlam hsmall).1
  have hT1 : 1 ≤ T := by linarith
  have h2 : T^2 = lam^(-(2:ℝ)/13) := by
    simpa only [Nat.cast_ofNat] using thirteenth_root_nat_pow hlam 2
  have h3 : T^3 = lam^(-(3:ℝ)/13) := by
    simpa only [Nat.cast_ofNat] using thirteenth_root_nat_pow hlam 3
  have h8 : T^8 = lam^(-(8:ℝ)/13) := by
    simpa only [Nat.cast_ofNat] using thirteenth_root_nat_pow hlam 8
  have hHM : (H:ℝ) ≤ T^2/2 := by rwa [h2]
  have hMM : T^8 ≤ (M:ℝ) := by rwa [h8]
  have hQ : (⌊lam^(-(3:ℝ)/13)⌋₊:ℝ) ≤ T^3 := by
    rw [h3]
    exact Nat.floor_le (by positivity)
  have hH2 : (H:ℝ)^2 ≤ T^4/4 := by
    have hs := mul_self_le_mul_self (Nat.cast_nonneg H) hHM
    nlinarith
  have h23 : T^2 ≤ T^3 := by
    nlinarith [mul_le_mul_of_nonneg_right hT1 (sq_nonneg T)]
  have h7 : T^7 ≤ (M:ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_right hT1 (show 0 ≤ T^7 by positivity)]
  have hE : 4*(H:ℝ)+6*(⌊lam^(-(3:ℝ)/13)⌋₊:ℝ) ≤ 8*T^3 := by linarith
  have hp := mul_le_mul hH2 hE
    (show 0 ≤ 4*(H:ℝ)+6*(⌊lam^(-(3:ℝ)/13)⌋₊:ℝ) by positivity)
    (show 0 ≤ T^4/4 by positivity)
  have hprod : (H:ℝ)^2*(4*(H:ℝ)+6*(⌊lam^(-(3:ℝ)/13)⌋₊:ℝ)) ≤ 2*(M:ℝ) := by
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 8*(M:ℝ) by positivity)
  nlinarith

end TaoTrudgianYang2025
