import TaoTrudgianYang2025.SargosCProcessThresholds

/-! An actual integer differencing length, including the secondary-term constraint. -/

noncomputable section

namespace TaoTrudgianYang2025

theorem sargosCProcess_integer_choice {M : ℕ} {R T N η : ℝ}
    (hR : 2 ≤ R) (hRM : R ≤ (M:ℝ)) (hT : 0 < T)
    (hsmall : R^3/N^2 ≤ η) (hsecondary : 8*N^4 ≤ T*R^3) :
    ∃ H : ℕ, 1 ≤ H ∧ H ≤ M ∧ R/2 ≤ (H:ℝ) ∧ (H:ℝ) ≤ R ∧
      (H:ℝ)^3/N^2 ≤ η ∧ N^4 ≤ T*(H:ℝ)^3 := by
  let H : ℕ := ⌊R⌋₊
  have hH1 : 1 ≤ H := by
    have hp : 0 < H := Nat.floor_pos.mpr (by linarith)
    omega
  have hHM : H ≤ M := Nat.floor_le_of_le hRM
  have hup : (H:ℝ) ≤ R := Nat.floor_le (by linarith)
  have hfloor := Nat.lt_floor_add_one R
  have hlo : R/2 ≤ (H:ℝ) := by dsimp [H]; linarith
  have hHp : (0:ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  refine ⟨H,hH1,hHM,hlo,hup,?_,?_⟩
  · exact (div_le_div_of_nonneg_right
      (pow_le_pow_left₀ hHp.le hup 3) (sq_nonneg N)).trans hsmall
  · have htwice : R ≤ 2*(H:ℝ) := by linarith
    have hc := pow_le_pow_left₀ (show 0 ≤ R by linarith) htwice 3
    have hm := mul_le_mul_of_nonneg_left hc hT.le
    nlinarith only [hsecondary,hm]

theorem sargosCProcess_secondary_term_le {D T N H : ℝ}
    (hD : 0 < D) (hT : 0 < T) (hN : 0 < N) (hH : 0 < H)
    (hsecondary : N^4 ≤ T*H^3) :
    N^16/(D*T*H^4) ≤ (1/D)*(N^12/H) := by
  have hm := mul_le_mul_of_nonneg_left hsecondary (show 0 ≤ N^12 by positivity)
  calc
    _ ≤ (N^12*(T*H^3))/(D*T*H^4) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith only [hm]
    _ = _ := by field_simp

theorem sargosCProcess_first_term_le {N H R : ℝ}
    (hN : 0 < N) (hR : 0 < R) (hH : R/2 ≤ H) :
    N^12/H ≤ 2*(N^12/R) := by
  calc
    _ ≤ N^12/(R/2) := div_le_div_of_nonneg_left (by positivity) (by positivity) hH
    _ = _ := by ring

end TaoTrudgianYang2025
