import TaoTrudgianYang2025.SargosSixthBootstrapInputs

/-! Exact exponent algebra and the admissible bootstrap parameter. -/

noncomputable section

namespace TaoTrudgianYang2025

def sargosSixthExponentStep (β : ℝ) : ℝ := β/(1+β)

theorem sargosSixthExponentStep_nonneg {β : ℝ} (hβ : 0 ≤ β) :
    0 ≤ sargosSixthExponentStep β := by
  dsimp [sargosSixthExponentStep]
  positivity

theorem sargosSixthExponentStep_identity {β : ℝ} (hβ : 0 ≤ β) :
    (1-sargosSixthExponentStep β)*β = sargosSixthExponentStep β := by
  have hd : 0 < 1+β := by linarith only [hβ]
  dsimp [sargosSixthExponentStep]
  field_simp
  ring

theorem sargosSixthExponentStep_add_le {β η : ℝ} (hβ : 0 ≤ β) (hη : 0 ≤ η) :
    sargosSixthExponentStep (β+η) ≤ sargosSixthExponentStep β+η := by
  have h₁ : 0 < 1+β := by linarith only [hβ]
  have h₂ : 0 < 1+(β+η) := by linarith only [hβ,hη]
  have he : sargosSixthExponentStep (β+η)-sargosSixthExponentStep β =
      η/((1+β)*(1+(β+η))) := by
    dsimp [sargosSixthExponentStep]
    field_simp
    ring
  have hd : 1 ≤ (1+β)*(1+(β+η)) := by nlinarith only [hβ,hη,sq_nonneg β,mul_nonneg hβ hη]
  have hh : η/((1+β)*(1+(β+η))) ≤ η :=
    div_le_self hη hd
  linarith only [he,hh]

def sargosSixthBootstrapParameter (N β : ℝ) : ℝ :=
  (1/4)*N^(-sargosSixthExponentStep β)

theorem sargosSixthBootstrapParameter_bounds {N β : ℝ} (hN : 1 ≤ N) (hβ : 0 ≤ β) :
    0 < sargosSixthBootstrapParameter N β ∧ sargosSixthBootstrapParameter N β ≤ 1/4 := by
  have hNp : 0 < N := by linarith only [hN]
  have hq := sargosSixthExponentStep_nonneg hβ
  have hp := Real.rpow_le_one_of_one_le_of_nonpos hN (neg_nonpos.mpr hq)
  dsimp [sargosSixthBootstrapParameter]
  constructor
  · positivity
  · nlinarith only [hp]

theorem sargosSixthBootstrapParameter_inverse {N β : ℝ} (hN : 0 < N) :
    1/sargosSixthBootstrapParameter N β = 4*N^(sargosSixthExponentStep β) := by
  dsimp [sargosSixthBootstrapParameter]
  rw [Real.rpow_neg hN.le]
  field_simp

theorem sargosSixthBootstrapParameter_power {N β : ℝ} (hN : 0 < N) (hβ : 0 ≤ β) :
    (4*sargosSixthBootstrapParameter N β*N)^β = N^(sargosSixthExponentStep β) := by
  have he : 4*sargosSixthBootstrapParameter N β*N = N^(1-sargosSixthExponentStep β) := by
    dsimp [sargosSixthBootstrapParameter]
    rw [Real.rpow_sub hN]
    simp only [Real.rpow_one,Real.rpow_neg hN.le]
    ring
  rw [he,← Real.rpow_mul hN.le,sargosSixthExponentStep_identity hβ]

end TaoTrudgianYang2025
