import TaoTrudgianYang2025.SargosSixthPowerBootstrap

/-! Actual initial inputs to the sixth-moment iteration. -/

noncomputable section

namespace TaoTrudgianYang2025

theorem sargosSixthBaseMoment_cubic_bootstrap :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N : ℕ) (A : ℝ),
      16 ≤ N → 0 < A → A ≤ 1/4 →
      sargosSixthBaseMoment N ≤
        C*((1+Real.log N)^5/A+2*(Real.log N)^6*(4*A*N)^3) := by
  obtain ⟨C,hC,h⟩ := sargosSixthBaseMoment_power_bootstrap
  refine ⟨C,hC,?_⟩
  have hc := h 3 2 (by norm_num) (by norm_num) (by
    intro M hM
    simpa only [show (3:ℝ) = (3:ℕ) by norm_num,Real.rpow_natCast]
      using sargosSixthBaseMoment_trivial hM)
  intro N A hN hA hA₁
  simpa only [show (3:ℝ) = (3:ℕ) by norm_num,Real.rpow_natCast] using hc N A hN hA hA₁

theorem sargosSixthBaseMoment_sqrt_bound {N : ℕ} (hN : 4 ≤ N) :
    sargosSixthBaseMoment N ≤
      (1024*44845498368)*Real.sqrt N*(1+Real.log N)^5 := by
  have hNr : (4:ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0:ℝ) < N := by linarith only [hNr]
  have hs : 0 < Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr hNp
  have hs₂ : 2 ≤ Real.sqrt (N:ℝ) := by
    nlinarith only [Real.sq_sqrt hNp.le,Real.sqrt_nonneg (N:ℝ),hNr]
  have hA : 0 < 1/Real.sqrt (N:ℝ) := by positivity
  have hA₁ : 1/Real.sqrt (N:ℝ) ≤ 1/2 := by
    apply (div_le_iff₀ hs).2
    linarith only [hs₂]
  have hN₁ : 1 ≤ N := by omega
  calc
    _ ≤ (1024/(1/Real.sqrt (N:ℝ)))*sargosSixthInitialMoment N (1/Real.sqrt N) :=
      sargosSixthBaseMoment_localize hN₁ hA hA₁
    _ ≤ (1024/(1/Real.sqrt (N:ℝ)))*(44845498368*(1+Real.log N)^5) :=
      mul_le_mul_of_nonneg_left (sargosSixthInitialMoment_small hN₁) (by positivity)
    _ = _ := by field_simp

end TaoTrudgianYang2025
