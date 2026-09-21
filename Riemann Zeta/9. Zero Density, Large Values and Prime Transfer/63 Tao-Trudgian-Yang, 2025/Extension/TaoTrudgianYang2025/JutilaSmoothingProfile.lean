import TaoTrudgianYang2025.JutilaSmoothingErrors

/-!
# A uniform profile for Jutila's smoothing losses

The profile contains the actual bin count, smoothing height, prefix
logarithm and divisor loss. Its bound is uniform in the source pattern.
-/

open Filter RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

/-- The terminal cap grows at most quadratically under native smoothing. -/
theorem jutila_dual_cap_smoothing_le {θ T : ℝ}
    (hθ : 0 ≤ θ) (hθOne : θ ≤ 1) (hT : 1 ≤ T) :
    (jutilaDualLengthCap T (heathBrownSmoothingHeight T θ) : ℝ) ≤ 4*T^2 := by
  have hTp : 0 < T := by linarith
  have hH := heathBrownSmoothingHeight_le_two_rpow hT hθ
  have hp : T^θ ≤ T := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hT hθOne
  have hc := Nat.ceil_lt_add_one
    (show 0 ≤ T*(heathBrownSmoothingHeight T θ : ℝ) by positivity)
  unfold jutilaDualLengthCap
  push_cast
  have hm := mul_le_mul_of_nonneg_left (hH.trans (by linarith : 2*T^θ ≤ 2*T)) hTp.le
  nlinarith [sq_nonneg (T-1)]

/-- Prefix logarithms retain logarithmic height growth after smoothing. -/
theorem jutila_cap_log_smoothing_le {θ T : ℝ}
    (hθ : 0 ≤ θ) (hθOne : θ ≤ 1) (hT : 1 ≤ T) :
    (Nat.clog 2 (jutilaDualLengthCap T (heathBrownSmoothingHeight T θ)) : ℝ)+1 ≤
      2+(Real.log 4+2*Real.log T)/Real.log 2 := by
  let M := jutilaDualLengthCap T (heathBrownSmoothingHeight T θ)
  have hM : 1 ≤ M := by dsimp [M, jutilaDualLengthCap]; omega
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have hTp : 0 < T := by linarith
  have hc := heathBrown_natCast_clog_two_le_one_add_log M hM
  have hm := jutila_dual_cap_smoothing_le hθ hθOne hT
  have hlog : Real.log (M : ℝ) ≤ Real.log 4+2*Real.log T := by
    calc
      Real.log (M : ℝ) ≤ Real.log (4*T^2) := Real.log_le_log hMp hm
      _ = _ := by
        rw [Real.log_mul (by norm_num) (pow_ne_zero _ hTp.ne'), Real.log_pow]
        norm_num
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hd := div_le_div_of_nonneg_right hlog htwo.le
  dsimp [M] at hc hd
  linarith

/-- One positive profile controls every variable loss in the powered
reflection bound. This is a numerical expression, not a proof premise. -/
def jutilaSmoothingProfile (θ T : ℝ) : ℝ :=
  1 + ((Nat.log 2 (Nat.floor T)+1 : ℕ) : ℝ) +
    (heathBrownSmoothingHeight T θ : ℝ) +
    ((Nat.clog 2 (jutilaDualLengthCap T (heathBrownSmoothingHeight T θ)) : ℝ)+1) +
    (2*(jutilaDualLengthCap T (heathBrownSmoothingHeight T θ) : ℝ))^θ

theorem jutila_smoothing_profile_components (θ T : ℝ) :
    1 ≤ jutilaSmoothingProfile θ T ∧
    ((Nat.log 2 (Nat.floor T)+1 : ℕ) : ℝ) ≤ jutilaSmoothingProfile θ T ∧
    (heathBrownSmoothingHeight T θ : ℝ) ≤ jutilaSmoothingProfile θ T ∧
    ((Nat.clog 2 (jutilaDualLengthCap T (heathBrownSmoothingHeight T θ)) : ℝ)+1) ≤
      jutilaSmoothingProfile θ T ∧
    (2*(jutilaDualLengthCap T (heathBrownSmoothingHeight T θ) : ℝ))^θ ≤
      jutilaSmoothingProfile θ T := by
  unfold jutilaSmoothingProfile
  have ha : 0 ≤ ((Nat.log 2 (Nat.floor T)+1 : ℕ) : ℝ) := by positivity
  have hb : 0 ≤ (heathBrownSmoothingHeight T θ : ℝ) := by positivity
  have hc : 0 ≤ ((Nat.clog 2 (jutilaDualLengthCap T (heathBrownSmoothingHeight T θ)) : ℝ)+1) :=
    by positivity
  have hd : 0 ≤ (2*(jutilaDualLengthCap T (heathBrownSmoothingHeight T θ) : ℝ))^θ :=
    by positivity
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- The complete profile costs at most a constant times T^(2θ).
Both witnesses are chosen before the height and source pattern. -/
theorem jutila_smoothing_profile_uniform {θ : ℝ} (hθ : 0 < θ) (hθOne : θ ≤ 1) :
    ∃ B T₀ : ℝ, 0 < B ∧ 2 ≤ T₀ ∧
      ∀ T : ℝ, T₀ ≤ T → jutilaSmoothingProfile θ T ≤ B*T^(2*θ) := by
  obtain ⟨Tlog, hTlog⟩ := eventually_atTop.mp (heathBrown_eventually_log_le_rpow θ hθ)
  let B : ℝ := 6+(8 : ℝ)^θ+(Real.log 4+3)/Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B, max 2 Tlog, hB, le_max_left _ _, ?_⟩
  intro T hT
  have hT2 : 2 ≤ T := (le_max_left _ _).trans hT
  have hT1 : 1 ≤ T := by linarith
  have hTp : 0 < T := by linarith
  have hl := hTlog T ((le_max_right _ _).trans hT)
  have hone : 1 ≤ T^(2*θ) := Real.one_le_rpow hT1 (by positivity)
  have hp : T^θ ≤ T^(2*θ) := Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
  have hbin := heathBrown_displacement_bin_count_le_log hT2
  have hheight := heathBrownSmoothingHeight_le_two_rpow hT1 hθ.le
  have hclog := jutila_cap_log_smoothing_le hθ.le hθOne hT1
  have hcap := jutila_dual_cap_smoothing_le hθ.le hθOne hT1
  have hdivisor :
      (2*(jutilaDualLengthCap T (heathBrownSmoothingHeight T θ) : ℝ))^θ ≤
        (8 : ℝ)^θ*T^(2*θ) := by
    calc
      _ ≤ (8*T^2)^θ := Real.rpow_le_rpow (by positivity) (by linarith) hθ.le
      _ = _ := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8) (sq_nonneg T),
          ← Real.rpow_natCast_mul hTp.le]
        norm_num
  have hlogBudget :
      (Real.log 4+3*Real.log T)/Real.log 2 ≤
        ((Real.log 4+3)/Real.log 2)*T^(2*θ) := by
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hlog2]
    nlinarith [mul_le_mul_of_nonneg_left hone hlog4, hl.trans hp]
  unfold jutilaSmoothingProfile
  dsimp [B]
  have hLogs :
      Real.log T/Real.log 2+(Real.log 4+2*Real.log T)/Real.log 2 =
        (Real.log 4+3*Real.log T)/Real.log 2 := by ring
  nlinarith

end TaoTrudgianYang2025
