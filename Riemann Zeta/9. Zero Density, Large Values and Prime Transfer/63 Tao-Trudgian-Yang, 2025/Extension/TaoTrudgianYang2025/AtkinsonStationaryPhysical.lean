import TaoTrudgianYang2025.AtkinsonSignedStationaryMain

/-!
# Physical small-frequency consumers of finite stationary reduction

The saddle-window hypotheses are derived from physical height and frequency,
rather than supplied independently. Both signs of sqrt(n) are covered.
This is not yet the sharp Atkinson frequency range or a Fresnel evaluation.
-/

noncomputable section

open Complex

namespace TaoTrudgianYang2025

theorem atkinsonSaddleRoot_small_frequency {T b : ℝ} (hT : 0 < T)
    (hb : |b| ≤ Real.sqrt T / 100) :
    Real.sqrt T / 3 ≤ atkinsonSaddleRoot (T / (2 * Real.pi)) b ∧
      atkinsonSaddleRoot (T / (2 * Real.pi)) b ≤ Real.sqrt T / 2 := by
  let r := atkinsonSaddleRoot (T / (2 * Real.pi)) b
  let S := Real.sqrt T
  have hS : 0 < S := Real.sqrt_pos.2 hT
  have hSsq : S ^ 2 = T := Real.sq_sqrt hT.le
  have hr : 0 < r := atkinsonSaddleRoot_pos (by positivity) b
  have hrb : 0 < r - b := atkinsonSaddleRoot_sub_pos (by positivity) b
  have he : r ^ 2 - b * r = T / (2 * Real.pi) := atkinsonSaddleRoot_equation (by positivity) b
  have hAlo : T / 8 ≤ T / (2 * Real.pi) :=
    div_le_div_of_nonneg_left hT.le (by positivity) (by nlinarith [Real.pi_lt_four])
  have hAhi : T / (2 * Real.pi) ≤ T / 6 :=
    div_le_div_of_nonneg_left hT.le (by norm_num) (by nlinarith [Real.pi_gt_three])
  have hbSlo := mul_le_mul_of_nonneg_right (abs_le.mp hb).1 hS.le
  have hbShi := mul_le_mul_of_nonneg_right (abs_le.mp hb).2 hS.le
  change S / 3 ≤ r ∧ r ≤ S / 2
  constructor
  · by_contra hn
    have hprod : (S / 3 - r) * (S / 3 + r - b) > 0 :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  · by_contra hn
    have hprod : (r - S / 2) * (r + S / 2 - b) > 0 :=
      mul_pos (by linarith) (by linarith)
    nlinarith

theorem atkinsonSaddleRoot_small_frequency_window {T b H : ℝ} (hT : 0 < T)
    (hb : |b| ≤ Real.sqrt T / 100) (hH : H ≤ Real.sqrt T / 12) :
    Real.sqrt T / 4 ≤ atkinsonSaddleRoot (T / (2 * Real.pi)) b - H ∧
      atkinsonSaddleRoot (T / (2 * Real.pi)) b + H ≤ Real.sqrt T ∧
        H ≤ atkinsonSaddleRoot (T / (2 * Real.pi)) b / 2 := by
  obtain ⟨hlo, hhi⟩ := atkinsonSaddleRoot_small_frequency hT hb
  constructor
  · linarith
  constructor <;> nlinarith [Real.sqrt_nonneg T]

theorem sqrt_nat_small_frequency {T : ℝ} (hT : 0 < T) (n : ℕ)
    (hn : 10000 * (n : ℝ) ≤ T) : |Real.sqrt (n : ℝ)| ≤ Real.sqrt T / 100 := by
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  have hsq := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n)
  have hTsq := Real.sq_sqrt hT.le
  nlinarith [Real.sqrt_nonneg (n : ℝ), Real.sqrt_pos.2 hT]

theorem exists_atkinsonPowerIntegral_small_frequency_approximation (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L b H : ℝ, 0 < T → 1 ≤ G → G ^ 2 ≤ 2 * T →
      1 ≤ L → 8 * L ≤ G → 0 < H → H ≤ Real.sqrt T / 12 →
      |b| ≤ Real.sqrt T / 100 →
      ‖atkinsonPowerIntegral T G L α b - atkinsonFiniteStationaryMain T G L α b H‖ ≤
        C * G * T ^ (-α) * (4 / (H * Real.pi) + 4 * (G / Real.sqrt T) * H ^ 2 +
          432 * H ^ 4 / Real.sqrt T) := by
  obtain ⟨C, hC, hbound⟩ := exists_atkinsonPowerIntegral_finite_stationary_approximation α
  refine ⟨C, hC, ?_⟩
  intro T G L b H hT hG hGT hL hwidth hH hHT hb
  obtain ⟨hleft, hright, hwindow⟩ := atkinsonSaddleRoot_small_frequency_window hT hb hHT
  have h := hbound T G L b H hT hG hGT hL hwidth hH hleft hright hwindow
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have hr := atkinsonSaddleRoot_pos (by positivity : 0 < T / (2 * Real.pi)) b
  have hlo := (atkinsonSaddleRoot_small_frequency hT hb).1
  have hrem : 16 * T * H ^ 4 / (atkinsonSaddleRoot (T / (2 * Real.pi)) b) ^ 3 ≤
      432 * H ^ 4 / Real.sqrt T := by
    calc
      _ ≤ 16 * T * H ^ 4 / (Real.sqrt T / 3) ^ 3 := by gcongr
      _ = _ := by
        rw [div_pow, show (Real.sqrt T) ^ 3 = (Real.sqrt T) ^ 2 * Real.sqrt T by ring,
          Real.sq_sqrt hT.le]
        field_simp
        ring
  exact h.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hrem) (by positivity))

theorem exists_atkinsonPowerIntegral_small_n_pair_approximation (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L H : ℝ, 0 < T → 1 ≤ G → G ^ 2 ≤ 2 * T →
      1 ≤ L → 8 * L ≤ G → 0 < H → H ≤ Real.sqrt T / 12 →
      ∀ n : ℕ, 10000 * (n : ℝ) ≤ T →
      ‖atkinsonPowerIntegral T G L α (Real.sqrt n) -
        atkinsonFiniteStationaryMain T G L α (Real.sqrt n) H‖ ≤
          C * G * T ^ (-α) * (4 / (H * Real.pi) + 4 * (G / Real.sqrt T) * H ^ 2 +
            432 * H ^ 4 / Real.sqrt T) ∧
      ‖atkinsonPowerIntegral T G L α (-Real.sqrt n) -
        atkinsonFiniteStationaryMain T G L α (-Real.sqrt n) H‖ ≤
          C * G * T ^ (-α) * (4 / (H * Real.pi) + 4 * (G / Real.sqrt T) * H ^ 2 +
            432 * H ^ 4 / Real.sqrt T) := by
  obtain ⟨C, hC, hbound⟩ := exists_atkinsonPowerIntegral_small_frequency_approximation α
  refine ⟨C, hC, ?_⟩
  intro T G L H hT hG hGT hL hwidth hH hHT n hn
  have hb := sqrt_nat_small_frequency hT n hn
  constructor
  · exact hbound T G L (Real.sqrt n) H hT hG hGT hL hwidth hH hHT hb
  · exact hbound T G L (-Real.sqrt n) H hT hG hGT hL hwidth hH hHT (by simpa only [abs_neg])

end TaoTrudgianYang2025
