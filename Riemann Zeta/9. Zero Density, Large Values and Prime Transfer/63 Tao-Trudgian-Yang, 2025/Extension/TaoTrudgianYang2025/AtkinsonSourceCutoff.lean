import TaoTrudgianYang2025.AtkinsonSourceBand

/-!
# One explicit source cutoff linked to the stationary range

The ceiling preserves the full sharp tail condition. Its size is derived
from the actual physical width, so every retained index lies in the
already proved small-frequency stationary range beyond one threshold.
-/

noncomputable section

open Complex Filter

namespace TaoTrudgianYang2025

def atkinsonSourceCutoff (T G L : ℝ) : ℕ := ⌈36 * T * (L / G) ^ 2⌉₊

theorem atkinsonSourceCutoff_lower (T G L : ℝ) :
    36 * T * (L / G) ^ 2 ≤ (atkinsonSourceCutoff T G L : ℝ) :=
  Nat.le_ceil _

theorem atkinsonSourceCutoff_pos {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) : 0 < atkinsonSourceCutoff T G L := by
  have h := (by positivity : 0 < 36 * T * (L / G) ^ 2).trans_le
    (atkinsonSourceCutoff_lower T G L)
  exact_mod_cast h

theorem atkinsonSourceCutoff_le_small {T G L : ℝ}
    (hT : 40000 ≤ T) (hG : 0 < G) (hL : 0 ≤ L) (hwidth : 1200 * L ≤ G) :
    10000 * (atkinsonSourceCutoff T G L : ℝ) ≤ T := by
  have hT0 : 0 < T := by linarith
  have hratio : L / G ≤ 1 / 1200 := (div_le_iff₀ hG).2 (by linarith)
  have hband : 36 * T * (L / G) ^ 2 ≤ T / 40000 := by
    calc
      _ ≤ 36 * T * (1 / 1200 : ℝ) ^ 2 := by gcongr
      _ = _ := by ring
  have hceil := Nat.ceil_lt_add_one (by positivity : 0 ≤ 36 * T * (L / G) ^ 2)
  change (atkinsonSourceCutoff T G L : ℝ) < 36 * T * (L / G) ^ 2 + 1 at hceil
  linarith

theorem atkinsonStationaryMain_pair_eq_zero_after_cutoff {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8 * L ≤ G)
    (α : ℝ) (n : ℕ) (hn : atkinsonSourceCutoff T G L ≤ n) :
    atkinsonStationaryMain T G L α (Real.sqrt n) = 0 ∧
      atkinsonStationaryMain T G L α (-Real.sqrt n) = 0 := by
  apply atkinsonStationaryMain_pair_eq_zero_of_index hT hG hL hwidth α n
  have h : 36 * T * (L / G) ^ 2 ≤ (n : ℝ) :=
    (atkinsonSourceCutoff_lower T G L).trans (by exact_mod_cast hn)
  have hp : 0 < T * (L / G) ^ 2 := by positivity
  nlinarith

theorem eventually_atkinsonSourceCutoff_small {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in atTop, ∀ G : ℝ, T ^ δ ≤ G →
      10000 * (atkinsonSourceCutoff T G (Real.log T) : ℝ) ≤ T := by
  filter_upwards [eventually_const_log_pow_le_rpow 1200 (by norm_num) 1 hδ,
    eventually_ge_atTop (40000 : ℝ)] with T hlog hT
  intro G hG
  have hG0 : 0 < G := (Real.rpow_pos_of_pos (by linarith : 0 < T) δ).trans_le hG
  apply atkinsonSourceCutoff_le_small hT hG0 (Real.log_nonneg (by linarith))
  simpa only [pow_one] using hlog.trans hG

theorem exists_atkinsonSourceCutoff_carrier_approximation (α : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) →
      ∀ n : ℕ, n < atkinsonSourceCutoff T G (Real.log T) →
      ‖atkinsonPowerIntegral T G (Real.log T) α (Real.sqrt n) -
        atkinsonStationaryMain T G (Real.log T) α (Real.sqrt n)‖ ≤
          C * G * T ^ (-α) * T ^ (-min (δ / 3) (1 / 10)) ∧
      ‖atkinsonPowerIntegral T G (Real.log T) α (-Real.sqrt n) -
        atkinsonStationaryMain T G (Real.log T) α (-Real.sqrt n)‖ ≤
          C * G * T ^ (-α) * T ^ (-min (δ / 3) (1 / 10)) := by
  obtain ⟨C, hC, B, _, hbound⟩ := exists_atkinsonPowerIntegral_source_power_saving α hδ
  obtain ⟨D, hD⟩ := eventually_atTop.mp (eventually_atkinsonSourceCutoff_small hδ)
  refine ⟨C, hC, max 40000 (max B D), le_max_left _ _, ?_⟩
  intro T G hT hlower hupper n hn
  have hBT : B ≤ T := (le_max_left B D).trans ((le_max_right _ _).trans hT)
  have hDT : D ≤ T := (le_max_right B D).trans ((le_max_right _ _).trans hT)
  have hcut := hD T hDT G hlower
  apply hbound T G hBT hlower hupper n
  have hnR : (n : ℝ) ≤ atkinsonSourceCutoff T G (Real.log T) := by
    exact_mod_cast Nat.le_of_lt hn
  linarith

end TaoTrudgianYang2025
