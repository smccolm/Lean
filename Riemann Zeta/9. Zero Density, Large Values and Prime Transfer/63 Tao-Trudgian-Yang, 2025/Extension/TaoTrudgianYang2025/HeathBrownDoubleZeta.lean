import TaoTrudgianYang2025.HeathBrownDoubleZetaFinite
import TaoTrudgianYang2025.EnergyLogLimits

/-!
# The actual fifth-coordinate Heath--Brown bound

This proves the frozen blueprint's `hb-double` conclusion from realizing
patterns and the native finite estimate. The physical scale and all logarithmic
exponents are linked. Height padding is removed on the whole source domain,
including `τ = 0`. No powered fifth-coordinate relation is asserted.
-/

open Filter Topology

noncomputable section

namespace TaoTrudgianYang2025

/-- The three terms of the double-zeta upper bound, before optimization. -/
def heathBrownDoubleZetaExponent (τ ρ : ℝ) : ℝ :=
  max (max (2 * ρ + 1) (ρ + 2)) (5 / 4 * ρ + 1 / 2 * τ + 1)

/-- Exact agreement with the displayed `hb-double` formula. -/
theorem heathBrownDoubleZetaExponent_eq_source (τ ρ : ℝ) :
    heathBrownDoubleZetaExponent τ ρ =
      max (max (ρ + 1) (2 * ρ)) (5 / 4 * ρ + τ / 2) + 1 := by
  unfold heathBrownDoubleZetaExponent
  rw [show ρ + 2 = (ρ + 1) + 1 by ring, max_add_add_right,
    show 1 / 2 * τ = τ / 2 by ring, max_add_add_right, max_comm (2 * ρ) (ρ + 1)]

/-- The harmless padded height is removed using the actual separation bound. -/
theorem heathBrownDoubleZetaExponent_max_one {τ ρ : ℝ} (hρ : ρ ≤ τ) :
    heathBrownDoubleZetaExponent (max 1 τ) ρ =
      heathBrownDoubleZetaExponent τ ρ := by
  by_cases hτ : τ ≤ 1
  · have hp : 5 / 4 * ρ + 1 / 2 * (1 : ℝ) + 1 ≤ max (2 * ρ + 1) (ρ + 2) := by
      have := le_max_right (2 * ρ + 1) (ρ + 2)
      linarith
    have ht : 5 / 4 * ρ + 1 / 2 * τ + 1 ≤ max (2 * ρ + 1) (ρ + 2) := by
      linarith
    simp only [heathBrownDoubleZetaExponent, max_eq_left hτ, max_eq_left hp, max_eq_left ht]
  · rw [max_eq_right (le_of_not_ge hτ)]

/-- Logarithmic limit of the genuine finite double-zeta estimate.
The input consists of actual patterns, not an assumed exponent inequality. -/
theorem heathBrown_doubleZeta_log_bound
    (P : ℕ → LargeValuePattern) {τ ρ s : ℝ}
    (hNtop : Tendsto (fun n => (P n).N) atTop atTop)
    (hRpos : ∀ n, 0 < ((P n).ordinates.card : ℝ))
    (hSpos : ∀ n, 0 < doubleZetaSum (P n))
    (hTlog : Tendsto (fun n => Real.logb (P n).N (P n).T) atTop (nhds τ))
    (hRlog : Tendsto (fun n => Real.logb (P n).N ((P n).ordinates.card : ℝ))
      atTop (nhds ρ))
    (hSlog : Tendsto (fun n => Real.logb (P n).N (doubleZetaSum (P n)))
      atTop (nhds s)) :
    s ≤ heathBrownDoubleZetaExponent (max 1 τ) ρ := by
  let N : ℕ → ℝ := fun n => (P n).N
  let H : ℕ → ℝ := fun n => max (N n) (P n).T
  let R : ℕ → ℝ := fun n => ((P n).ordinates.card : ℝ)
  have hN (n : ℕ) : 1 < N n := (P n).one_lt_N
  have hNpos (n : ℕ) : 0 < N n := zero_lt_one.trans (hN n)
  have hHpos (n : ℕ) : 0 < H n := (hNpos n).trans_le (le_max_left _ _)
  have hNlog : Tendsto (fun n => Real.logb (N n) (N n)) atTop (nhds 1) := by
    simpa only [Real.logb_self_eq_one (hN _)] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1))
  have hHlog := tendsto_logb_max hN hNpos (fun n => (P n).T_pos) hNlog hTlog
  have hHtop : Tendsto H atTop atTop :=
    tendsto_atTop_mono (fun n => le_max_left (N n) (P n).T) hNtop
  let A : ℕ → ℝ := fun n => R n ^ 2 * N n + R n * N n ^ 2 +
    R n ^ (5 / 4 : ℝ) * H n ^ (1 / 2 : ℝ) * N n
  have hApos (n : ℕ) : 0 < A n := by
    dsimp only [A, R]
    have := hRpos n
    have := hNpos n
    have := hHpos n
    positivity
  let a : ℝ := heathBrownDoubleZetaExponent (max 1 τ) ρ
  have hAlog : Tendsto (fun n => Real.logb (N n) (A n)) atTop (nhds a) := by
    apply tendsto_logb_add hN hNtop
      (fun n => by have := hRpos n; have := hNpos n; dsimp [R]; positivity)
      (fun n => by have := hRpos n; have := hNpos n; have := hHpos n; dsimp [R]; positivity)
    · apply tendsto_logb_add hN hNtop
        (fun n => by have := hRpos n; have := hNpos n; dsimp [R]; positivity)
        (fun n => by have := hRpos n; have := hNpos n; dsimp [R]; positivity)
      · exact tendsto_logb_mul (fun n => pow_pos (hRpos n) 2) hNpos
          (tendsto_logb_pow 2 hRlog) hNlog
      · convert tendsto_logb_mul hRpos (fun n => pow_pos (hNpos n) 2)
          hRlog (tendsto_logb_pow 2 hNlog) using 1
        norm_num
    · exact tendsto_logb_mul
        (fun n => by have := hRpos n; have := hHpos n; dsimp [R]; positivity) hNpos
        (tendsto_logb_mul (fun n => Real.rpow_pos_of_pos (hRpos n) _)
          (fun n => Real.rpow_pos_of_pos (hHpos n) _)
          (tendsto_logb_rpow (5 / 4) hRpos hRlog)
          (tendsto_logb_rpow (1 / 2) hHpos hHlog)) hNlog
  have hε (ε : ℝ) (hε : 0 < ε) : s ≤ ε * max 1 τ + a := by
    obtain ⟨C, H₀, hC, _, hbound⟩ := heathBrown_largeValuePattern_doubleZeta ε hε
    have hClog : Tendsto (fun n => Real.logb (N n) C) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp hNtop)
    have hboundlog := tendsto_logb_mul
      (fun n => mul_pos hC (Real.rpow_pos_of_pos (hHpos n) ε)) hApos
      (tendsto_logb_mul (fun _ => hC) (fun n => Real.rpow_pos_of_pos (hHpos n) ε)
        hClog (tendsto_logb_rpow ε hHpos hHlog)) hAlog
    simp only [zero_add] at hboundlog
    apply le_of_tendsto_of_tendsto hSlog hboundlog
    filter_upwards [hHtop.eventually_ge_atTop H₀] with n hn
    apply (Real.logb_le_logb (hN n) (hSpos n)
      (mul_pos (mul_pos hC (Real.rpow_pos_of_pos (hHpos n) ε)) (hApos n))).2
    exact hbound (P n) (H n) hn (le_max_right _ _)
  have hlim := (poweringAccuracy_tendsto.mul_const (max 1 τ)).add_const a
  simp only [zero_mul, zero_add] at hlim
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim
    (fun n => hε _ (poweringAccuracy_pos n))

/-- Full source `hb-double` on actual five-dimensional region points. -/
theorem InLargeValueEnergyRegion.heathBrown_doubleZeta
    {σ τ ρ e s : ℝ} (h : InLargeValueEnergyRegion σ τ ρ e s) :
    s ≤ max (max (ρ + 1) (2 * ρ)) (5 / 4 * ρ + τ / 2) + 1 := by
  classical
  have hex (n : ℕ) := h.2.2.2.2.2
    (poweringAccuracy n) (poweringAccuracy_pos n)
    (poweringAccuracy n) (poweringAccuracy_pos n) ((n : ℝ) + 2) (by positivity)
  let P : ℕ → LargeValuePattern := fun n => Classical.choose (hex n)
  have hP (n : ℕ) := Classical.choose_spec (hex n)
  change ∀ n : ℕ, (n : ℝ) + 2 ≤ (P n).N ∧ _ at hP
  have hNtop : Tendsto (fun n => (P n).N) atTop atTop := by
    apply tendsto_atTop_mono (fun n => (hP n).1)
    exact tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hcard (n : ℕ) : 0 < ((P n).ordinates.card : ℝ) :=
    (Real.rpow_pos_of_pos (zero_lt_one.trans (P n).one_lt_N) _).trans_le
      (hP n).2.2.2.2.2.1
  have hsum (n : ℕ) : 0 < doubleZetaSum (P n) :=
    (Real.rpow_pos_of_pos (zero_lt_one.trans (P n).one_lt_N) _).trans_le
      (hP n).2.2.2.2.2.2.2.2.2.1
  have ht := tendsto_logb_of_power_sandwich (fun n => (P n).N) (fun n => (P n).T)
    poweringAccuracy τ (fun n => (P n).one_lt_N) (fun n => (P n).T_pos)
    poweringAccuracy_tendsto (fun n => ⟨(hP n).2.1, (hP n).2.2.1⟩)
  have hr := tendsto_logb_of_power_sandwich (fun n => (P n).N)
    (fun n => ((P n).ordinates.card : ℝ)) poweringAccuracy ρ
    (fun n => (P n).one_lt_N) hcard poweringAccuracy_tendsto
    (fun n => ⟨(hP n).2.2.2.2.2.1, (hP n).2.2.2.2.2.2.1⟩)
  have hs := tendsto_logb_of_power_sandwich (fun n => (P n).N)
    (fun n => doubleZetaSum (P n)) poweringAccuracy s
    (fun n => (P n).one_lt_N) hsum poweringAccuracy_tendsto
    (fun n => ⟨(hP n).2.2.2.2.2.2.2.2.2.1, (hP n).2.2.2.2.2.2.2.2.2.2⟩)
  have hb := heathBrown_doubleZeta_log_bound P hNtop hcard hsum ht hr hs
  rwa [heathBrownDoubleZetaExponent_max_one h.rho_le_tau,
    heathBrownDoubleZetaExponent_eq_source] at hb

/-- The mixed term is a convex combination when the source height is at most 3/2. -/
theorem InLargeValueEnergyRegion.heathBrown_doubleZeta_small_height
    {σ τ ρ e s : ℝ} (h : InLargeValueEnergyRegion σ τ ρ e s)
    (hτ : τ ≤ 3 / 2) :
    s ≤ max (ρ + 2) (2 * ρ + 1) := by
  have hm : 5 / 4 * ρ + τ / 2 ≤ max (ρ + 1) (2 * ρ) := by
    have := le_max_left (ρ + 1) (2 * ρ)
    have := le_max_right (ρ + 1) (2 * ρ)
    linarith
  have hb := h.heathBrown_doubleZeta
  rw [max_eq_left hm] at hb
  convert hb using 1
  rw [← max_add_add_right]
  congr 1
  ring

/-- In the small-height, small-cardinality range the diagonal determines s exactly.
This is an unpowered equality, not the disproved fifth-coordinate scaling. -/
theorem InLargeValueEnergyRegion.heathBrown_doubleZeta_eq_diagonal
    {σ τ ρ e s : ℝ} (h : InLargeValueEnergyRegion σ τ ρ e s)
    (hτ : τ ≤ 3 / 2) (hρ : ρ ≤ 1) :
    s = ρ + 2 := by
  have hb := h.heathBrown_doubleZeta_small_height hτ
  rw [max_eq_left (show 2 * ρ + 1 ≤ ρ + 2 by linarith)] at hb
  exact le_antisymm hb h.rho_add_two_le_s

/-- The zeta-restricted region inherits the proved general double-zeta estimate. -/
theorem InZetaLargeValueEnergyRegion.heathBrown_doubleZeta
    {σ τ ρ e s : ℝ} (h : InZetaLargeValueEnergyRegion σ τ ρ e s) :
    s ≤ max (max (ρ + 1) (2 * ρ)) (5 / 4 * ρ + τ / 2) + 1 :=
  h.toGeneral.heathBrown_doubleZeta

end TaoTrudgianYang2025
