import TaoTrudgianYang2025.ZetaReflectionPowerLossPattern
import TaoTrudgianYang2025.EnergyLogLimits

/-! Exact reflected physical-coordinate limits along actual pattern sequences. -/

noncomputable section
open Complex Filter MeasureTheory Set Topology
namespace TaoTrudgianYang2025

theorem tendsto_logb_self_of_one_lt (N : ℕ → ℝ) (hN : ∀ n, 1 < N n) :
    Tendsto (fun n => Real.logb (N n) (N n)) atTop (nhds 1) := by
  have he (n : ℕ) : Real.logb (N n) (N n) = 1 := by
    rw [Real.logb,div_self (Real.log_pos (hN n)).ne']
  simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1))

theorem tendsto_atTop_of_positive_logb_limit (N X : ℕ → ℝ) {a : ℝ}
    (hN : ∀ n, 1 < N n) (hX : ∀ n, 0 < X n) (ha : 0 < a)
    (hNtop : Tendsto N atTop atTop)
    (hlog : Tendsto (fun n => Real.logb (N n) (X n)) atTop (nhds a)) :
    Tendsto X atTop atTop := by
  have hl := (tendsto_order.mp hlog).1 (a/2) (by linarith)
  have hbound : ∀ᶠ n in atTop, (N n)^(a/2) ≤ X n :=
    hl.mono (fun n hn => (Real.le_logb_iff_rpow_le (hN n) (hX n)).mp hn.le)
  exact tendsto_atTop_mono' atTop hbound
    ((tendsto_rpow_atTop (show 0 < a/2 by linarith)).comp hNtop)

theorem reflection_tendsto_log_scale (P Q : ℕ → ZetaLargeValuePattern) {τ : ℝ}
    (hNtop : Tendsto (fun n => (P n).N) atTop atTop)
    (hTlog : Tendsto (fun n => Real.logb (P n).N (P n).T) atTop (nhds τ))
    (hscale : ∀ n, (P n).T/(4*Real.pi*(P n).N)/2 ≤ (Q n).N ∧
      (Q n).N ≤ 4*((P n).T/(4*Real.pi*(P n).N))) :
    Tendsto (fun n => Real.logb (P n).N (Q n).N) atTop (nhds (τ-1)) := by
  have hratio := tendsto_logb_div (fun n => (P n).T_pos)
    (fun n => zero_lt_one.trans (P n).one_lt_N) hTlog
    (tendsto_logb_self_of_one_lt (fun n => (P n).N) (fun n => (P n).one_lt_N))
  apply tendsto_logb_of_const_mul_sandwich (fun n => (P n).N)
    (fun n => (P n).T/(P n).N) (fun n => (Q n).N) (τ-1)
    (1/(8*Real.pi)) (1/Real.pi) (fun n => (P n).one_lt_N) hNtop
    (fun n => div_pos (P n).T_pos (zero_lt_one.trans (P n).one_lt_N))
    (by positivity) (by positivity) _ hratio
  intro n
  constructor
  · convert (hscale n).1 using 1
    ring
  · convert (hscale n).2 using 1
    ring

theorem reflection_tendsto_log_height (P Q : ℕ → ZetaLargeValuePattern) {τ : ℝ}
    (hNtop : Tendsto (fun n => (P n).N) atTop atTop)
    (hTlog : Tendsto (fun n => Real.logb (P n).N (P n).T) atTop (nhds τ))
    (hheight : ∀ n, (P n).T/2 ≤ (Q n).T ∧ (Q n).T ≤ 2*(P n).T) :
    Tendsto (fun n => Real.logb (P n).N (Q n).T) atTop (nhds τ) := by
  apply tendsto_logb_of_const_mul_sandwich (fun n => (P n).N)
    (fun n => (P n).T) (fun n => (Q n).T) τ (1/2) 2
    (fun n => (P n).one_lt_N) hNtop (fun n => (P n).T_pos)
    (by norm_num) (by norm_num) _ hTlog
  intro n
  simpa only [one_div,mul_comm,div_eq_mul_inv,one_mul] using hheight n

theorem reflection_tendsto_target_scale (P Q : ℕ → ZetaLargeValuePattern) {τ : ℝ}
    (hτ : 1 < τ) (hNtop : Tendsto (fun n => (P n).N) atTop atTop)
    (hTlog : Tendsto (fun n => Real.logb (P n).N (P n).T) atTop (nhds τ))
    (hscale : ∀ n, (P n).T/(4*Real.pi*(P n).N)/2 ≤ (Q n).N ∧
      (Q n).N ≤ 4*((P n).T/(4*Real.pi*(P n).N))) :
    Tendsto (fun n => (Q n).N) atTop atTop :=
  tendsto_atTop_of_positive_logb_limit _ _ (fun n => (P n).one_lt_N)
    (fun n => zero_lt_one.trans (Q n).one_lt_N) (sub_pos.mpr hτ) hNtop
    (reflection_tendsto_log_scale P Q hNtop hTlog hscale)

theorem reflection_tendsto_target_height_exponent (P Q : ℕ → ZetaLargeValuePattern) {τ : ℝ}
    (hτ : 1 < τ) (hNtop : Tendsto (fun n => (P n).N) atTop atTop)
    (hTlog : Tendsto (fun n => Real.logb (P n).N (P n).T) atTop (nhds τ))
    (hscale : ∀ n, (P n).T/(4*Real.pi*(P n).N)/2 ≤ (Q n).N ∧
      (Q n).N ≤ 4*((P n).T/(4*Real.pi*(P n).N)))
    (hheight : ∀ n, (P n).T/2 ≤ (Q n).T ∧ (Q n).T ≤ 2*(P n).T) :
    Tendsto (fun n => Real.logb (Q n).N (Q n).T) atTop (nhds (τ/(τ-1))) :=
  tendsto_logb_rebase _ _ _ τ (τ-1) (sub_pos.mpr hτ).ne'
    (fun n => (P n).one_lt_N)
    (reflection_tendsto_log_scale P Q hNtop hTlog hscale)
    (reflection_tendsto_log_height P Q hNtop hTlog hheight)

end TaoTrudgianYang2025
