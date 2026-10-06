import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Logarithmic exponents from positive multiplicative asymptotics -/

namespace Dubon2026

open Filter
open scoped Topology

theorem tendsto_log_scaled_ratio {f g : ℕ → ℝ} {c β : ℝ}
    (hc : 0 < c) (hg : ∀ᶠ N in atTop, 0 < g N)
    (hr : Tendsto (fun N => f N / g N) atTop (𝓝 c))
    (hlogg : Tendsto (fun N => Real.log (g N) / Real.log N) atTop (𝓝 β)) :
    Tendsto (fun N => Real.log (f N) / Real.log N) atTop (𝓝 β) := by
  have hlogN : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have he : Tendsto (fun N => Real.log (f N / g N) / Real.log N) atTop (𝓝 0) :=
    ((Real.continuousAt_log hc.ne').tendsto.comp hr).div_atTop hlogN
  have hh := he.add hlogg
  simp only [zero_add] at hh
  apply hh.congr'
  filter_upwards [hg, hr.eventually (lt_mem_nhds hc)] with N hgN hrN
  have hfN : 0 < f N := (div_pos_iff.mp hrN).resolve_right (by rintro ⟨_, hh⟩; linarith) |>.1
  rw [Real.log_div hfN.ne' hgN.ne', sub_div, sub_add_cancel]

theorem tendsto_log_nat_div_log_ratio :
    Tendsto (fun N : ℕ => Real.log ((N : ℝ) / Real.log N) / Real.log N) atTop (𝓝 1) := by
  have hlogN : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have he : Tendsto (fun N : ℕ => Real.log (Real.log N) / Real.log N) atTop (𝓝 0) := by
    have h : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
      simpa only [pow_one, one_mul, add_zero] using
        Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    exact h.comp hlogN
  have hh : Tendsto (fun N : ℕ => 1 - Real.log (Real.log N) / Real.log N) atTop (𝓝 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub he
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  rw [Real.log_div (by positivity : (N : ℝ) ≠ 0) (Real.log_pos hNr).ne', sub_div,
    div_self (Real.log_pos hNr).ne']

end Dubon2026
