import Dubon2026.LocalLogTail

/-! # Continuity of the finite-height logarithmic mean, including abscissae containing zeros -/

namespace Dubon2026

open Filter MeasureTheory Set
open scoped Topology

theorem continuousAt_integral_vertical_log {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (σ b t : ℝ) (hbt : b ≤ t) :
    ContinuousAt (fun x : ℝ => ∫ y in Icc b t,
      Real.log ‖dirichletSum a N ((x : ℂ) + Complex.I * y)‖) σ := by
  obtain ⟨V, K, η, C, hV, _, hη, _, hb⟩ :=
    exists_local_integral_logTruncationError_bound hN ha σ b t hbt
  let G := fun x : ℝ => ∫ y in Icc b t,
    Real.log ‖dirichletSum a N ((x : ℂ) + Complex.I * y)‖
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hdecay : Tendsto (fun R : ℝ => (K : ℝ) * C * Real.exp (-R)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul ((K : ℝ) * C)
  obtain ⟨R, hR, hsmall⟩ := ((eventually_ge_atTop (0 : ℝ)).and
    ((tendsto_order.mp hdecay).2 (ε / 3) (by positivity))).exists
  let F := fun x : ℝ => ∫ y in Icc b t,
    Real.log (max ‖dirichletSum a N ((x : ℂ) + Complex.I * y)‖
      (η * Real.exp (-(K : ℝ) * R)))
  have hF : Continuous F := continuous_integral_truncated_vertical_log a N b t
    (mul_pos hη (Real.exp_pos _))
  have hσ := hb σ (mem_of_mem_nhds hV) R hR
  have hclose := Metric.tendsto_nhds.mp (hF.continuousAt (x := σ)) (ε / 3) (by positivity)
  filter_upwards [hV, hclose] with x hx hmid
  have hbound := hb x hx R hR
  have hmid' : |F x - F σ| < ε / 3 := by simpa only [Real.dist_eq] using hmid
  change |F x - G x| ≤ _ at hbound
  change |F σ - G σ| ≤ _ at hσ
  change dist (G x) (G σ) < ε
  rw [Real.dist_eq]
  calc
    _ ≤ |G x - F x| + |F x - G σ| := abs_sub_le _ _ _
    _ ≤ |G x - F x| + (|F x - F σ| + |F σ - G σ|) :=
      add_le_add le_rfl (abs_sub_le _ _ _)
    _ ≤ (K : ℝ) * C * Real.exp (-R) +
        (|F x - F σ| + (K : ℝ) * C * Real.exp (-R)) :=
      add_le_add (by simpa only [abs_sub_comm] using hbound) (add_le_add le_rfl hσ)
    _ < ε := by linarith

theorem continuous_integral_vertical_log {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (b t : ℝ) (hbt : b ≤ t) :
    Continuous (fun x : ℝ => ∫ y in b..t,
      Real.log ‖dirichletSum a N ((x : ℂ) + Complex.I * y)‖) := by
  simp only [intervalIntegral.integral_of_le hbt, ← integral_Icc_eq_integral_Ioc]
  exact continuous_iff_continuousAt.mpr fun σ => continuousAt_integral_vertical_log hN ha σ b t hbt

theorem continuous_verticalLogMean {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (T : ℝ) (hT : 0 ≤ T) :
    Continuous (fun x => verticalLogMean a N x T) :=
  (continuous_integral_vertical_log hN ha (-T) T (neg_le_self hT)).const_mul ((2 * T)⁻¹)

end Dubon2026
