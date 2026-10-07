import Dubon2026.LocalVerticalSublevel

/-! # Locally uniform truncation of the logarithm on each finite vertical segment -/

namespace Dubon2026

open Filter MeasureTheory Set
open scoped Topology

theorem continuous_integral_truncated_vertical_log (a : ℕ → ℂ) (N : ℕ) (b t : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    Continuous (fun x : ℝ => ∫ y in Icc b t,
      Real.log (max ‖dirichletSum a N ((x : ℂ) + Complex.I * y)‖ ε)) := by
  have hf : Continuous (dirichletSum a N) :=
    continuous_iff_continuousAt.mpr fun z => (analyticAt_dirichletSum a N z).continuousAt
  apply continuous_parametric_integral_of_continuous (s := Icc b t) (μ := volume) ?_ isCompact_Icc
  exact (truncatedLogNorm ε hε).continuous.comp (hf.comp (by fun_prop))

theorem exists_local_integral_logTruncationError_bound {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (σ b t : ℝ) (hbt : b ≤ t) :
    ∃ (V : Set ℝ) (K : ℕ) (η C : ℝ), V ∈ 𝓝 σ ∧ 0 < K ∧ 0 < η ∧ 0 < C ∧
      ∀ x ∈ V, ∀ R : ℝ, 0 ≤ R →
        |(∫ y in Icc b t,
            Real.log (max ‖dirichletSum a N ((x : ℂ) + Complex.I * y)‖
              (η * Real.exp (-(K : ℝ) * R)))) -
          (∫ y in Icc b t, Real.log ‖dirichletSum a N ((x : ℂ) + Complex.I * y)‖)| ≤
            (K : ℝ) * C * Real.exp (-R) := by
  obtain ⟨V, K, η, C, hV, hK, hη, hC, hb⟩ := exists_local_vertical_sublevel_bound hN ha σ b t
  refine ⟨V, K, η, C, hV, hK, hη, hC, ?_⟩
  intro x hx R hR
  let f := fun y : ℝ => dirichletSum a N ((x : ℂ) + Complex.I * y)
  have hc : Continuous f := continuous_vertical_dirichletSum a N x
  have hi : IntegrableOn (fun y => Real.log ‖f y‖) (Icc b t) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hbt).mp
      (intervalIntegrable_vertical_log a N x b t)
  have hn : ∀ᵐ y ∂volume.restrict (Icc b t), f y ≠ 0 :=
    ae_restrict_of_ae (vertical_dirichletSum_ne_zero_ae hN ha x)
  have hd := integral_logDeficit_le_of_sublevel hi hn hK hη hC.le (R := R) (by
    intro δ hδ hδ1
    rw [Measure.restrict_apply (isClosed_le hc.norm continuous_const).measurableSet]
    convert hb x hx δ hδ hδ1 using 1
    congr 1
    ext y
    exact and_comm) hR
  have hε : 0 < η * Real.exp (-(K : ℝ) * R) := mul_pos hη (Real.exp_pos _)
  have htint : IntegrableOn (fun y => Real.log (max ‖f y‖
      (η * Real.exp (-(K : ℝ) * R)))) (Icc b t) :=
    ((truncatedLogNorm _ hε).continuous.comp hc).continuousOn.integrableOn_compact isCompact_Icc
  have he : (∫ y in Icc b t, Real.log (max ‖f y‖ (η * Real.exp (-(K : ℝ) * R)))) -
      (∫ y in Icc b t, Real.log ‖f y‖) =
        (K : ℝ) * ∫ y in Icc b t, logDeficit K η R (f y) := by
    rw [← integral_sub htint hi, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hn] with y hy
    exact log_truncation_eq_mul_logDeficit hK hη R hy
  change |(∫ y in Icc b t, Real.log (max ‖f y‖ (η * Real.exp (-(K : ℝ) * R)))) -
      (∫ y in Icc b t, Real.log ‖f y‖)| ≤ _
  rw [he, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg K)
    (integral_nonneg fun y => le_max_left _ _))]
  nlinarith [mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg K)]

end Dubon2026
