import GafniTao.Pintz2023ShellEnvelope

/-!
# Pintz (2023), equation (4.24): removal of the source perturbations

The detector argument uses two strictly positive auxiliary parameters.  This
file proves that its literal shell exponent tends to Pintz's displayed
coefficient and then spends half of the outer epsilon on each perturbation.
No continuity of a zero-density exponent is assumed.
-/

open Asymptotics Filter Topology

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- The two-variable exponent produced before Pintz sends the detector
epsilon and the strict scale reserve to zero. -/
noncomputable def pintz2023ShellEnvelopeMap
    (eta : ℝ) (k ell : ℕ) (p : ℝ × ℝ) : ℝ :=
  pintz2023ShellCoreExponent eta p.1 p.2 k ell

theorem continuousAt_pintz2023ShellEnvelopeMap
    {eta : ℝ} {k ell : ℕ} (hcell : PintzCell eta k ell) :
    ContinuousAt (pintz2023ShellEnvelopeMap eta k ell) (0, 0) := by
  have hkNe : pintzKDenominator eta 0 k ≠ 0 :=
    (pintzCell_k_base_denominator_pos hcell).ne'
  have hellNe : pintzEllDenominator eta 0 ell ≠ 0 :=
    (pintzCell_ell_base_denominator_pos hcell).ne'
  have hK : ContinuousAt (fun p : ℝ × ℝ =>
      1 / pintzKDenominator eta p.1 k) (0, 0) := by
    apply ContinuousAt.div continuousAt_const
      (show ContinuousAt (fun p : ℝ × ℝ =>
        pintzKDenominator eta p.1 k) (0, 0) by
          unfold pintzKDenominator
          fun_prop)
    simpa using hkNe
  have hEll : ContinuousAt (fun p : ℝ × ℝ =>
      1 / pintzEllDenominator eta p.1 ell) (0, 0) := by
    apply ContinuousAt.div continuousAt_const
      (show ContinuousAt (fun p : ℝ × ℝ =>
        pintzEllDenominator eta p.1 ell) (0, 0) by
          unfold pintzEllDenominator
          fun_prop)
    simpa using hellNe
  unfold pintz2023ShellEnvelopeMap pintz2023ShellCoreExponent
    pintz2023ShellBlockExponent pintz2023SquareBlockScale
    pintz2023CriticalScaleExponent pintz2023EllPowerWindowUpper
    pintz2023EllThreshold
  have hQ : ContinuousAt
      (fun p : ℝ × ℝ => 2 * eta + 2 * (p.1 / (100 * (k : ℝ))))
      (0, 0) := by fun_prop
  have hSquare : ContinuousAt
      (fun p : ℝ × ℝ => 2 * (p.1 / (10 * (ell : ℝ)) +
        1 / ((k : ℝ) *
          (1 - ((k : ℝ) - 1) * eta - 6 * (k : ℝ) * p.1)) + p.2))
      (0, 0) := by
    simpa only [pintzKDenominator] using
      ((by fun_prop : ContinuousAt
        (fun p : ℝ × ℝ => 2 * (p.1 / (10 * (ell : ℝ)) +
          1 / pintzKDenominator eta p.1 k + p.2)) (0, 0)))
  have hEllBranch : ContinuousAt
      (fun p : ℝ × ℝ =>
        3 / 2 * (1 / pintzEllDenominator eta p.1 ell) +
          p.1 / (20 * (ell : ℝ))) (0, 0) := by fun_prop
  exact (hQ.mul hSquare).max (hQ.mul hEllBranch)

theorem pintz2023ShellEnvelopeMap_zero
    {eta : ℝ} {k ell : ℕ} (hcell : PintzCell eta k ell) :
    pintz2023ShellEnvelopeMap eta k ell (0, 0) =
      eta * pintzTheoremOneCoefficient eta k ell := by
  have heta : 0 ≤ eta := (pintzCell_eta_pos hcell).le
  unfold pintz2023ShellEnvelopeMap pintz2023ShellCoreExponent
    pintz2023ShellBlockExponent pintz2023SquareBlockScale
    pintz2023CriticalScaleExponent pintz2023EllPowerWindowUpper
    pintz2023EllThreshold pintzTheoremOneCoefficient
    pintzEllDenominator
  rw [mul_max_of_nonneg _ _ heta]
  rw [max_comm]
  congr 1 <;> ring

/-- Both strict source perturbations may be chosen while losing less than an
arbitrary prescribed amount in the physical shell exponent. -/
theorem exists_pintz2023_power_margin_data_shell_budget
    {eta target : ℝ} {k ell : ℕ}
    (hcell : PintzCell eta k ell) (hetaUpper : eta < 1 / 24)
    (htarget : 0 < target) :
    ∃ small : ℝ, 0 < small ∧
      ∃ data : Pintz2023PowerMarginData eta small k ell,
        pintz2023ShellCoreExponent eta data.epsilon data.delta k ell <
          eta * pintzTheoremOneCoefficient eta k ell + target := by
  obtain ⟨radius, hradius, hclose⟩ := Metric.continuousAt_iff.mp
    (continuousAt_pintz2023ShellEnvelopeMap hcell) target htarget
  let small : ℝ := min (radius / 2) (target / 2)
  have hsmall : 0 < small := by dsimp only [small]; positivity
  let data := Classical.choice
    (exists_pintz2023_power_margin_data hcell hetaUpper hsmall)
  have hepsilon : data.epsilon < radius := by
    exact data.epsilon_lt_target.trans_le
      ((min_le_left (radius / 2) (target / 2)).trans (by linarith))
  have hdelta : data.delta < radius := by
    exact data.delta_lt_target.trans_le
      ((min_le_left (radius / 2) (target / 2)).trans (by linarith))
  have hdist : dist (data.epsilon, data.delta) (0, 0) < radius := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero, sub_zero,
      abs_of_pos data.epsilon_pos, abs_of_pos data.delta_pos, max_lt_iff]
    exact ⟨hepsilon, hdelta⟩
  have hvalue := hclose hdist
  rw [Real.dist_eq, pintz2023ShellEnvelopeMap_zero hcell] at hvalue
  refine ⟨small, hsmall, data, ?_⟩
  dsimp only [pintz2023ShellEnvelopeMap] at hvalue
  linarith [le_abs_self
    (pintz2023ShellCoreExponent eta data.epsilon data.delta k ell -
      eta * pintzTheoremOneCoefficient eta k ell)]

/-- If every positive perturbation of a central exponent is admissible, then
the central exponent itself is admissible under the epsilon-power convention.
This is epsilon splitting, not attainment of an exponent infimum. -/
theorem epsilonExponentBound_of_forall_add
    {f : ℝ → ℝ} {a : ℝ}
    (h : ∀ d : ℝ, 0 < d → EpsilonExponentBound f (a + d)) :
    EpsilonExponentBound f a := by
  unfold EpsilonExponentBound EpsilonPowerBound at h ⊢
  intro eps heps
  have H := h (eps / 2) (half_pos heps) (eps / 2) (half_pos heps)
  apply H.trans_eventuallyEq
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  rw [abs_of_nonneg (Real.rpow_nonneg hT.le _),
    abs_of_nonneg (Real.rpow_nonneg hT.le _),
    ← Real.rpow_add hT, ← Real.rpow_add hT]
  congr 1
  ring

/-- Pintz's exact equation-(4.24) exponent for one dyadic height shell. -/
theorem pintz2023_dyadicHeightShell_native
    {eta : ℝ} {k ell : ℕ}
    (hcell : PintzCell eta k ell) (hetaUpper : eta < 1 / 24) :
    EpsilonExponentBound
      (fun T => ((∑ rho ∈ pintz2023DyadicHeightShell eta T,
        zeroMultiplicity rho : ℕ) : ℝ))
      (eta * pintzTheoremOneCoefficient eta k ell) := by
  apply epsilonExponentBound_of_forall_add
  intro target htarget
  obtain ⟨small, hsmall, data, hbudget⟩ :=
    exists_pintz2023_power_margin_data_shell_budget hcell hetaUpper htarget
  exact (pintz2023_dyadicHeightShell_epsilonExponentBound hcell data).mono_exponent
    hbudget.le

#print axioms pintz2023ShellEnvelopeMap_zero
#print axioms exists_pintz2023_power_margin_data_shell_budget
#print axioms epsilonExponentBound_of_forall_add
#print axioms pintz2023_dyadicHeightShell_native

end

end GafniTao
