import Tao2026.SmoothNumberSaddlePerronLimit

/-!
# The complementary smooth saddle Perron line

This module normalizes the complete finite Perron line by the saddle main
term, removes the already evaluated central Gaussian segment, and identifies
the remainder both with the two literal tail integrals and with its exact
infinite-height limit.  It isolates the remaining analytic estimate without
an implicit normalization or endpoint convention.
-/

open Filter Topology MeasureTheory Set
open scoped Interval

namespace Tao2026

noncomputable section

noncomputable def smoothSaddleNormalizedPerronLine
    (X y : ℕ) (T : ℝ) : ℂ :=
  ((smoothSaddleStandardDeviation X y : ℂ) /
      (Real.sqrt (2 * Real.pi) : ℂ)) *
    ∫ t in (-T)..T, smoothSaddlePerronLineIntegrand X y t

theorem smoothSaddlePerronNormalization_eq
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    (((((X : ℝ) ^ smoothSaddlePoint X y : ℝ) : ℂ) *
          (smoothDirichletSeries (y + 1) (smoothSaddlePoint X y) : ℂ) /
          (smoothSaddlePoint X y : ℂ)) *
        (1 / (2 * Real.pi) : ℂ)) /
        (smoothSaddleMainTerm X y : ℂ) =
      (smoothSaddleStandardDeviation X y : ℂ) /
        (Real.sqrt (2 * Real.pi) : ℂ) := by
  have hsigma := smoothSaddlePoint_pos hX hy
  have hphi := smoothSaddlePhiTwo_pos hy hsigma
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsqrtPi : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hsqrtPhi : 0 < Real.sqrt
      (smoothSaddlePhiTwo y (smoothSaddlePoint X y)) :=
    Real.sqrt_pos.2 hphi
  have hZ : smoothDirichletSeries (y + 1) (smoothSaddlePoint X y) =
      ∏ p ∈ (Finset.Icc 2 y).filter Nat.Prime,
        (1 - (p : ℝ) ^ (-smoothSaddlePoint X y))⁻¹ :=
    smoothDirichletSeries_source_eq_eulerProduct y hsigma
  have hphase : (X : ℝ) ^ smoothSaddlePoint X y *
        smoothDirichletSeries (y + 1) (smoothSaddlePoint X y) =
      Real.exp (smoothSaddlePhase X y (smoothSaddlePoint X y)) := by
    rw [hZ]
    exact rpow_mul_sourceEulerProduct_eq_exp_smoothSaddlePhase
      (show 1 ≤ X by omega) hsigma
  unfold smoothSaddleMainTerm smoothSaddleStandardDeviation
  rw [← Complex.ofReal_mul, hphase]
  rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi)]
  push_cast
  field_simp [hsigma.ne', hpi.ne', hsqrtPi.ne', hsqrtPhi.ne', Real.exp_ne_zero]
  norm_cast
  exact Real.sq_sqrt (by positivity)

theorem smoothSaddleNormalizedPerronLine_eq_tsum_div_mainTerm
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) (T : ℝ) :
    smoothSaddleNormalizedPerronLine X y T =
      (∑' n : Nat.smoothNumbers (y + 1),
        GafniTao.sharpPerronKernel (smoothSaddlePoint X y) T X n.1) /
          (smoothSaddleMainTerm X y : ℂ) := by
  rw [smoothSaddlePerronLine_eq_tsum_sharpPerronKernels hX hy T]
  unfold smoothSaddleNormalizedPerronLine
  rw [← smoothSaddlePerronNormalization_eq hX hy]
  ring

theorem tendsto_smoothSaddleNormalizedPerronLine_atTop
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    Tendsto (smoothSaddleNormalizedPerronLine X y) atTop
      (𝓝 (((psiNat X y : ℂ) - smoothPerronEndpointCorrection X y) /
        (smoothSaddleMainTerm X y : ℂ))) := by
  have h := (tendsto_tsum_smoothSharpPerronKernel_atTop (X := X) (y := y)
    (smoothSaddlePoint_pos hX hy) (show 1 ≤ X by omega)).div_const
      (smoothSaddleMainTerm X y : ℂ)
  apply h.congr'
  filter_upwards [] with T
  exact (smoothSaddleNormalizedPerronLine_eq_tsum_div_mainTerm hX hy T).symm

noncomputable def smoothSaddleComplementaryPerronLine
    (X y : ℕ) (T : ℝ) : ℂ :=
  smoothSaddleNormalizedPerronLine X y T -
    smoothSaddleCentralLaplaceContribution X y

theorem tendsto_smoothSaddleComplementaryPerronLine_atTop
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    Tendsto (smoothSaddleComplementaryPerronLine X y) atTop
      (𝓝 ((((psiNat X y : ℂ) - smoothPerronEndpointCorrection X y) /
          (smoothSaddleMainTerm X y : ℂ)) -
        smoothSaddleCentralLaplaceContribution X y)) := by
  exact (tendsto_smoothSaddleNormalizedPerronLine_atTop hX hy).sub_const _

theorem smoothSaddleComplementaryPerronLine_eq_tailIntegrals
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) (T : ℝ) :
    smoothSaddleComplementaryPerronLine X y T =
      ((smoothSaddleStandardDeviation X y : ℂ) /
          (Real.sqrt (2 * Real.pi) : ℂ)) *
        ((∫ t in (-T)..(-smoothSaddleCentralPerronHeight X y),
            smoothSaddlePerronLineIntegrand X y t) +
          ∫ t in (smoothSaddleCentralPerronHeight X y)..T,
            smoothSaddlePerronLineIntegrand X y t) := by
  let f := smoothSaddlePerronLineIntegrand X y
  let H := smoothSaddleCentralPerronHeight X y
  have hf : Continuous f := continuous_smoothSaddlePerronLineIntegrand hX hy
  have hleft : IntervalIntegrable f MeasureTheory.volume (-T) (-H) :=
    hf.intervalIntegrable _ _
  have hcenter : IntervalIntegrable f MeasureTheory.volume (-H) H :=
    hf.intervalIntegrable _ _
  have hthrough : IntervalIntegrable f MeasureTheory.volume (-T) H :=
    hf.intervalIntegrable _ _
  have hright : IntervalIntegrable f MeasureTheory.volume H T :=
    hf.intervalIntegrable _ _
  have hsplit : (∫ t in (-T)..T, f t) =
      (∫ t in (-T)..(-H), f t) + (∫ t in (-H)..H, f t) +
        ∫ t in H..T, f t := by
    calc
      (∫ t in (-T)..T, f t) =
          (∫ t in (-T)..H, f t) + ∫ t in H..T, f t :=
        (intervalIntegral.integral_add_adjacent_intervals hthrough hright).symm
      _ = ((∫ t in (-T)..(-H), f t) + ∫ t in (-H)..H, f t) +
          ∫ t in H..T, f t := by
        rw [intervalIntegral.integral_add_adjacent_intervals hleft hcenter]
  unfold smoothSaddleComplementaryPerronLine
    smoothSaddleNormalizedPerronLine
  rw [smoothSaddleCentralLaplaceContribution_eq_perronLine hX hy]
  change _ * (∫ t in (-T)..T, f t) - _ * (∫ t in (-H)..H, f t) = _
  rw [hsplit]
  ring

noncomputable def smoothSaddleInfiniteComplementaryPerronLine
    (X y : ℕ) : ℂ :=
  ((psiNat X y : ℂ) - smoothPerronEndpointCorrection X y) /
      (smoothSaddleMainTerm X y : ℂ) -
    smoothSaddleCentralLaplaceContribution X y

theorem tendsto_smoothSaddleComplementaryPerronLine_atTop_eq_infinite
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    Tendsto (smoothSaddleComplementaryPerronLine X y) atTop
      (𝓝 (smoothSaddleInfiniteComplementaryPerronLine X y)) := by
  simpa only [smoothSaddleInfiniteComplementaryPerronLine] using
    tendsto_smoothSaddleComplementaryPerronLine_atTop hX hy

theorem norm_smoothPerronEndpointCorrection_div_mainTerm_le
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    ‖smoothPerronEndpointCorrection X y /
        (smoothSaddleMainTerm X y : ℂ)‖ ≤
      (1 / 2 : ℝ) / smoothSaddleMainTerm X y := by
  have hm := smoothSaddleMainTerm_pos hX hy
  rw [norm_div]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm]
  exact div_le_div_of_nonneg_right
    (norm_smoothPerronEndpointCorrection_le_half X y) hm.le

theorem IsTaoCriticalSmoothRegime.tendsto_infiniteComplementaryPerronLine_zero_iff
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun n =>
      smoothSaddleInfiniteComplementaryPerronLine (X n) (y n))
        atTop (𝓝 0) ↔
      Tendsto (fun n =>
        (((psiNat (X n) (y n) : ℂ) -
            smoothPerronEndpointCorrection (X n) (y n)) /
          (smoothSaddleMainTerm (X n) (y n) : ℂ)))
        atTop (𝓝 1) := by
  have hcentral :=
    hregime.tendsto_smoothSaddleCentralLaplaceContribution_one hα
  constructor
  · intro htail
    have hsum := htail.add hcentral
    have heq : (fun n =>
        smoothSaddleInfiniteComplementaryPerronLine (X n) (y n) +
          smoothSaddleCentralLaplaceContribution (X n) (y n)) =
        (fun n =>
          (((psiNat (X n) (y n) : ℂ) -
              smoothPerronEndpointCorrection (X n) (y n)) /
            (smoothSaddleMainTerm (X n) (y n) : ℂ))) := by
      funext n
      unfold smoothSaddleInfiniteComplementaryPerronLine
      ring
    rw [heq] at hsum
    simpa only [zero_add] using hsum
  · intro hratio
    have hdiff := hratio.sub hcentral
    simpa only [smoothSaddleInfiniteComplementaryPerronLine, sub_self]
      using hdiff

end

end Tao2026
