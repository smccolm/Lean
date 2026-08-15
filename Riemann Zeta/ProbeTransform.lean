import RiemannZeta.GuthMaynard.DFIEquation29

open Complex Set Filter Topology MeasureTheory
open scoped BigOperators ContDiff FourierTransform SchwartzMap Topology Interval
open Classical

namespace RiemannZeta.GuthMaynard

def probeBranchSign : DFIVoronoiDualBranch → ℂ
  | .minusTerm => -1
  | .plusTerm => 1

theorem probeMultiplierShift (q : ℕ) [NeZero q]
    (branch : DFIVoronoiDualBranch) (z : ℂ) (hz : z ≠ 1) :
    dfiEquation29Multiplier q branch (z - 1) =
      probeBranchSign branch *
        ((q : ℂ) / (2 * Real.pi : ℂ)) ^ 2 * (1 - z) ^ 2 *
          dfiEquation29Multiplier q branch z := by
  cases branch
  · simp only [dfiEquation29Multiplier, probeBranchSign]
    rw [dfiVoronoiMinusMultiplier_sub_one q z hz]
    ring
  · simp only [dfiEquation29Multiplier, probeBranchSign, one_mul]
    exact dfiVoronoiPlusMultiplier_sub_one q z hz

theorem probeIntegrandShift
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    {n : ℕ} (hn : 0 < n) (σ u : ℝ) (hσ : σ < 1) :
    dfiEquation29Integrand q branch g n
        (((σ - 1 : ℝ) : ℂ) + (u : ℂ) * I) =
      (probeBranchSign branch *
          ((q : ℂ) / (2 * Real.pi : ℂ)) ^ 2 / (n : ℂ)) *
        dfiEquation29Integrand q branch
          (dfiEquation29BesselShiftIterate 2 g) n
          ((σ : ℂ) + (u : ℂ) * I) := by
  let z : ℂ := (σ : ℂ) + (u : ℂ) * I
  have hz : z ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [z] at hre
    linarith
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hline : (((σ - 1 : ℝ) : ℂ) + (u : ℂ) * I) = z - 1 := by
    simp only [z]
    push_cast
    ring
  have hpow : (n : ℂ) ^ (-(1 - (z - 1))) =
      (n : ℂ)⁻¹ * (n : ℂ) ^ (-(1 - z)) := by
    rw [show -(1 - (z - 1)) = (-1 : ℂ) + (-(1 - z)) by ring]
    rw [Complex.cpow_add _ _ hnC, Complex.cpow_neg_one]
  have hmult := probeMultiplierShift q branch z hz
  have hmellin := hg.mellin_besselShiftIterate_line_eq_source 2 σ u
  rw [hline]
  unfold dfiEquation29Integrand
  rw [hpow, hmult]
  change _ = _ *
    ((n : ℂ) ^ (-(1 - z)) * dfiEquation29Multiplier q branch z *
      mellin (dfiEquation29BesselShiftIterate 2 g) z)
  rw [hmellin]
  simp only [pow_two]
  field_simp
  ring

theorem probeVerticalTranslateOne (f : ℂ → ℂ) (σ : ℝ) :
    VerticalIntegral' (fun z => f (z + 1)) (σ - 1) =
      VerticalIntegral' f σ := by
  unfold VerticalIntegral' VerticalIntegral
  congr 2
  apply MeasureTheory.integral_congr_ae
  filter_upwards with u
  congr 1
  push_cast
  ring

theorem probeTransformShift
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    {n : ℕ} (hn : 0 < n) (σ : ℝ) (hσ : σ < 1) :
    dfiEquation29TransformAt q branch g n (σ - 1) =
      (probeBranchSign branch *
          ((q : ℂ) / (2 * Real.pi : ℂ)) ^ 2 / (n : ℂ)) *
        dfiEquation29TransformAt q branch
          (dfiEquation29BesselShiftIterate 2 g) n σ := by
  let c : ℂ := probeBranchSign branch *
    ((q : ℂ) / (2 * Real.pi : ℂ)) ^ 2 / (n : ℂ)
  let F : ℂ → ℂ := dfiEquation29Integrand q branch
    (dfiEquation29BesselShiftIterate 2 g) n
  unfold dfiEquation29TransformAt
  calc
    VerticalIntegral' (dfiEquation29Integrand q branch g n) (σ - 1) =
        VerticalIntegral' (fun z => c * F (z + 1)) (σ - 1) := by
      apply verticalIntegral'_congr_line
      intro u
      dsimp [c, F]
      rw [probeIntegrandShift hg q branch hn σ u hσ]
      congr 2
      push_cast
      ring
    _ = c * VerticalIntegral' (fun z => F (z + 1)) (σ - 1) :=
      verticalIntegral'_const_mul_bridge c _ _
    _ = c * VerticalIntegral' F σ := by rw [probeVerticalTranslateOne]
    _ = _ := rfl

end RiemannZeta.GuthMaynard
