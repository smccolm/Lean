import GafniTao.HeathBrownAtkinsonRealPhase

/-!
# Curvature of the real-index Atkinson phase

This file proves the exact second derivative in the summation variable and
the corresponding identity for a difference of two source phases.  These
are the differential identities immediately preceding the exponent-pair
estimate in Heath--Brown's argument.
-/

namespace GafniTao

noncomputable section

/-- The exact real-index slope of the Atkinson phase. -/
def heathBrownAtkinsonRealSlope (T x : ℝ) : ℝ :=
  Real.sqrt (2 * Real.pi * T / x + Real.pi ^ (2 : ℕ))

/-- The exact real-index curvature of the Atkinson phase. -/
def heathBrownAtkinsonRealCurvature (T x : ℝ) : ℝ :=
  -(Real.pi * T) /
    (x ^ (2 : ℕ) * heathBrownAtkinsonRealSlope T x)

theorem heathBrownAtkinsonRealSlope_pos
    {T x : ℝ} (hT : 0 < T) (hx : 0 < x) :
    0 < heathBrownAtkinsonRealSlope T x := by
  unfold heathBrownAtkinsonRealSlope
  apply Real.sqrt_pos.2
  positivity

/-- Exact derivative of the phase slope, hence the second derivative of
the equation-(11) phase. -/
theorem hasDerivAt_heathBrownAtkinsonRealSlope
    {T x : ℝ} (hT : 0 < T) (hx : 0 < x) :
    HasDerivAt (heathBrownAtkinsonRealSlope T)
      (heathBrownAtkinsonRealCurvature T x) x := by
  have hdiv : HasDerivAt (fun u : ℝ => 2 * Real.pi * T / u)
      (-(2 * Real.pi * T) / x ^ (2 : ℕ)) x := by
    convert (hasDerivAt_const x (2 * Real.pi * T)).div
      (hasDerivAt_id x) hx.ne' using 1
    simp only [id_eq]
    ring
  have hradicand : HasDerivAt
      (fun u : ℝ => 2 * Real.pi * T / u + Real.pi ^ (2 : ℕ))
      (-(2 * Real.pi * T) / x ^ (2 : ℕ)) x := by
    simpa only [add_zero] using hdiv.add
      (hasDerivAt_const x (Real.pi ^ (2 : ℕ)))
  have hpos : 0 < 2 * Real.pi * T / x + Real.pi ^ (2 : ℕ) := by
    positivity
  have hsqrt := hradicand.sqrt hpos.ne'
  unfold heathBrownAtkinsonRealSlope heathBrownAtkinsonRealCurvature
  convert hsqrt using 1
  simp only [heathBrownAtkinsonRealSlope]
  ring

/-- The literal source phase has the exact second derivative displayed by
`heathBrownAtkinsonRealCurvature`. -/
theorem hasDerivAt_deriv_heathBrownAtkinsonRealPhase
    {T x : ℝ} (hT : 0 < T) (hx : 0 < x) :
    HasDerivAt (fun u => deriv (heathBrownAtkinsonRealPhase T) u)
      (heathBrownAtkinsonRealCurvature T x) x := by
  have hev : (fun u => deriv (heathBrownAtkinsonRealPhase T) u) =ᶠ[nhds x]
      heathBrownAtkinsonRealSlope T := by
    filter_upwards [eventually_gt_nhds hx] with u hu
    rw [(hasDerivAt_heathBrownAtkinsonRealPhase hT hu).deriv]
    rfl
  exact (hasDerivAt_heathBrownAtkinsonRealSlope hT hx).congr_of_eventuallyEq
    hev

/-- Difference of two exact Atkinson phases, with the later height first. -/
def heathBrownAtkinsonPhaseDifference (t u x : ℝ) : ℝ :=
  heathBrownAtkinsonRealPhase t x - heathBrownAtkinsonRealPhase u x

/-- Exact first derivative of the phase difference. -/
theorem hasDerivAt_heathBrownAtkinsonPhaseDifference
    {t u x : ℝ} (ht : 0 < t) (hu : 0 < u) (hx : 0 < x) :
    HasDerivAt (heathBrownAtkinsonPhaseDifference t u)
      (heathBrownAtkinsonRealSlope t x -
        heathBrownAtkinsonRealSlope u x) x := by
  unfold heathBrownAtkinsonPhaseDifference heathBrownAtkinsonRealSlope
  exact (hasDerivAt_heathBrownAtkinsonRealPhase ht hx).sub
    (hasDerivAt_heathBrownAtkinsonRealPhase hu hx)

/-- Exact second derivative of the phase difference. -/
theorem hasDerivAt_heathBrownAtkinsonPhaseDifferenceSlope
    {t u x : ℝ} (ht : 0 < t) (hu : 0 < u) (hx : 0 < x) :
    HasDerivAt
      (fun y => heathBrownAtkinsonRealSlope t y -
        heathBrownAtkinsonRealSlope u y)
      (heathBrownAtkinsonRealCurvature t x -
        heathBrownAtkinsonRealCurvature u x) x :=
  (hasDerivAt_heathBrownAtkinsonRealSlope ht hx).sub
    (hasDerivAt_heathBrownAtkinsonRealSlope hu hx)

theorem heathBrownAtkinsonRealCurvature_neg
    {T x : ℝ} (hT : 0 < T) (hx : 0 < x) :
    heathBrownAtkinsonRealCurvature T x < 0 := by
  unfold heathBrownAtkinsonRealCurvature
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (mul_pos Real.pi_pos hT))
    (mul_pos (sq_pos_of_pos hx) (heathBrownAtkinsonRealSlope_pos hT hx))


end

end GafniTao
