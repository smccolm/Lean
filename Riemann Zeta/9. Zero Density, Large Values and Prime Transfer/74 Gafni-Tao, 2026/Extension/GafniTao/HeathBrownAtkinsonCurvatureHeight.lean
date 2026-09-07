import GafniTao.HeathBrownAtkinsonRealCurvature
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Height variation of Atkinson curvature

The phase-difference estimate compares the curvatures at two separated
heights.  Here the positive curvature magnitude is differentiated in the
height variable.  This is the exact source quantity; later scale bounds are
obtained from this formula.
-/

open Set

namespace GafniTao

noncomputable section

/-- Positive magnitude of the (negative) real-index curvature. -/
def heathBrownAtkinsonCurvatureMagnitude (T x : ℝ) : ℝ :=
  Real.pi * T /
    (x ^ (2 : ℕ) * heathBrownAtkinsonRealSlope T x)

theorem heathBrownAtkinsonCurvatureMagnitude_eq_neg
    (T x : ℝ) :
    heathBrownAtkinsonCurvatureMagnitude T x =
      -heathBrownAtkinsonRealCurvature T x := by
  unfold heathBrownAtkinsonCurvatureMagnitude
    heathBrownAtkinsonRealCurvature
  ring

theorem heathBrownAtkinsonCurvatureMagnitude_pos
    {T x : ℝ} (hT : 0 < T) (hx : 0 < x) :
    0 < heathBrownAtkinsonCurvatureMagnitude T x := by
  unfold heathBrownAtkinsonCurvatureMagnitude
  exact div_pos (mul_pos Real.pi_pos hT)
    (mul_pos (sq_pos_of_pos hx) (heathBrownAtkinsonRealSlope_pos hT hx))

/-- Height derivative of the exact real-index slope. -/
theorem hasDerivAt_heathBrownAtkinsonRealSlope_height
    {T x : ℝ} (hT : 0 < T) (hx : 0 < x) :
    HasDerivAt (fun u => heathBrownAtkinsonRealSlope u x)
      (Real.pi / (x * heathBrownAtkinsonRealSlope T x)) T := by
  have hlin : HasDerivAt
      (fun u : ℝ => 2 * Real.pi * u / x + Real.pi ^ (2 : ℕ))
      (2 * Real.pi / x) T := by
    convert ((hasDerivAt_id T).const_mul (2 * Real.pi)).div_const x |>.add_const
      (Real.pi ^ (2 : ℕ)) using 1
    all_goals ring
  have hpos : 0 < 2 * Real.pi * T / x + Real.pi ^ (2 : ℕ) := by
    positivity
  have hsqrt := hlin.sqrt hpos.ne'
  unfold heathBrownAtkinsonRealSlope
  convert hsqrt using 1
  ring

/-- Exact height derivative of the positive curvature magnitude. -/
theorem hasDerivAt_heathBrownAtkinsonCurvatureMagnitude
    {T x : ℝ} (hT : 0 < T) (hx : 0 < x) :
    HasDerivAt (fun u => heathBrownAtkinsonCurvatureMagnitude u x)
      (Real.pi / x ^ (2 : ℕ) *
        (Real.pi * T / x + Real.pi ^ (2 : ℕ)) /
        (heathBrownAtkinsonRealSlope T x) ^ (3 : ℕ)) T := by
  have hs := hasDerivAt_heathBrownAtkinsonRealSlope_height hT hx
  have hden : HasDerivAt
      (fun u => x ^ (2 : ℕ) * heathBrownAtkinsonRealSlope u x)
      (x ^ (2 : ℕ) *
        (Real.pi / (x * heathBrownAtkinsonRealSlope T x))) T :=
    hs.const_mul (x ^ (2 : ℕ))
  have hdenpos : 0 <
      x ^ (2 : ℕ) * heathBrownAtkinsonRealSlope T x := by
    exact mul_pos (sq_pos_of_pos hx)
      (heathBrownAtkinsonRealSlope_pos hT hx)
  have hnum : HasDerivAt (fun u : ℝ => Real.pi * u) Real.pi T := by
    simpa only [mul_one] using (hasDerivAt_id T).const_mul Real.pi
  have hquot := hnum.div hden hdenpos.ne'
  unfold heathBrownAtkinsonCurvatureMagnitude
  convert hquot using 1
  have hspos := heathBrownAtkinsonRealSlope_pos hT hx
  have hsquare :
      (heathBrownAtkinsonRealSlope T x) ^ 2 =
        2 * Real.pi * T / x + Real.pi ^ (2 : ℕ) := by
    unfold heathBrownAtkinsonRealSlope
    rw [Real.sq_sqrt]
    positivity
  have hsquare_mul :
      x * (heathBrownAtkinsonRealSlope T x) ^ 2 =
        2 * Real.pi * T + Real.pi ^ (2 : ℕ) * x := by
    calc
      x * (heathBrownAtkinsonRealSlope T x) ^ 2 =
          x * (2 * Real.pi * T / x + Real.pi ^ (2 : ℕ)) := by
        rw [hsquare]
      _ = 2 * Real.pi * T + Real.pi ^ (2 : ℕ) * x := by
        field_simp [hx.ne']
  field_simp [hx.ne', hspos.ne']
  nlinarith [hsquare_mul]

theorem heathBrownAtkinsonCurvatureMagnitude_deriv_pos
    {T x : ℝ} (hT : 0 < T) (hx : 0 < x) :
    0 < Real.pi / x ^ (2 : ℕ) *
        (Real.pi * T / x + Real.pi ^ (2 : ℕ)) /
        (heathBrownAtkinsonRealSlope T x) ^ (3 : ℕ) := by
  exact div_pos
    (mul_pos
      (div_pos Real.pi_pos (sq_pos_of_pos hx))
      (add_pos (div_pos (mul_pos Real.pi_pos hT) hx)
        (sq_pos_of_pos Real.pi_pos)))
    (pow_pos (heathBrownAtkinsonRealSlope_pos hT hx) 3)

/-- The magnitude of the Atkinson curvature is strictly increasing with
height on the physical half-line. -/
theorem strictMonoOn_heathBrownAtkinsonCurvatureMagnitude (x : ℝ)
    (hx : 0 < x) :
    StrictMonoOn (fun T => heathBrownAtkinsonCurvatureMagnitude T x)
      (Set.Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro T hT
    exact (hasDerivAt_heathBrownAtkinsonCurvatureMagnitude hT hx).continuousAt.continuousWithinAt
  · intro T hT
    simp only [interior_Ioi, mem_Ioi] at hT
    rw [(hasDerivAt_heathBrownAtkinsonCurvatureMagnitude hT hx).deriv]
    exact heathBrownAtkinsonCurvatureMagnitude_deriv_pos hT hx

/-- Curvature difference has the source sign when the first height is the
larger one. -/
theorem heathBrownAtkinsonCurvatureDifference_neg
    {t u x : ℝ} (hu : 0 < u) (htu : u < t) (hx : 0 < x) :
    heathBrownAtkinsonRealCurvature t x -
        heathBrownAtkinsonRealCurvature u x < 0 := by
  have hmag := strictMonoOn_heathBrownAtkinsonCurvatureMagnitude x hx hu
    (hu.trans htu) htu
  have het := heathBrownAtkinsonCurvatureMagnitude_eq_neg t x
  have heu := heathBrownAtkinsonCurvatureMagnitude_eq_neg u x
  linarith

/-- Mean-value representation of the curvature difference in the height
variable. -/
theorem exists_heathBrownAtkinsonCurvatureDifference_eq
    {t u x : ℝ} (hu : 0 < u) (htu : u < t) (hx : 0 < x) :
    ∃ c ∈ Set.Ioo u t,
      -(heathBrownAtkinsonRealCurvature t x -
          heathBrownAtkinsonRealCurvature u x) =
        (Real.pi / x ^ (2 : ℕ) *
          (Real.pi * c / x + Real.pi ^ (2 : ℕ)) /
          (heathBrownAtkinsonRealSlope c x) ^ (3 : ℕ)) * (t - u) := by
  let F : ℝ → ℝ := fun v => heathBrownAtkinsonCurvatureMagnitude v x
  let F' : ℝ → ℝ := fun v =>
    Real.pi / x ^ (2 : ℕ) *
      (Real.pi * v / x + Real.pi ^ (2 : ℕ)) /
      (heathBrownAtkinsonRealSlope v x) ^ (3 : ℕ)
  have hcont : ContinuousOn F (Set.Icc u t) := by
    intro v hv
    exact (hasDerivAt_heathBrownAtkinsonCurvatureMagnitude
      (hu.trans_le hv.1) hx).continuousAt.continuousWithinAt
  have hderiv : ∀ v ∈ Set.Ioo u t, HasDerivAt F (F' v) v := by
    intro v hv
    exact hasDerivAt_heathBrownAtkinsonCurvatureMagnitude
      (hu.trans hv.1) hx
  obtain ⟨c, hc, heq⟩ := exists_hasDerivAt_eq_slope F F' htu hcont hderiv
  refine ⟨c, hc, ?_⟩
  dsimp only [F, F'] at heq ⊢
  rw [heathBrownAtkinsonCurvatureMagnitude_eq_neg,
    heathBrownAtkinsonCurvatureMagnitude_eq_neg] at heq
  rw [heq]
  field_simp [sub_ne_zero.mpr htu.ne']
  ring


end

end GafniTao
