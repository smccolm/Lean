import GafniTao.HeathBrownAtkinsonCurvatureHeight

/-!
# Uniform dyadic curvature scales for the Atkinson phase

On the source range `0 < x <= u <= c <= 2u`, the height derivative of the
curvature has size `u^(-1/2) x^(-3/2)`.  This file first records exact
radical bounds; the constants remain literal so no asymptotic convention is
hidden.
-/

namespace GafniTao

noncomputable section

/-- Literal lower slope used in the dyadic curvature estimate. -/
def heathBrownAtkinsonSlopeLower (u x : ℝ) : ℝ :=
  Real.sqrt (2 * Real.pi * u / x)

/-- Literal upper slope used in the dyadic curvature estimate. -/
def heathBrownAtkinsonSlopeUpper (u x : ℝ) : ℝ :=
  Real.sqrt ((2 * Real.pi + Real.pi ^ (2 : ℕ)) * (2 * u) / x)

/-- Lower curvature-variation scale on a dyadic height box. -/
def heathBrownAtkinsonCurvatureDerivativeLower (u x : ℝ) : ℝ :=
  Real.pi /
    (2 * x ^ (2 : ℕ) * heathBrownAtkinsonSlopeUpper u x)

/-- Upper curvature-variation scale on a dyadic height box. -/
def heathBrownAtkinsonCurvatureDerivativeUpper (u x : ℝ) : ℝ :=
  Real.pi /
    (x ^ (2 : ℕ) * heathBrownAtkinsonSlopeLower u x)

/-- A uniform lower curvature scale for indices in `[A,B]`. -/
def heathBrownAtkinsonBoxCurvatureLower (u A B : ℝ) : ℝ :=
  Real.pi / (2 * B ^ (2 : ℕ) * heathBrownAtkinsonSlopeUpper u A)

/-- A uniform upper curvature scale for indices in `[A,B]`. -/
def heathBrownAtkinsonBoxCurvatureUpper (u A B : ℝ) : ℝ :=
  Real.pi / (A ^ (2 : ℕ) * heathBrownAtkinsonSlopeLower u B)

theorem heathBrownAtkinsonSlopeLower_pos
    {u x : ℝ} (hu : 0 < u) (hx : 0 < x) :
    0 < heathBrownAtkinsonSlopeLower u x := by
  unfold heathBrownAtkinsonSlopeLower
  exact Real.sqrt_pos.2 (div_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) hu) hx)

theorem heathBrownAtkinsonSlopeUpper_pos
    {u x : ℝ} (hu : 0 < u) (hx : 0 < x) :
    0 < heathBrownAtkinsonSlopeUpper u x := by
  unfold heathBrownAtkinsonSlopeUpper
  apply Real.sqrt_pos.2
  exact div_pos
    (mul_pos (add_pos (mul_pos (by norm_num) Real.pi_pos)
      (sq_pos_of_pos Real.pi_pos)) (mul_pos (by norm_num) hu)) hx

/-- Lower radical comparison on the source dyadic box. -/
theorem heathBrownAtkinsonSlopeLower_le
    {u c x : ℝ} (hx : 0 < x) (huc : u ≤ c) :
    heathBrownAtkinsonSlopeLower u x ≤
      heathBrownAtkinsonRealSlope c x := by
  unfold heathBrownAtkinsonSlopeLower heathBrownAtkinsonRealSlope
  apply Real.sqrt_le_sqrt
  have hmul := mul_le_mul_of_nonneg_left huc
    (mul_nonneg (show 0 ≤ (2 : ℝ) by norm_num) Real.pi_nonneg)
  have hdiv : 2 * Real.pi * u / x ≤ 2 * Real.pi * c / x :=
    div_le_div_of_nonneg_right hmul hx.le
  exact hdiv.trans (le_add_of_nonneg_right (sq_nonneg Real.pi))

/-- Upper radical comparison on the source dyadic box. -/
theorem heathBrownAtkinsonSlope_le_upper
    {u c x : ℝ} (hu : 0 < u) (hx : 0 < x) (hxu : x ≤ u)
    (hcu : c ≤ 2 * u) :
    heathBrownAtkinsonRealSlope c x ≤
      heathBrownAtkinsonSlopeUpper u x := by
  unfold heathBrownAtkinsonSlopeUpper heathBrownAtkinsonRealSlope
  apply Real.sqrt_le_sqrt
  have hc2 : 2 * c ≤ 2 * (2 * u) := by linarith
  have hxu' : Real.pi * x ≤ Real.pi * (2 * u) := by
    have : x ≤ 2 * u := hxu.trans (by linarith)
    exact mul_le_mul_of_nonneg_left this Real.pi_nonneg
  rw [le_div_iff₀ hx]
  field_simp [hx.ne']
  nlinarith

theorem heathBrownAtkinsonCurvatureDerivativeLower_pos
    {u x : ℝ} (hu : 0 < u) (hx : 0 < x) :
    0 < heathBrownAtkinsonCurvatureDerivativeLower u x := by
  unfold heathBrownAtkinsonCurvatureDerivativeLower
  exact div_pos Real.pi_pos
    (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hx))
      (heathBrownAtkinsonSlopeUpper_pos hu hx))

theorem heathBrownAtkinsonCurvatureDerivativeUpper_pos
    {u x : ℝ} (hu : 0 < u) (hx : 0 < x) :
    0 < heathBrownAtkinsonCurvatureDerivativeUpper u x := by
  unfold heathBrownAtkinsonCurvatureDerivativeUpper
  exact div_pos Real.pi_pos
    (mul_pos (sq_pos_of_pos hx)
      (heathBrownAtkinsonSlopeLower_pos hu hx))

theorem heathBrownAtkinsonSlopeUpper_anti
    {u A x : ℝ} (hu : 0 < u) (hA : 0 < A) (hAx : A ≤ x) :
    heathBrownAtkinsonSlopeUpper u x ≤
      heathBrownAtkinsonSlopeUpper u A := by
  unfold heathBrownAtkinsonSlopeUpper
  apply Real.sqrt_le_sqrt
  have hnum : 0 ≤ (2 * Real.pi + Real.pi ^ (2 : ℕ)) * (2 * u) := by
    positivity
  exact div_le_div_of_nonneg_left hnum hA hAx

theorem heathBrownAtkinsonSlopeLower_anti
    {u x B : ℝ} (hu : 0 < u) (hx : 0 < x) (hxB : x ≤ B) :
    heathBrownAtkinsonSlopeLower u B ≤
      heathBrownAtkinsonSlopeLower u x := by
  unfold heathBrownAtkinsonSlopeLower
  apply Real.sqrt_le_sqrt
  have hnum : 0 ≤ 2 * Real.pi * u := by positivity
  exact div_le_div_of_nonneg_left hnum hx hxB

/-- Uniformize the pointwise curvature bounds on a closed index box. -/
theorem heathBrownAtkinsonCurvatureDerivative_box_bounds
    {u A x B : ℝ} (hu : 0 < u) (hA : 0 < A) (hAx : A ≤ x)
    (hxB : x ≤ B) :
    heathBrownAtkinsonBoxCurvatureLower u A B ≤
        heathBrownAtkinsonCurvatureDerivativeLower u x ∧
      heathBrownAtkinsonCurvatureDerivativeUpper u x ≤
        heathBrownAtkinsonBoxCurvatureUpper u A B := by
  have hx : 0 < x := hA.trans_le hAx
  have hB : 0 < B := hx.trans_le hxB
  have hupperAnti := heathBrownAtkinsonSlopeUpper_anti hu hA hAx
  have hlowerAnti := heathBrownAtkinsonSlopeLower_anti hu hx hxB
  have hxSq : x ^ (2 : ℕ) ≤ B ^ (2 : ℕ) := by
    exact pow_le_pow_left₀ hx.le hxB 2
  have hASq : A ^ (2 : ℕ) ≤ x ^ (2 : ℕ) := by
    exact pow_le_pow_left₀ hA.le hAx 2
  constructor
  · unfold heathBrownAtkinsonBoxCurvatureLower
      heathBrownAtkinsonCurvatureDerivativeLower
    have hden :
        2 * x ^ (2 : ℕ) * heathBrownAtkinsonSlopeUpper u x ≤
          2 * B ^ (2 : ℕ) * heathBrownAtkinsonSlopeUpper u A := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hxSq (by norm_num)) hupperAnti
        (heathBrownAtkinsonSlopeUpper_pos hu hx).le
        (mul_nonneg (by norm_num) (sq_nonneg B))
    exact div_le_div_of_nonneg_left Real.pi_nonneg
      (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hx))
        (heathBrownAtkinsonSlopeUpper_pos hu hx)) hden
  · unfold heathBrownAtkinsonBoxCurvatureUpper
      heathBrownAtkinsonCurvatureDerivativeUpper
    have hden :
        A ^ (2 : ℕ) * heathBrownAtkinsonSlopeLower u B ≤
          x ^ (2 : ℕ) * heathBrownAtkinsonSlopeLower u x := by
      exact mul_le_mul hASq hlowerAnti
        (heathBrownAtkinsonSlopeLower_pos hu hB).le (sq_nonneg x)
    exact div_le_div_of_nonneg_left Real.pi_nonneg
      (mul_pos (sq_pos_of_pos hA)
        (heathBrownAtkinsonSlopeLower_pos hu hB)) hden

/-- Exact derivative squeezed between its literal dyadic lower and upper
scales. -/
theorem heathBrownAtkinsonCurvatureDerivative_bounds
    {u c x : ℝ} (hu : 0 < u) (hx : 0 < x) (hxu : x ≤ u)
    (huc : u ≤ c) (hcu : c ≤ 2 * u) :
    heathBrownAtkinsonCurvatureDerivativeLower u x ≤
        Real.pi / x ^ (2 : ℕ) *
          (Real.pi * c / x + Real.pi ^ (2 : ℕ)) /
          (heathBrownAtkinsonRealSlope c x) ^ (3 : ℕ) ∧
      Real.pi / x ^ (2 : ℕ) *
          (Real.pi * c / x + Real.pi ^ (2 : ℕ)) /
          (heathBrownAtkinsonRealSlope c x) ^ (3 : ℕ) ≤
        heathBrownAtkinsonCurvatureDerivativeUpper u x := by
  have hc : 0 < c := hu.trans_le huc
  have hspos := heathBrownAtkinsonRealSlope_pos hc hx
  have hslow := heathBrownAtkinsonSlopeLower_le hx huc
  have hsup := heathBrownAtkinsonSlope_le_upper hu hx hxu hcu
  have hsquare :
      (heathBrownAtkinsonRealSlope c x) ^ 2 =
        2 * Real.pi * c / x + Real.pi ^ (2 : ℕ) := by
    unfold heathBrownAtkinsonRealSlope
    rw [Real.sq_sqrt]
    positivity
  have hhalf :
      (heathBrownAtkinsonRealSlope c x) ^ 2 / 2 ≤
        Real.pi * c / x + Real.pi ^ (2 : ℕ) := by
    calc
      (heathBrownAtkinsonRealSlope c x) ^ 2 / 2 =
          Real.pi * c / x + Real.pi ^ (2 : ℕ) / 2 := by
        rw [hsquare]
        ring
      _ ≤ Real.pi * c / x + Real.pi ^ (2 : ℕ) := by
        linarith [sq_nonneg Real.pi]
  have hwhole :
      Real.pi * c / x + Real.pi ^ (2 : ℕ) ≤
        (heathBrownAtkinsonRealSlope c x) ^ 2 := by
    rw [hsquare]
    have hp := div_nonneg (mul_nonneg Real.pi_nonneg hc.le) hx.le
    calc
      Real.pi * c / x + Real.pi ^ (2 : ℕ) ≤
          Real.pi * c / x +
            (Real.pi * c / x + Real.pi ^ (2 : ℕ)) := by
        exact le_add_of_nonneg_left hp
      _ = 2 * Real.pi * c / x + Real.pi ^ (2 : ℕ) := by ring
  constructor
  · have hden :
        2 * x ^ (2 : ℕ) * heathBrownAtkinsonRealSlope c x ≤
          2 * x ^ (2 : ℕ) * heathBrownAtkinsonSlopeUpper u x := by
      exact mul_le_mul_of_nonneg_left hsup
        (mul_nonneg (by norm_num) (sq_nonneg x))
    have hrecip :
        Real.pi /
            (2 * x ^ (2 : ℕ) * heathBrownAtkinsonSlopeUpper u x) ≤
          Real.pi /
            (2 * x ^ (2 : ℕ) * heathBrownAtkinsonRealSlope c x) := by
      exact div_le_div_of_nonneg_left Real.pi_nonneg
        (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hx)) hspos) hden
    rw [heathBrownAtkinsonCurvatureDerivativeLower]
    refine hrecip.trans ?_
    have hmul := mul_le_mul_of_nonneg_left hhalf
      (div_nonneg Real.pi_nonneg (sq_nonneg x))
    have hpow : 0 < (heathBrownAtkinsonRealSlope c x) ^ (3 : ℕ) := by
      positivity
    calc
      Real.pi / (2 * x ^ (2 : ℕ) * heathBrownAtkinsonRealSlope c x) =
          (Real.pi / x ^ (2 : ℕ)) *
            ((heathBrownAtkinsonRealSlope c x) ^ 2 / 2) /
            (heathBrownAtkinsonRealSlope c x) ^ (3 : ℕ) := by
        field_simp [hx.ne', hspos.ne']
      _ ≤ (Real.pi / x ^ (2 : ℕ)) *
            (Real.pi * c / x + Real.pi ^ (2 : ℕ)) /
            (heathBrownAtkinsonRealSlope c x) ^ (3 : ℕ) := by
        exact div_le_div_of_nonneg_right hmul hpow.le
  · have hmul := mul_le_mul_of_nonneg_left hwhole
      (div_nonneg Real.pi_nonneg (sq_nonneg x))
    have hpow : 0 < (heathBrownAtkinsonRealSlope c x) ^ (3 : ℕ) := by
      positivity
    have hfirst :
        (Real.pi / x ^ (2 : ℕ)) *
            (Real.pi * c / x + Real.pi ^ (2 : ℕ)) /
            (heathBrownAtkinsonRealSlope c x) ^ (3 : ℕ) ≤
          Real.pi /
            (x ^ (2 : ℕ) * heathBrownAtkinsonRealSlope c x) := by
      calc
        (Real.pi / x ^ (2 : ℕ)) *
              (Real.pi * c / x + Real.pi ^ (2 : ℕ)) /
              (heathBrownAtkinsonRealSlope c x) ^ (3 : ℕ) ≤
            (Real.pi / x ^ (2 : ℕ)) *
              (heathBrownAtkinsonRealSlope c x) ^ 2 /
              (heathBrownAtkinsonRealSlope c x) ^ (3 : ℕ) := by
          exact div_le_div_of_nonneg_right hmul hpow.le
        _ = Real.pi /
              (x ^ (2 : ℕ) * heathBrownAtkinsonRealSlope c x) := by
          field_simp [hx.ne', hspos.ne']
    refine hfirst.trans ?_
    rw [heathBrownAtkinsonCurvatureDerivativeUpper]
    have hden :
        x ^ (2 : ℕ) * heathBrownAtkinsonSlopeLower u x ≤
          x ^ (2 : ℕ) * heathBrownAtkinsonRealSlope c x :=
      mul_le_mul_of_nonneg_left hslow (sq_nonneg x)
    exact div_le_div_of_nonneg_left Real.pi_nonneg
      (mul_pos (sq_pos_of_pos hx) (heathBrownAtkinsonSlopeLower_pos hu hx)) hden

/-- Quantitative phase-curvature comparison between two heights in one
dyadic box. -/
theorem heathBrownAtkinsonCurvatureDifference_bounds
    {t u x : ℝ} (hu : 0 < u) (htu : u < t) (hx : 0 < x)
    (hxu : x ≤ u) (htuUpper : t ≤ 2 * u) :
    heathBrownAtkinsonCurvatureDerivativeLower u x * (t - u) ≤
        -(heathBrownAtkinsonRealCurvature t x -
          heathBrownAtkinsonRealCurvature u x) ∧
      -(heathBrownAtkinsonRealCurvature t x -
          heathBrownAtkinsonRealCurvature u x) ≤
        heathBrownAtkinsonCurvatureDerivativeUpper u x * (t - u) := by
  obtain ⟨c, hc, heq⟩ :=
    exists_heathBrownAtkinsonCurvatureDifference_eq hu htu hx
  have hcBounds := heathBrownAtkinsonCurvatureDerivative_bounds hu hx hxu
    hc.1.le (hc.2.le.trans htuUpper)
  rw [heq]
  exact ⟨mul_le_mul_of_nonneg_right hcBounds.1 (sub_nonneg.mpr htu.le),
    mul_le_mul_of_nonneg_right hcBounds.2 (sub_nonneg.mpr htu.le)⟩


end

end GafniTao
