import GafniTao.HeathBrownAtkinsonLemma71Absorption

/-!
# Physical scales in Ivić equation (7.19)

This file removes the nested square roots from the two coefficients in the
summed form of equation (7.19).  Fourth and second powers are used so that the
identities are exact: no asymptotic notation or unrecorded absolute constant
is introduced.
-/

namespace GafniTao

noncomputable section

/-- The fourth power of the terminal quarter-scale is the literal physical
ratio `u / (K+1)`. -/
theorem heathBrownAtkinsonQuarterScale_pow_four
    {u : ℝ} {K : ℕ} (hu : 0 ≤ u) :
    heathBrownAtkinsonQuarterScale u K ^ (4 : ℕ) =
      u / ((K + 1 : ℕ) : ℝ) := by
  let x : ℝ := u / ((K + 1 : ℕ) : ℝ)
  have hx : 0 ≤ x := by
    dsimp only [x]
    positivity
  have houter : Real.sqrt (Real.sqrt x) ^ (2 : ℕ) = Real.sqrt x :=
    Real.sq_sqrt (Real.sqrt_nonneg x)
  have hinner : Real.sqrt x ^ (2 : ℕ) = x := Real.sq_sqrt hx
  unfold heathBrownAtkinsonQuarterScale
  change Real.sqrt (Real.sqrt x) ^ (4 : ℕ) = x
  calc
    Real.sqrt (Real.sqrt x) ^ (4 : ℕ) =
        (Real.sqrt (Real.sqrt x) ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
    _ = Real.sqrt x ^ (2 : ℕ) := by rw [houter]
    _ = x := hinner

/-- The first coefficient in the summed equation-(7.19) estimate has exact
fourth power `900^4 * 2*T*(K+1)`. -/
theorem heathBrownAtkinsonEquation719FirstCoefficient_pow_four
    {T : ℝ} {K : ℕ} (hT : 0 < T) :
    heathBrownAtkinsonEquation719FirstCoefficient T K ^ (4 : ℕ) =
      900 ^ (4 : ℕ) * (2 * T * ((K + 1 : ℕ) : ℝ)) := by
  have hq : 0 < heathBrownAtkinsonQuarterScale (T / 2) K :=
    heathBrownAtkinsonQuarterScale_pos (half_pos hT)
  have hq4 := heathBrownAtkinsonQuarterScale_pow_four
    (K := K) (show 0 ≤ T / 2 by positivity)
  have hsqrt : Real.sqrt T ^ (2 : ℕ) = T := Real.sq_sqrt hT.le
  have hsqrt4 : Real.sqrt T ^ (4 : ℕ) = T ^ (2 : ℕ) := by
    calc
      Real.sqrt T ^ (4 : ℕ) =
          (Real.sqrt T ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
      _ = T ^ (2 : ℕ) := by rw [hsqrt]
  unfold heathBrownAtkinsonEquation719FirstCoefficient
  rw [div_pow, mul_pow, hsqrt4, hq4]
  field_simp [hT.ne', hq.ne']

/-- The reciprocal-gap coefficient in equation (7.19) has exact square
`28^2*T*(K+1)`. -/
theorem heathBrownAtkinsonEquation719ReciprocalCoefficient_sq
    {T : ℝ} {K : ℕ} (hT : 0 ≤ T) :
    heathBrownAtkinsonEquation719ReciprocalCoefficient T K ^ (2 : ℕ) =
      28 ^ (2 : ℕ) * (T * ((K + 1 : ℕ) : ℝ)) := by
  have hrad : 0 ≤ T * ((K + 1 : ℕ) : ℝ) := by positivity
  unfold heathBrownAtkinsonEquation719ReciprocalCoefficient
  rw [mul_pow, Real.sq_sqrt hrad]


end

end GafniTao
