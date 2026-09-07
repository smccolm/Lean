import GafniTao.HeathBrownAtkinsonFirstDerivativeGram
import GafniTao.HeathBrownAtkinsonLambdaScale

/-!
# Physical scale of the first-derivative Atkinson Gram bound

The literal Kusmin--Landau majorant is reduced here to the reciprocal-gap
term in Ivić (7.19), with an explicit numerical constant and the harmless
terminal shift `K+1` retained.
-/

namespace GafniTao

noncomputable section

/-- Multiplying the normalized square root by its denominator recovers the
geometric-mean scale. -/
theorem mul_sqrt_div_eq_sqrt_mul
    {u A : ℝ} (hu : 0 ≤ u) (hA : 0 < A) :
    A * Real.sqrt (u / A) = Real.sqrt (u * A) := by
  have hdiv : 0 ≤ u / A := div_nonneg hu hA.le
  have hmul : 0 ≤ u * A := mul_nonneg hu hA.le
  have hleft : 0 ≤ A * Real.sqrt (u / A) := by positivity
  have hright : 0 ≤ Real.sqrt (u * A) := Real.sqrt_nonneg _
  have hsqLeft : (A * Real.sqrt (u / A)) ^ (2 : ℕ) = u * A := by
    rw [mul_pow, Real.sq_sqrt hdiv]
    field_simp [hA.ne']
  have hsqRight : (Real.sqrt (u * A)) ^ (2 : ℕ) = u * A :=
    Real.sq_sqrt hmul
  nlinarith

/-- The literal reciprocal-gap majorant is at most an explicit constant
times `sqrt(u*(K+1))/(t-u)`. -/
theorem heathBrownAtkinsonFirstDerivativeGramMajorant_le_physical
    {K : ℕ} {t u : ℝ} (hu : 0 < u) (htu : u < t) :
    heathBrownAtkinsonFirstDerivativeGramMajorant K t u ≤
      28 * Real.sqrt (u * (K + 1 : ℕ)) / (t - u) := by
  have hA : 0 < ((K + 1 : ℕ) : ℝ) := by positivity
  have hs := heathBrownAtkinsonSlopeUpper_le_seven_sqrt hu hA
  have hs' : heathBrownAtkinsonSlopeUpper u ((K : ℝ) + 1) ≤
      7 * Real.sqrt (u / ((K : ℝ) + 1)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hs
  have hsPos : 0 ≤ heathBrownAtkinsonSlopeUpper u ((K : ℝ) + 1) :=
    (heathBrownAtkinsonSlopeUpper_pos hu (by positivity)).le
  have hgap : 0 < t - u := sub_pos.mpr htu
  have hnat : (2 * K + 1 : ℕ) ≤ 2 * (K + 1) := by omega
  have hcast : ((2 * K + 1 : ℕ) : ℝ) ≤
      2 * ((K + 1 : ℕ) : ℝ) := by exact_mod_cast hnat
  have hsqrt : 0 ≤ Real.sqrt (u / ((K + 1 : ℕ) : ℝ)) :=
    Real.sqrt_nonneg _
  have hnum :
      2 * ((2 * K + 1 : ℕ) : ℝ) *
          heathBrownAtkinsonSlopeUpper u (K + 1) ≤
        28 * Real.sqrt (u * ((K + 1 : ℕ) : ℝ)) := by
    calc
      2 * ((2 * K + 1 : ℕ) : ℝ) *
          heathBrownAtkinsonSlopeUpper u (K + 1) ≤
          2 * (2 * ((K + 1 : ℕ) : ℝ)) *
            heathBrownAtkinsonSlopeUpper u (K + 1) := by
        gcongr
      _ ≤
          2 * (2 * ((K + 1 : ℕ) : ℝ)) *
            (7 * Real.sqrt (u / ((K + 1 : ℕ) : ℝ))) := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          mul_le_mul_of_nonneg_left hs'
            (by positivity : 0 ≤ 2 * (2 * ((K : ℝ) + 1)))
      _ = 28 * (((K + 1 : ℕ) : ℝ) *
          Real.sqrt (u / ((K + 1 : ℕ) : ℝ))) := by ring
      _ = 28 * Real.sqrt (u * ((K + 1 : ℕ) : ℝ)) := by
        rw [mul_sqrt_div_eq_sqrt_mul hu.le hA]
  unfold heathBrownAtkinsonFirstDerivativeGramMajorant
  exact div_le_div_of_nonneg_right hnum hgap.le

/-- Physical reciprocal-gap estimate in the small-frequency branch. -/
theorem norm_heathBrownAtkinsonGram_le_physical_firstDerivative_of_small
    {K : ℕ} {t u : ℝ}
    (hu : 0 < u) (htu : u < t) (hK : 0 < K)
    (hblock : (((2 * K + 2 : ℕ) : ℝ)) ≤ u)
    (htUpper : t ≤ 2 * u)
    (hsmall :
      heathBrownAtkinsonFirstDerivativeUpper u t (K + 1) (2 * K + 1) ≤
        Real.pi) :
    ‖heathBrownAtkinsonGram K t u‖ ≤
      28 * Real.sqrt (u * (K + 1 : ℕ)) / (t - u) :=
  (norm_heathBrownAtkinsonGram_le_firstDerivativeMajorant_of_small
    hu htu hK hblock htUpper hsmall).trans
      (heathBrownAtkinsonFirstDerivativeGramMajorant_le_physical hu htu)


end

end GafniTao
