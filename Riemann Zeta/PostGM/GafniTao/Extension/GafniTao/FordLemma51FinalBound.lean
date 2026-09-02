import GafniTao.FordCoreCoefficientBound

/-!
# A coefficient-free large-scale form of Ford's Lemma 5.1

The explicit polynomial coefficient is first retained, then absorbed once the
physical summation length exceeds an explicit (very conservative) threshold.
No asymptotic constant is hidden in this step.
-/

namespace GafniTao

noncomputable section

def fordCoefficientAbsorptionPower (k : ℕ) : ℕ :=
  24006400 * k ^ 2

def fordCoefficientAbsorptionThreshold (k : ℕ) : ℕ :=
  fordCoefficientBase k ^ fordCoefficientAbsorptionPower k

theorem ford_exponential_lemma_5_1_with_polynomial_coefficient
    {k N R : ℕ} {u t : ℝ}
    (hk : fordCoefficientKThreshold ≤ k) (hN : 1024 ≤ N)
    (hR : R ≤ 2 * N) (hu : 0 < u) (huOne : u ≤ 1) (ht : 0 < t)
    (hlower : (69 / 100 : ℝ) * k ≤ fordLambda N t)
    (hupper : fordLambda N t ≤ (7 / 10 : ℝ) * k) :
    ‖fordShiftedExponentialSum N R u t‖ ≤
      3 * (N : ℝ) ^ (3 / 10 : ℝ) +
        2 * (N : ℝ) * (fordCoefficientBase k : ℝ) ^ 11 *
          (N : ℝ) ^ (-(1 / ((1091200 : ℝ) * (k : ℝ) ^ 2))) := by
  have hsource := ford_exponential_lemma_5_1_quantitative
    (fordCoefficientKThreshold_ge_thousand.trans hk)
    hN hR hu huOne ht hlower hupper
  have hroot := fordScaledCoreCoefficient_root_le hk
  have hfactor : 0 ≤ 2 * (N : ℝ) := by positivity
  have htail : 0 ≤
      (N : ℝ) ^ (-(1 / ((1091200 : ℝ) * (k : ℝ) ^ 2))) := by positivity
  apply hsource.trans
  gcongr

theorem ford_coefficient_absorbed
    {k N : ℕ} (hk : fordCoefficientKThreshold ≤ k)
    (hN : fordCoefficientAbsorptionThreshold k ≤ N) :
    (fordCoefficientBase k : ℝ) ^ 11 ≤
      (N : ℝ) ^ (1 / ((2182400 : ℝ) * (k : ℝ) ^ 2)) := by
  let B : ℕ := fordCoefficientBase k
  let P : ℕ := fordCoefficientAbsorptionPower k
  let q : ℝ := 1 / ((2182400 : ℝ) * (k : ℝ) ^ 2)
  have hk1 : 1 ≤ k := by
    exact (show 1 ≤ fordCoefficientKThreshold by
      exact le_trans (by norm_num) fordCoefficientKThreshold_ge_thousand).trans hk
  have hB0 : (0 : ℝ) ≤ B := by positivity
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hcast : ((B ^ P : ℕ) : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hN
  have hmono := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (B ^ P : ℕ))
    hcast hq0
  have hPq : (P : ℝ) * q = 11 := by
    dsimp [P, q, fordCoefficientAbsorptionPower]
    have hk0 : (k : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  calc
    (fordCoefficientBase k : ℝ) ^ 11 = (B : ℝ) ^ (11 : ℝ) := by
      simp [B]
    _ = ((B : ℝ) ^ (P : ℝ)) ^ q := by
      rw [← Real.rpow_mul hB0, hPq]
    _ = ((B ^ P : ℕ) : ℝ) ^ q := by
      rw [Real.rpow_natCast]
      norm_num
    _ ≤ (N : ℝ) ^ q := hmono
    _ = (N : ℝ) ^ (1 / ((2182400 : ℝ) * (k : ℝ) ^ 2)) := rfl

theorem ford_half_decay_exponent_identity
    {k : ℕ} (hk : 1 ≤ k) :
    (1 / ((2182400 : ℝ) * (k : ℝ) ^ 2)) +
        (-(1 / ((1091200 : ℝ) * (k : ℝ) ^ 2))) =
      -(1 / ((2182400 : ℝ) * (k : ℝ) ^ 2)) := by
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem ford_boundary_exponent_le_half_decay
    {k : ℕ} (hk : 1 ≤ k) :
    (3 / 10 : ℝ) ≤
      1 - 1 / ((2182400 : ℝ) * (k : ℝ) ^ 2) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hdenPos : (0 : ℝ) < (2182400 : ℝ) * (k : ℝ) ^ 2 := by positivity
  have hq : 1 / ((2182400 : ℝ) * (k : ℝ) ^ 2) ≤ 7 / 10 := by
    rw [div_le_iff₀ hdenPos]
    nlinarith [sq_nonneg ((k : ℝ) - 1)]
  linarith

/-- Fully explicit large-scale exponential-sum estimate obtained from Ford's
Lemma 5.1. -/
theorem ford_exponential_lemma_5_1_large_scale
    {k N R : ℕ} {u t : ℝ}
    (hk : fordCoefficientKThreshold ≤ k) (hN : 1024 ≤ N)
    (hNlarge : fordCoefficientAbsorptionThreshold k ≤ N)
    (hR : R ≤ 2 * N) (hu : 0 < u) (huOne : u ≤ 1) (ht : 0 < t)
    (hlower : (69 / 100 : ℝ) * k ≤ fordLambda N t)
    (hupper : fordLambda N t ≤ (7 / 10 : ℝ) * k) :
    ‖fordShiftedExponentialSum N R u t‖ ≤
      5 * (N : ℝ) ^
        (1 - 1 / ((2182400 : ℝ) * (k : ℝ) ^ 2)) := by
  have hk1 : 1 ≤ k := by
    exact (show 1 ≤ fordCoefficientKThreshold by
      exact le_trans (by norm_num) fordCoefficientKThreshold_ge_thousand).trans hk
  have hsource := ford_exponential_lemma_5_1_with_polynomial_coefficient
    hk hN hR hu huOne ht hlower hupper
  have hcoeff := ford_coefficient_absorbed hk hNlarge
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans_le hNreal
  have htail0 : 0 ≤
      (N : ℝ) ^ (-(1 / ((1091200 : ℝ) * (k : ℝ) ^ 2))) := by positivity
  have hcentralCoeff :
      (fordCoefficientBase k : ℝ) ^ 11 *
          (N : ℝ) ^ (-(1 / ((1091200 : ℝ) * (k : ℝ) ^ 2))) ≤
        (N : ℝ) ^ (-(1 / ((2182400 : ℝ) * (k : ℝ) ^ 2))) := by
    calc
      _ ≤ (N : ℝ) ^ (1 / ((2182400 : ℝ) * (k : ℝ) ^ 2)) *
          (N : ℝ) ^ (-(1 / ((1091200 : ℝ) * (k : ℝ) ^ 2))) := by
        gcongr
      _ = (N : ℝ) ^
          ((1 / ((2182400 : ℝ) * (k : ℝ) ^ 2)) +
            (-(1 / ((1091200 : ℝ) * (k : ℝ) ^ 2)))) := by
        rw [Real.rpow_add hNpos]
      _ = (N : ℝ) ^ (-(1 / ((2182400 : ℝ) * (k : ℝ) ^ 2))) := by
        rw [ford_half_decay_exponent_identity hk1]
  have hboundaryPow :
      (N : ℝ) ^ (3 / 10 : ℝ) ≤
        (N : ℝ) ^ (1 - 1 / ((2182400 : ℝ) * (k : ℝ) ^ 2)) :=
    Real.rpow_le_rpow_of_exponent_le hNreal
      (ford_boundary_exponent_le_half_decay hk1)
  have hcentral :
      2 * (N : ℝ) * (fordCoefficientBase k : ℝ) ^ 11 *
          (N : ℝ) ^ (-(1 / ((1091200 : ℝ) * (k : ℝ) ^ 2))) ≤
        2 * (N : ℝ) ^
          (1 - 1 / ((2182400 : ℝ) * (k : ℝ) ^ 2)) := by
    have hmerge :
        (N : ℝ) * (N : ℝ) ^
            (-(1 / ((2182400 : ℝ) * (k : ℝ) ^ 2))) =
          (N : ℝ) ^
            (1 - 1 / ((2182400 : ℝ) * (k : ℝ) ^ 2)) := by
      calc
        (N : ℝ) * (N : ℝ) ^
            (-(1 / ((2182400 : ℝ) * (k : ℝ) ^ 2))) =
          (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^
            (-(1 / ((2182400 : ℝ) * (k : ℝ) ^ 2))) := by simp
        _ = (N : ℝ) ^
            ((1 : ℝ) + (-(1 / ((2182400 : ℝ) * (k : ℝ) ^ 2)))) := by
          rw [Real.rpow_add hNpos]
        _ = (N : ℝ) ^
            (1 - 1 / ((2182400 : ℝ) * (k : ℝ) ^ 2)) := by ring_nf
    calc
      _ ≤ 2 * (N : ℝ) *
          (N : ℝ) ^ (-(1 / ((2182400 : ℝ) * (k : ℝ) ^ 2))) := by
        have hleft : 0 ≤ 2 * (N : ℝ) := by positivity
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left hcentralCoeff hleft
      _ = 2 * ((N : ℝ) *
          (N : ℝ) ^ (-(1 / ((2182400 : ℝ) * (k : ℝ) ^ 2)))) := by ring
      _ = 2 * (N : ℝ) ^
          (1 - 1 / ((2182400 : ℝ) * (k : ℝ) ^ 2)) := by rw [hmerge]
  calc
    ‖fordShiftedExponentialSum N R u t‖ ≤
        3 * (N : ℝ) ^ (3 / 10 : ℝ) +
          2 * (N : ℝ) * (fordCoefficientBase k : ℝ) ^ 11 *
            (N : ℝ) ^ (-(1 / ((1091200 : ℝ) * (k : ℝ) ^ 2))) := hsource
    _ ≤ 3 * (N : ℝ) ^
          (1 - 1 / ((2182400 : ℝ) * (k : ℝ) ^ 2)) +
        2 * (N : ℝ) ^
          (1 - 1 / ((2182400 : ℝ) * (k : ℝ) ^ 2)) := by gcongr
    _ = 5 * (N : ℝ) ^
          (1 - 1 / ((2182400 : ℝ) * (k : ℝ) ^ 2)) := by ring

#print axioms ford_coefficient_absorbed
#print axioms ford_exponential_lemma_5_1_large_scale

end

end GafniTao
