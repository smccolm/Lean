import GafniTao.FordLemma36Equation314

/-! # Ford Lemma 3.6: lower recurrence used after (3.21) -/

namespace GafniTao

noncomputable section

theorem fordDeltaZero35_lower316
    {k : ℕ} {delta : ℝ} (hk : 1000 ≤ k)
    (hdeltaLower : (k : ℝ) < delta)
    (hdeltaUpper : delta ≤ ((k : ℝ) ^ 2 - k) / 2) :
    let r := fordR36 k delta
    fordDeltaZero35 k r delta ≥
      delta - 2 * k +
        4 * (k : ℝ) ^ 2 * r /
          (2 * (r : ℝ) * k + fordY35 k r delta) := by
  let r := fordR36 k delta
  let j := fordJ35 k r delta
  let Φ := fordCanonicalPhiSchedule k r j delta
  let star := fordPhiStar35 k r delta
  dsimp only
  have hk26 : 26 ≤ k := by omega
  have hrBounds := fordR36_bounds hk26 hdeltaLower.le hdeltaUpper
  have hr : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hy := fordY35_rounded_nonneg hk26 hdeltaLower.le hdeltaUpper
  have hj := fordJ35_admissible hrBounds.1 hy
  have hdelta : 2 * delta ≤ (k : ℝ) ^ 2 - k := by nlinarith
  have hphi : star ≤ Φ.phi 1 := by
    exact fordCanonicalPhiSchedule_phiStar_le
      (by omega) (by omega) hj.2 hdelta 1 (by omega) (by omega)
  have hfactor : 0 ≤ 2 * (r : ℝ) * k - fordY35 k r delta := by
    have hrOne : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
    unfold fordY35
    nlinarith [sq_nonneg ((k : ℝ) - r),
      mul_nonneg (show (0 : ℝ) ≤ r by positivity) (sub_nonneg.mpr hrOne)]
  have hsource :
      fordDeltaZero35 k r delta =
        delta - k + Φ.phi 1 / 2 *
          (2 * (r : ℝ) * k - fordY35 k r delta) := by
    simpa [Φ, j] using fordDeltaZero35_source_identity k r delta
  have hstar :
      delta - k + star / 2 *
          (2 * (r : ℝ) * k - fordY35 k r delta) =
        delta - 2 * k +
          4 * (k : ℝ) ^ 2 * r /
            (2 * (r : ℝ) * k + fordY35 k r delta) := by
    let D : ℝ := 2 * (r : ℝ) * k + fordY35 k r delta
    have hD : 0 < D := by dsimp [D]; positivity
    change delta - k + ((2 * (k : ℝ)) / D) / 2 *
        (2 * (r : ℝ) * k - fordY35 k r delta) =
      delta - 2 * k + 4 * (k : ℝ) ^ 2 * r / D
    field_simp [ne_of_gt hD]
    ring
  rw [hsource, ← hstar]
  gcongr

theorem fordDeltaZero35_normalized_lower
    {k : ℕ} {delta : ℝ} (hk : 1000 ≤ k)
    (hdeltaLower : (k : ℝ) < delta)
    (hdeltaUpper : delta ≤ ((k : ℝ) ^ 2 - k) / 2) :
    let r := fordR36 k delta
    let d := delta / (k : ℝ) ^ 2
    fordDeltaZero35 k r delta / (k : ℝ) ^ 2 ≥
      d * (1 - 2 / (k : ℝ)) := by
  let r := fordR36 k delta
  let d := delta / (k : ℝ) ^ 2
  let D : ℝ := 2 * (r : ℝ) * k + fordY35 k r delta
  dsimp only
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hlow := fordDeltaZero35_lower316 hk hdeltaLower hdeltaUpper
  have hscaled := div_le_div_of_nonneg_right hlow (sq_nonneg (k : ℝ))
  have hratio : (1 - d) / (2 * (k : ℝ)) ≤ (r : ℝ) / D := by
    simpa [r, d, D] using (fordEquation317 hk hdeltaLower hdeltaUpper).1
  have hfour := mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 4)
  have hnorm :
      (delta - 2 * (k : ℝ) +
          4 * (k : ℝ) ^ 2 * fordR36 k delta /
            (2 * (fordR36 k delta : ℝ) * k +
              fordY35 k (fordR36 k delta) delta)) /
          (k : ℝ) ^ 2 =
        d - 2 / (k : ℝ) + 4 * ((r : ℝ) / D) := by
    dsimp [d, D, r]
    field_simp
  rw [hnorm] at hscaled
  calc
    d * (1 - 2 / (k : ℝ)) =
        d - 2 / (k : ℝ) + 4 * ((1 - d) / (2 * k)) := by
      field_simp
      ring
    _ ≤ d - 2 / (k : ℝ) + 4 * ((r : ℝ) / D) := by linarith
    _ ≤ fordDeltaZero35 k r delta / (k : ℝ) ^ 2 := hscaled

#print axioms fordDeltaZero35_lower316
#print axioms fordDeltaZero35_normalized_lower

end

end GafniTao
