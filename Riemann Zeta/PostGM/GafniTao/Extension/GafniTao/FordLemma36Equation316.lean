import GafniTao.FordLemma36PhiUpper

/-!
# Ford Lemma 3.6: equation (3.16)

This module assembles the exact updated exponent with the sharp `theta_1`
estimate.  The resulting theorem is Ford's displayed equation (3.16).
-/

namespace GafniTao

noncomputable section

theorem fordDeltaZero35_source_identity
    (k r : ℕ) (delta : ℝ) :
    let j := fordJ35 k r delta
    let Φ := fordCanonicalPhiSchedule k r j delta
    fordDeltaZero35 k r delta =
      delta - k + Φ.phi 1 / 2 *
        (2 * (r : ℝ) * k - fordY35 k r delta) := by
  dsimp only
  rw [fordDeltaZero35_eq]
  unfold fordDeltaPrime34 fordY35
  ring

theorem fordRoundedRemainder36
    {k : ℕ} {delta : ℝ} (hk : 1000 ≤ k)
    (hdeltaLower : (k : ℝ) < delta)
    (hdeltaUpper : delta ≤ ((k : ℝ) ^ 2 - k) / 2) :
    let r := fordR36 k delta
    let d := delta / (k : ℝ) ^ 2
    8 / (7 * (k : ℝ) ^ 2 * r) *
        (2 * (r : ℝ) * k - fordY35 k r delta) ≤
      16 * (1 - d) / (7 * k) := by
  let r := fordR36 k delta
  let a := delta / (k : ℝ)
  let d := delta / (k : ℝ) ^ 2
  dsimp only
  have hk26 : 26 ≤ k := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hrNat := (fordR36_bounds hk26 hdeltaLower.le hdeltaUpper).1
  have hr : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hrBounds := fordR36_real_bounds hk26 hdeltaUpper
  have haLower : 1 < a := by
    dsimp [a]
    apply (lt_div_iff₀ hkR).2
    simpa using hdeltaLower
  have haUpper : a ≤ ((k : ℝ) - 1) / 2 := by
    dsimp [a]
    apply (div_le_iff₀ hkR).2
    nlinarith
  have hka : 0 < (k : ℝ) - a := by
    have hk1000 : (1000 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hB :
      (k : ℝ) ^ 2 + k - 2 * delta ≤
        ((k : ℝ) - a) * ((k : ℝ) - a + 1) := by
    have haProd : 0 ≤ a * (a - 1) :=
      mul_nonneg (by linarith) (sub_nonneg.mpr haLower.le)
    have hadef : a * (k : ℝ) = delta := by
      dsimp [a]
      field_simp
    nlinarith
  have hBdiv :
      ((k : ℝ) ^ 2 + k - 2 * delta) / r ≤
        2 * ((k : ℝ) - a) - r + 1 := by
    have hrLower : (k : ℝ) - a ≤ r := by simpa [a, r] using hrBounds.1
    have hrUpper : (r : ℝ) ≤ (k : ℝ) - a + 1 := by
      simpa [a, r] using hrBounds.2
    have hbridge :
        ((k : ℝ) - a) * ((k : ℝ) - a + 1) ≤
          (r : ℝ) * (2 * ((k : ℝ) - a) - r + 1) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hrLower)
        (sub_nonneg.mpr hrUpper)]
    apply (div_le_iff₀ hr).2
    calc
      (k : ℝ) ^ 2 + k - 2 * delta ≤
          ((k : ℝ) - a) * ((k : ℝ) - a + 1) := hB
      _ ≤ (2 * ((k : ℝ) - a) - r + 1) * (r : ℝ) := by
        nlinarith [hbridge]
  have hquot :
      (2 * (r : ℝ) * k - fordY35 k r delta) / r ≤
        2 * ((k : ℝ) - a) := by
    have hid :
        (2 * (r : ℝ) * k - fordY35 k r delta) / r =
          (r : ℝ) - 1 + ((k : ℝ) ^ 2 + k - 2 * delta) / r := by
      unfold fordY35
      field_simp
      ring
    calc
      (2 * (r : ℝ) * k - fordY35 k r delta) / r =
          (r : ℝ) - 1 + ((k : ℝ) ^ 2 + k - 2 * delta) / r := hid
      _ ≤ ((r : ℝ) - 1) + (2 * ((k : ℝ) - a) - r + 1) :=
        by simpa [add_comm] using add_le_add_left hBdiv ((r : ℝ) - 1)
      _ = 2 * ((k : ℝ) - a) := by ring
  have hkd : (k : ℝ) - a = k * (1 - d) := by
    dsimp [a, d]
    field_simp
  have hcoef : 0 ≤ 8 / (7 * (k : ℝ) ^ 2) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hquot hcoef
  have hreassoc :
      8 / (7 * (k : ℝ) ^ 2 * r) *
          (2 * (r : ℝ) * k - fordY35 k r delta) =
        (8 / (7 * (k : ℝ) ^ 2)) *
          ((2 * (r : ℝ) * k - fordY35 k r delta) / r) := by
    field_simp
  rw [hreassoc]
  calc
    8 / (7 * (k : ℝ) ^ 2) *
          ((2 * (r : ℝ) * k - fordY35 k r delta) / r) ≤
        8 / (7 * (k : ℝ) ^ 2) * (2 * ((k : ℝ) - a)) := hmul
    _ = 16 * (1 - d) / (7 * k) := by
      rw [hkd]
      field_simp
      ring

theorem fordEquation316
    {k : ℕ} {delta : ℝ} (hk : 1000 ≤ k)
    (hdeltaLower : (k : ℝ) < delta)
    (hdeltaUpper : delta ≤ ((k : ℝ) ^ 2 - k) / 2) :
    let r := fordR36 k delta
    let d := delta / (k : ℝ) ^ 2
    fordDeltaZero35 k r delta ≤
      delta - 2 * k +
        4 * (k : ℝ) ^ 2 * r /
          (2 * (r : ℝ) * k + fordY35 k r delta) +
        16 * (1 - d) / (7 * k) := by
  let r := fordR36 k delta
  let j := fordJ35 k r delta
  let Φ := fordCanonicalPhiSchedule k r j delta
  let star := fordPhiStar35 k r delta
  let theta := Φ.phi 1 - star
  dsimp only
  have hk26 : 26 ≤ k := by omega
  have hrNat := (fordR36_bounds hk26 hdeltaLower.le hdeltaUpper).1
  have hr : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hy := fordY35_rounded_nonneg hk26 hdeltaLower.le hdeltaUpper
  have hden : 0 < 2 * (r : ℝ) * k + fordY35 k r delta := by positivity
  have hfactor : 0 ≤ 2 * (r : ℝ) * k - fordY35 k r delta := by
    have hdelta : 2 * delta ≤ (k : ℝ) ^ 2 - k := by nlinarith
    have hrOne : (1 : ℝ) ≤ r := by
      exact_mod_cast (show 1 ≤ r by omega)
    unfold fordY35
    nlinarith [sq_nonneg ((k : ℝ) - r),
      mul_nonneg (show (0 : ℝ) ≤ r by positivity)
        (sub_nonneg.mpr hrOne)]
  have htheta : theta ≤ 16 / (7 * (k : ℝ) ^ 2 * r) := by
    simpa [theta, star, Φ, j, r] using
      fordCanonicalTheta_one_rounded hk hdeltaLower hdeltaUpper
  have hsource := fordDeltaZero35_source_identity k r delta
  have hsource' :
      fordDeltaZero35 k r delta =
        delta - k + Φ.phi 1 / 2 *
          (2 * (r : ℝ) * k - fordY35 k r delta) := by
    simpa [Φ, j] using hsource
  have hstarIdentity :
      delta - k + star / 2 *
          (2 * (r : ℝ) * k - fordY35 k r delta) =
        delta - 2 * k +
          4 * (k : ℝ) ^ 2 * r /
            (2 * (r : ℝ) * k + fordY35 k r delta) := by
    let D : ℝ := 2 * (r : ℝ) * k + fordY35 k r delta
    have hD : D ≠ 0 := by
      dsimp [D]
      exact ne_of_gt hden
    change delta - k + ((2 * (k : ℝ)) / D) / 2 *
        (2 * (r : ℝ) * k - fordY35 k r delta) =
      delta - 2 * k + 4 * (k : ℝ) ^ 2 * r / D
    field_simp [hD]
    ring
  have hrem := fordRoundedRemainder36 hk hdeltaLower hdeltaUpper
  dsimp [r] at hrem ⊢
  calc
    fordDeltaZero35 k (fordR36 k delta) delta =
        delta - k +
          (star + theta) / 2 *
            (2 * (r : ℝ) * k - fordY35 k r delta) := by
      rw [hsource']
      dsimp [theta]
      ring
    _ = (delta - k + star / 2 *
          (2 * (r : ℝ) * k - fordY35 k r delta)) +
        theta / 2 * (2 * (r : ℝ) * k - fordY35 k r delta) := by ring
    _ ≤ (delta - k + star / 2 *
          (2 * (r : ℝ) * k - fordY35 k r delta)) +
        (16 / (7 * (k : ℝ) ^ 2 * r)) / 2 *
          (2 * (r : ℝ) * k - fordY35 k r delta) := by
      gcongr
    _ = delta - 2 * k +
          4 * (k : ℝ) ^ 2 * r /
            (2 * (r : ℝ) * k + fordY35 k r delta) +
        8 / (7 * (k : ℝ) ^ 2 * r) *
          (2 * (r : ℝ) * k - fordY35 k r delta) := by
      rw [hstarIdentity]
      ring
    _ ≤ delta - 2 * k +
          4 * (k : ℝ) ^ 2 * r /
            (2 * (r : ℝ) * k + fordY35 k r delta) +
        16 * (1 - delta / (k : ℝ) ^ 2) / (7 * k) := by
      gcongr

#print axioms fordRoundedRemainder36
#print axioms fordEquation316

end

end GafniTao
