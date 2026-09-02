import GafniTao.FordLemma36Dyadic

/-!
# Ford Lemma 3.6: the sharp `phi*` and `theta_1` bounds

The decimal constants in the source are represented by exact rationals:
`0.16 = 4/25`, `0.071 = 71/1000`, and `0.32 = 8/25`.
-/

namespace GafniTao

noncomputable section

theorem fordRoundedDenominator36_lower
    {k : ℕ} {delta : ℝ} (hk : 1000 ≤ k)
    (hdeltaLower : (k : ℝ) < delta)
    (hdeltaUpper : delta ≤ ((k : ℝ) ^ 2 - k) / 2) :
    let d := delta / (k : ℝ) ^ 2
    (2 - d ^ 2) * (k : ℝ) ^ 2 - d * k ≤
      2 * (fordR36 k delta : ℝ) * k +
        fordY35 k (fordR36 k delta) delta := by
  let d := delta / (k : ℝ) ^ 2
  have hk26 : 26 ≤ k := by omega
  have hreal := (fordR36_real_bounds hk26 hdeltaUpper).1
  have hy := (fordY35_rounded_bounds hk26 hdeltaLower.le hdeltaUpper).1
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hd : d * (k : ℝ) = delta / k := by
    dsimp [d]
    field_simp
  calc
    (2 - d ^ 2) * (k : ℝ) ^ 2 - d * k =
        2 * ((k : ℝ) - d * k) * k +
          (d * k) * (2 * (k : ℝ) - d * k - 1) := by ring
    _ = 2 * ((k : ℝ) - delta / k) * k +
          (delta / k) * (2 * (k : ℝ) - delta / k - 1) := by rw [hd]
    _ ≤ 2 * (fordR36 k delta : ℝ) * k +
          fordY35 k (fordR36 k delta) delta := by
      gcongr

theorem fordRoundedDenominator36_numeric
    {k : ℕ} {delta : ℝ} (hk : 1000 ≤ k)
    (hdeltaLower : (k : ℝ) < delta)
    (hdeltaUpper : delta ≤ ((k : ℝ) ^ 2 - k) / 2) :
    let d := delta / (k : ℝ) ^ 2
    (7 * (k : ℝ) ^ 2 + 1) / 4 ≤
      (2 - d ^ 2) * (k : ℝ) ^ 2 - d * k := by
  let d := delta / (k : ℝ) ^ 2
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hdUpper : d ≤ ((k : ℝ) - 1) / (2 * k) := by
    dsimp [d]
    rw [div_le_iff₀ (sq_pos_of_pos hkR)]
    field_simp
    nlinarith
  have hdNonneg : 0 ≤ d := by
    have hdeltaNonneg : 0 ≤ delta := by
      have hkNonneg : (0 : ℝ) ≤ k := by positivity
      linarith
    dsimp [d]
    positivity
  have hk1000 : (1000 : ℝ) ≤ k := by exact_mod_cast hk
  have hlin : 0 ≤ ((k : ℝ) - 1) / (2 * k) - d := sub_nonneg.mpr hdUpper
  have hbase : 0 ≤ ((k : ℝ) - 1) / (2 * k) := by
    apply div_nonneg
    · linarith
    · positivity
  have hsum : 0 ≤ ((k : ℝ) - 1) / (2 * k) + d :=
    add_nonneg hbase hdNonneg
  have hsq : d ^ 2 ≤ (((k : ℝ) - 1) / (2 * k)) ^ 2 := by
    nlinarith [mul_nonneg hlin hsum]
  have hdecrease :
      (2 - (((k : ℝ) - 1) / (2 * k)) ^ 2) * (k : ℝ) ^ 2 -
          (((k : ℝ) - 1) / (2 * k)) * k ≤
        (2 - d ^ 2) * (k : ℝ) ^ 2 - d * k := by
    nlinarith
  calc
    (7 * (k : ℝ) ^ 2 + 1) / 4 =
        (2 - (((k : ℝ) - 1) / (2 * k)) ^ 2) * (k : ℝ) ^ 2 -
          (((k : ℝ) - 1) / (2 * k)) * k := by
            field_simp
            ring
    _ ≤ (2 - d ^ 2) * (k : ℝ) ^ 2 - d * k := hdecrease

theorem fordPhiStar35_rounded_upper_basic
    {k : ℕ} {delta : ℝ} (hk : 1000 ≤ k)
    (hdeltaLower : (k : ℝ) < delta)
    (hdeltaUpper : delta ≤ ((k : ℝ) ^ 2 - k) / 2) :
    fordPhiStar35 k (fordR36 k delta) delta ≤
      8 / (7 * (k : ℝ) + 1 / k) := by
  have hk26 : 26 ≤ k := by omega
  have hrNat := (fordR36_bounds hk26 hdeltaLower.le hdeltaUpper).1
  have hr : (0 : ℝ) < fordR36 k delta := by
    exact_mod_cast (show 0 < fordR36 k delta by omega)
  have hy := fordY35_rounded_nonneg hk26 hdeltaLower.le hdeltaUpper
  have hden :
      0 < 2 * (fordR36 k delta : ℝ) * k +
        fordY35 k (fordR36 k delta) delta := by positivity
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hsmall : 0 < 7 * (k : ℝ) + 1 / k := by positivity
  have hdenLower := fordRoundedDenominator36_lower hk hdeltaLower hdeltaUpper
  have hnumeric := fordRoundedDenominator36_numeric hk hdeltaLower hdeltaUpper
  have hquarter :
      (7 * (k : ℝ) ^ 2 + 1) / 4 ≤
        2 * (fordR36 k delta : ℝ) * k +
          fordY35 k (fordR36 k delta) delta :=
    hnumeric.trans hdenLower
  unfold fordPhiStar35
  rw [div_le_div_iff₀ hden hsmall]
  have heq : (k : ℝ) * (7 * k + 1 / k) = 7 * k ^ 2 + 1 := by
    field_simp
  nlinarith

theorem fordPhiStar35_numeric_sharpening {k : ℕ} (hk : 1000 ≤ k) :
    8 / (7 * (k : ℝ) + 1 / k) <
      8 / (7 * k) - (4 / 25 : ℝ) / k ^ 3 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hkSq : (0 : ℝ) < k ^ 2 := by positivity
  have hseven : (0 : ℝ) < 7 * k := by positivity
  have hden : (0 : ℝ) < 7 * k + 1 / k := by positivity
  rw [div_lt_iff₀ hden]
  field_simp
  ring_nf
  have hk1000 : (1000 : ℝ) ≤ k := by exact_mod_cast hk
  nlinarith

theorem fordPhiStar35_rounded_upper
    {k : ℕ} {delta : ℝ} (hk : 1000 ≤ k)
    (hdeltaLower : (k : ℝ) < delta)
    (hdeltaUpper : delta ≤ ((k : ℝ) ^ 2 - k) / 2) :
    fordPhiStar35 k (fordR36 k delta) delta <
      8 / (7 * (k : ℝ)) - (4 / 25 : ℝ) / k ^ 3 :=
  lt_of_le_of_lt
    (fordPhiStar35_rounded_upper_basic hk hdeltaLower hdeltaUpper)
    (fordPhiStar35_numeric_sharpening hk)

theorem fordCanonicalTheta_one_rounded
    {k : ℕ} {delta : ℝ} (hk : 1000 ≤ k)
    (hdeltaLower : (k : ℝ) < delta)
    (hdeltaUpper : delta ≤ ((k : ℝ) ^ 2 - k) / 2) :
    let r := fordR36 k delta
    let j := fordJ35 k r delta
    let Φ := fordCanonicalPhiSchedule k r j delta
    Φ.phi 1 - fordPhiStar35 k r delta ≤
      16 / (7 * (k : ℝ) ^ 2 * r) := by
  let r := fordR36 k delta
  let j := fordJ35 k r delta
  let Φ := fordCanonicalPhiSchedule k r j delta
  have hk26 : 26 ≤ k := by omega
  have hrBounds := fordR36_bounds hk26 hdeltaLower.le hdeltaUpper
  have hr : 1 ≤ r := by simpa [r] using (show 1 ≤ fordR36 k delta by omega)
  have hy := fordY35_rounded_nonneg hk26 hdeltaLower.le hdeltaUpper
  have hj := fordJ35_admissible hrBounds.1 hy
  have hdelta : 2 * delta ≤ (k : ℝ) ^ 2 - k := by nlinarith
  have htheta := fordCanonicalTheta_one_le
    (k := k) (r := r) (j := j) (delta := delta)
    (by omega) hr hj.1 hdelta hj.2
  have hdyadic := fordDyadicTerm36 hk hdeltaLower hdeltaUpper
  have hphi := fordPhiStar35_rounded_upper hk hdeltaLower hdeltaUpper
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hphiTerm :
      2 * fordPhiStar35 k r delta / ((k : ℝ) * r) <
        16 / (7 * (k : ℝ) ^ 2 * r) -
          (8 / 25 : ℝ) / ((k : ℝ) ^ 4 * r) := by
    have htemp := div_lt_div_of_pos_right
      (mul_lt_mul_of_pos_left hphi (by positivity : (0 : ℝ) < 2))
      (mul_pos hkR hrR)
    convert htemp using 1
    · field_simp
      ring
  dsimp [r, j, Φ] at htheta hdyadic hphiTerm ⊢
  have hsum := add_lt_add_of_le_of_lt hdyadic hphiTerm
  apply le_of_lt
  calc
    fordPhiBackwardAux k (fordR36 k delta)
          (fordJ35 k (fordR36 k delta) delta) delta
          (fordJ35 k (fordR36 k delta) delta - 1) -
        fordPhiStar35 k (fordR36 k delta) delta ≤
      1 / (fordR36 k delta : ℝ) /
          (2 : ℝ) ^ (fordJ35 k (fordR36 k delta) delta - 1) +
        2 * fordPhiStar35 k (fordR36 k delta) delta /
          ((k : ℝ) * fordR36 k delta) := htheta
    _ < 71 / 1000 / ((k : ℝ) ^ 4 * fordR36 k delta) +
        (16 / (7 * (k : ℝ) ^ 2 * fordR36 k delta) -
          8 / 25 / ((k : ℝ) ^ 4 * fordR36 k delta)) := hsum
    _ ≤ 16 / (7 * (k : ℝ) ^ 2 * fordR36 k delta) := by
      have hdenPos : 0 < (k : ℝ) ^ 4 * fordR36 k delta := by positivity
      have hc : (71 / 1000 : ℝ) ≤ 8 / 25 := by norm_num
      have hcdiv := div_le_div_of_nonneg_right hc hdenPos.le
      linarith

#print axioms fordPhiStar35_rounded_upper_basic
#print axioms fordPhiStar35_rounded_upper
#print axioms fordCanonicalTheta_one_rounded

end

end GafniTao
