import GafniTao.FordLemma36Equation316

/-!
# Ford Lemma 3.6: equation (3.17)

The upper estimate is proved on the entire rounded interval, not merely at a
sampled value of `r`.  The exact concave interpolation remainder is
`U * t * (1-t)`.
-/

namespace GafniTao

noncomputable section

def fordRatioUpper36 (k : ℕ) (d : ℝ) : ℝ :=
  (1 - d) / ((2 - d ^ 2) * k) +
    d / ((2 - d ^ 2) ^ 2 * (k : ℝ) ^ 2)

theorem fordRatioUpper36_nonneg
    {k : ℕ} {d : ℝ} (hk : 1000 ≤ k) (hd0 : 0 ≤ d)
    (hdUpper : d ≤ ((k : ℝ) - 1) / (2 * k)) :
    0 ≤ fordRatioUpper36 k d := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hk1000 : (1000 : ℝ) ≤ k := by exact_mod_cast hk
  have hdHalf : d ≤ 1 / 2 := by
    have : ((k : ℝ) - 1) / (2 * k) < 1 / 2 := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  have hS : 0 < 2 - d ^ 2 := by nlinarith [sq_nonneg d]
  have h1d : 0 ≤ 1 - d := by linarith
  unfold fordRatioUpper36
  exact add_nonneg
    (div_nonneg h1d (mul_nonneg hS.le (by positivity)))
    (div_nonneg hd0 (mul_nonneg (sq_nonneg _) (by positivity)))

private theorem fordRatioUpper36_endpoint_zero
    {k : ℕ} {d : ℝ} (hk : 1000 ≤ k) (hd0 : 0 ≤ d)
    (hdUpper : d ≤ ((k : ℝ) - 1) / (2 * k)) :
    let S := 2 - d ^ 2
    let x := (k : ℝ) * (1 - d)
    x ≤ fordRatioUpper36 k d * ((k : ℝ) * (S * k - d)) := by
  let S := 2 - d ^ 2
  let x := (k : ℝ) * (1 - d)
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hk1000 : (1000 : ℝ) ≤ k := by exact_mod_cast hk
  have hdHalf : d ≤ 1 / 2 := by
    have : ((k : ℝ) - 1) / (2 * k) < 1 / 2 := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  have hS : 0 < S := by dsimp [S]; nlinarith [sq_nonneg d]
  have hSK : 1 ≤ S * (k : ℝ) := by
    dsimp [S]
    nlinarith [sq_nonneg d]
  have hSKpos : 0 < S * (k : ℝ) := by positivity
  have hinv : 1 / (S * (k : ℝ)) ≤ 1 := by
    apply (div_le_iff₀ hSKpos).2
    simpa using hSK
  have hrem : 0 ≤ d ^ 2 / S * (1 - 1 / (S * k)) := by positivity
  have hid :
      fordRatioUpper36 k d * ((k : ℝ) * (S * k - d)) - x =
        d ^ 2 / S * (1 - 1 / (S * k)) := by
    change (((1 - d) / (S * k) + d / (S ^ 2 * (k : ℝ) ^ 2)) *
        ((k : ℝ) * (S * k - d)) - x) =
      d ^ 2 / S * (1 - 1 / (S * k))
    dsimp [x]
    field_simp [ne_of_gt hS]
    ring
  linarith

private theorem fordRatioUpper36_endpoint_one
    {k : ℕ} {d : ℝ} (hk : 1000 ≤ k) (hd0 : 0 ≤ d)
    (hdUpper : d ≤ ((k : ℝ) - 1) / (2 * k)) :
    let S := 2 - d ^ 2
    let x := (k : ℝ) * (1 - d)
    x + 1 ≤ fordRatioUpper36 k d * ((k : ℝ) * (S * k + 2 + d)) := by
  let S := 2 - d ^ 2
  let x := (k : ℝ) * (1 - d)
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hk1000 : (1000 : ℝ) ≤ k := by exact_mod_cast hk
  have hdHalf : d ≤ 1 / 2 := by
    have : ((k : ℝ) - 1) / (2 * k) < 1 / 2 := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  have hS : 0 < S := by dsimp [S]; nlinarith [sq_nonneg d]
  have hrem : 0 ≤ d * (2 + d) / (S ^ 2 * k) := by positivity
  have hid :
      fordRatioUpper36 k d * ((k : ℝ) * (S * k + 2 + d)) - (x + 1) =
        d * (2 + d) / (S ^ 2 * k) := by
    change (((1 - d) / (S * k) + d / (S ^ 2 * (k : ℝ) ^ 2)) *
        ((k : ℝ) * (S * k + 2 + d)) - (x + 1)) =
      d * (2 + d) / (S ^ 2 * k)
    dsimp [x]
    field_simp [ne_of_gt hS]
    ring
  linarith

theorem fordEquation317
    {k : ℕ} {delta : ℝ} (hk : 1000 ≤ k)
    (hdeltaLower : (k : ℝ) < delta)
    (hdeltaUpper : delta ≤ ((k : ℝ) ^ 2 - k) / 2) :
    let r := fordR36 k delta
    let d := delta / (k : ℝ) ^ 2
    (1 - d) / (2 * k) ≤
        (r : ℝ) / (2 * (r : ℝ) * k + fordY35 k r delta) ∧
      (r : ℝ) / (2 * (r : ℝ) * k + fordY35 k r delta) ≤
        fordRatioUpper36 k d := by
  let r := fordR36 k delta
  let d := delta / (k : ℝ) ^ 2
  let x := (k : ℝ) * (1 - d)
  let t := (r : ℝ) - x
  let D : ℝ := 2 * (r : ℝ) * k + fordY35 k r delta
  dsimp only
  have hk26 : 26 ≤ k := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hrNat := (fordR36_bounds hk26 hdeltaLower.le hdeltaUpper).1
  have hr : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hy0 := fordY35_rounded_nonneg hk26 hdeltaLower.le hdeltaUpper
  have hD : 0 < D := by dsimp [D]; positivity
  have hd0 : 0 ≤ d := by
    dsimp [d]
    have : (0 : ℝ) < delta := lt_of_lt_of_le (by positivity) hdeltaLower.le
    positivity
  have hdUpper : d ≤ ((k : ℝ) - 1) / (2 * k) := by
    dsimp [d]
    rw [div_le_iff₀ (sq_pos_of_pos hkR)]
    field_simp
    nlinarith
  have hxEq : x = (k : ℝ) - delta / k := by
    dsimp [x, d]
    field_simp
  have hrBounds := fordR36_real_bounds hk26 hdeltaUpper
  have ht0 : 0 ≤ t := by
    dsimp [t]
    rw [hxEq]
    simpa [r] using hrBounds.1
  have ht1 : t ≤ 1 := by
    dsimp [t]
    rw [hxEq]
    dsimp [r]
    linarith [hrBounds.2]
  have hyUpper := (fordY35_rounded_bounds hk26 hdeltaLower.le hdeltaUpper).2
  have hdk : d * (k : ℝ) = delta / k := by
    dsimp [d]
    field_simp
  have hySimple : fordY35 k r delta ≤ 2 * d * (k : ℝ) ^ 2 := by
    have haOne : 1 < delta / (k : ℝ) := by
      apply (lt_div_iff₀ hkR).2
      simpa using hdeltaLower
    calc
      fordY35 k r delta ≤
          (delta / (k : ℝ)) *
            (2 * (k : ℝ) - delta / (k : ℝ) + 1) := by
              simpa [r] using hyUpper
      _ ≤ (delta / (k : ℝ)) * (2 * (k : ℝ)) := by
        apply mul_le_mul_of_nonneg_left
        · linarith
        · positivity
      _ = 2 * d * (k : ℝ) ^ 2 := by
        rw [← hdk]
        ring
  have hrLower : x ≤ r := by
    rw [hxEq]
    simpa [r] using hrBounds.1
  have hlambdaY :
      (1 - d) * fordY35 k r delta ≤ 2 * (k : ℝ) * r * d := by
    have hdOne : d ≤ 1 := by
      have hk1000 : (1000 : ℝ) ≤ k := by exact_mod_cast hk
      have hhalf : ((k : ℝ) - 1) / (2 * k) < 1 := by
        rw [div_lt_iff₀ (by positivity)]
        nlinarith
      linarith
    calc
      (1 - d) * fordY35 k r delta ≤
          (1 - d) * (2 * d * (k : ℝ) ^ 2) := by gcongr
      _ = 2 * (k : ℝ) * x * d := by
        dsimp [x]
        ring
      _ ≤ 2 * (k : ℝ) * r * d := by gcongr
  constructor
  · change (1 - d) / (2 * (k : ℝ)) ≤ (r : ℝ) / D
    rw [le_div_iff₀ hD]
    have hDid : D = 2 * (r : ℝ) * k + fordY35 k r delta := rfl
    rw [hDid]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * k)).2
    nlinarith
  · change (r : ℝ) / D ≤ fordRatioUpper36 k d
    rw [div_le_iff₀ hD]
    let S := 2 - d ^ 2
    have hU0 := fordRatioUpper36_nonneg hk hd0 hdUpper
    have hEnd0 := fordRatioUpper36_endpoint_zero hk hd0 hdUpper
    have hEnd1 := fordRatioUpper36_endpoint_one hk hd0 hdUpper
    have hDpoly :
        D = 4 * (k : ℝ) * r - (r : ℝ) ^ 2 + r -
          ((k : ℝ) ^ 2 + k - 2 * delta) := by
      dsimp [D]
      unfold fordY35
      ring
    have hD0 :
        4 * (k : ℝ) * x - x ^ 2 + x -
            ((k : ℝ) ^ 2 + k - 2 * delta) =
          (k : ℝ) * (S * k - d) := by
      dsimp [x, S, d]
      field_simp
      ring
    have hD1 :
        4 * (k : ℝ) * (x + 1) - (x + 1) ^ 2 + (x + 1) -
            ((k : ℝ) ^ 2 + k - 2 * delta) =
          (k : ℝ) * (S * k + 2 + d) := by
      dsimp [x, S, d]
      field_simp
      ring
    have hg0 :
        0 ≤ fordRatioUpper36 k d *
            (4 * (k : ℝ) * x - x ^ 2 + x -
              ((k : ℝ) ^ 2 + k - 2 * delta)) - x := by
      rw [hD0]
      exact sub_nonneg.mpr hEnd0
    have hg1 :
        0 ≤ fordRatioUpper36 k d *
            (4 * (k : ℝ) * (x + 1) - (x + 1) ^ 2 + (x + 1) -
              ((k : ℝ) ^ 2 + k - 2 * delta)) - (x + 1) := by
      rw [hD1]
      exact sub_nonneg.mpr hEnd1
    have hinterp :
        fordRatioUpper36 k d * D - (r : ℝ) =
          (1 - t) *
              (fordRatioUpper36 k d *
                (4 * (k : ℝ) * x - x ^ 2 + x -
                  ((k : ℝ) ^ 2 + k - 2 * delta)) - x) +
            t *
              (fordRatioUpper36 k d *
                (4 * (k : ℝ) * (x + 1) - (x + 1) ^ 2 + (x + 1) -
                  ((k : ℝ) ^ 2 + k - 2 * delta)) - (x + 1)) +
            fordRatioUpper36 k d * t * (1 - t) := by
      rw [hDpoly]
      dsimp [t]
      ring
    rw [← sub_nonneg]
    rw [hinterp]
    positivity

#print axioms fordEquation317

end

end GafniTao
