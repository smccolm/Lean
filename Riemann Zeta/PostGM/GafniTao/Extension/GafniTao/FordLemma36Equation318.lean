import GafniTao.FordLemma36PotentialStep

/-! # Ford Lemma 3.6: equation (3.18) -/

namespace GafniTao

noncomputable section

def fordAlpha36 (k : ℕ) : ℝ :=
  (6 / 7) * (fordBeta36 k - (k : ℝ) * fordC36 k)

theorem fordAlpha36_bounds {k : ℕ} (hk : 1000 ≤ k) :
    0 < fordAlpha36 k ∧ fordAlpha36 k < 1 := by
  have hkR : (1000 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by positivity
  have hinside : 0 < fordBeta36 k - (k : ℝ) * fordC36 k := by
    unfold fordBeta36 fordC36
    field_simp
    nlinarith
  constructor
  · unfold fordAlpha36
    positivity
  · have hbeta := (fordBeta36_bounds hk).2
    unfold fordAlpha36
    have hc0 : 0 ≤ (k : ℝ) * fordC36 k := by
      apply mul_nonneg hk0.le
      unfold fordC36
      positivity
    have h : fordBeta36 k - (k : ℝ) * fordC36 k ≤ 2 / (k : ℝ) :=
      by linarith
    have htwo : (2 : ℝ) / k ≤ 1 / 500 := by
      rw [div_le_div_iff₀ hk0 (by norm_num)]
      nlinarith
    nlinarith

theorem fordEquation318
    {k : ℕ} {delta : ℝ} (hk : 1000 ≤ k)
    (hdeltaLower : (k : ℝ) < delta)
    (hdeltaUpper : delta ≤ ((k : ℝ) ^ 2 - k) / 2) :
    let r := fordR36 k delta
    let d := delta / (k : ℝ) ^ 2
    fordDeltaZero35 k r delta / (k : ℝ) ^ 2 ≤
      d * (1 - fordAlpha36 k) := by
  let r := fordR36 k delta
  let d := delta / (k : ℝ) ^ 2
  let a : ℝ := (2 - d) / (2 - d ^ 2)
  let beta' := fordBetaPrime36 k d
  dsimp only
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hkSq : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  have hd0 : 0 < d := by
    dsimp [d]
    have hdelta0 : 0 < delta := lt_of_lt_of_le (by positivity) hdeltaLower.le
    positivity
  have hdLower : 1 / (k : ℝ) < d := by
    dsimp [d]
    rw [div_lt_div_iff₀ hkR hkSq]
    have hmul := mul_lt_mul_of_pos_right hdeltaLower hkR
    nlinarith
  have hdHalf : d ≤ 1 / 2 := by
    dsimp [d]
    rw [div_le_iff₀ hkSq]
    nlinarith
  have hS : 0 < 2 - d ^ 2 := by nlinarith [sq_nonneg d]
  have haLower : (6 / 7 : ℝ) ≤ a := by
    dsimp [a]
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 7) hS]
    nlinarith [sq_nonneg (d - 1 / 2)]
  have hbeta' := fordBetaPrime36_bounds hk hdLower
  have hc0 : 0 ≤ fordC36 k := by unfold fordC36; positivity
  have hcPos : 0 < fordC36 k := by unfold fordC36; positivity
  have hcDiv : fordC36 k / d < (k : ℝ) * fordC36 k := by
    have hinv : 1 / d < (k : ℝ) := by
      rw [div_lt_iff₀ hd0]
      have := (div_lt_iff₀ hkR).mp hdLower
      nlinarith
    rw [div_eq_mul_inv]
    simpa [one_div, mul_comm] using mul_lt_mul_of_pos_left hinv hcPos
  have hbetaLower : fordBeta36 k - (k : ℝ) * fordC36 k ≤ beta' := by
    dsimp [beta', fordBetaPrime36]
    linarith
  have hinside0 : 0 ≤ fordBeta36 k - (k : ℝ) * fordC36 k :=
    (fordAlpha36_bounds hk).1.le |> fun h => by
      unfold fordAlpha36 at h
      nlinarith
  have hproduct : fordAlpha36 k ≤ a * beta' := by
    unfold fordAlpha36
    have ha0 : 0 ≤ a := le_trans (by norm_num) haLower
    exact mul_le_mul haLower hbetaLower hinside0 ha0
  have h314 := fordEquation314 hk hdeltaLower hdeltaUpper
  have hcform :
      16 / (7 * d * (k : ℝ) ^ 3) = fordC36 k / d := by
    unfold fordC36
    field_simp
  have h314' :
      fordDeltaZero35 k r delta / (k : ℝ) ^ 2 ≤ d * (1 - a * beta') := by
    change fordDeltaZero35 k r delta / (k : ℝ) ^ 2 ≤
      d * (1 - (2 - d) / (2 - d ^ 2) *
        (2 / (k : ℝ) - 32 / (21 * (k : ℝ) ^ 2) -
          16 / (7 * d * (k : ℝ) ^ 3))) at h314
    rw [hcform] at h314
    simpa [a, beta', fordBetaPrime36, fordBeta36] using h314
  calc
    fordDeltaZero35 k r delta / (k : ℝ) ^ 2 ≤ d * (1 - a * beta') := h314'
    _ ≤ d * (1 - fordAlpha36 k) := by
      exact mul_le_mul_of_nonneg_left (sub_le_sub_left hproduct 1) hd0.le

#print axioms fordAlpha36_bounds
#print axioms fordEquation318

end

end GafniTao
