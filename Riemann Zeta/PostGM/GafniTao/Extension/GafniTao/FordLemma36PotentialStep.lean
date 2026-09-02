import GafniTao.FordLemma36Potential

/-!
# Ford Lemma 3.6: source potential step

This composes equation (3.14) with the logarithmic model estimate.  The
parameters `beta`, `c`, and `beta'` are Ford's literal parameters.
-/

namespace GafniTao

noncomputable section

def fordBeta36 (k : ℕ) : ℝ :=
  2 / (k : ℝ) - 32 / (21 * (k : ℝ) ^ 2)

def fordC36 (k : ℕ) : ℝ :=
  16 / (7 * (k : ℝ) ^ 3)

def fordBetaPrime36 (k : ℕ) (d : ℝ) : ℝ :=
  fordBeta36 k - fordC36 k / d

theorem fordBeta36_bounds {k : ℕ} (hk : 1000 ≤ k) :
    0 < fordBeta36 k ∧ fordBeta36 k ≤ 2 / (k : ℝ) := by
  have hkR : (1000 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by positivity
  constructor
  · unfold fordBeta36
    field_simp
    nlinarith
  · unfold fordBeta36
    exact sub_le_self _ (by positivity)

theorem fordBetaPrime36_bounds
    {k : ℕ} {d : ℝ} (hk : 1000 ≤ k)
    (hdLower : 1 / (k : ℝ) < d) :
    0 < fordBetaPrime36 k d ∧
      fordBetaPrime36 k d ≤ fordBeta36 k := by
  have hkR : (1000 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by positivity
  have hd0 : 0 < d := lt_of_lt_of_le (by positivity) hdLower.le
  have hkd : 1 < (k : ℝ) * d := by
    have h := (div_lt_iff₀ hk0).mp hdLower
    nlinarith
  have hcinv : fordC36 k / d < 16 / (7 * (k : ℝ) ^ 2) := by
    unfold fordC36
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    field_simp
    nlinarith
  have hbase : 0 < 2 / (k : ℝ) - 80 / (21 * (k : ℝ) ^ 2) := by
    field_simp
    nlinarith
  constructor
  · unfold fordBetaPrime36
    rw [sub_pos]
    have hsum :
        32 / (21 * (k : ℝ) ^ 2) + 16 / (7 * (k : ℝ) ^ 2) =
          80 / (21 * (k : ℝ) ^ 2) := by
      field_simp
      ring
    have hgap : 16 / (7 * (k : ℝ) ^ 2) < fordBeta36 k := by
      unfold fordBeta36
      linarith
    exact hcinv.trans hgap
  · unfold fordBetaPrime36
    have hc0 : 0 ≤ fordC36 k / d :=
      div_nonneg (by unfold fordC36; positivity) hd0.le
    linarith

theorem fordPotential36_actual_step
    {k : ℕ} {delta : ℝ} (hk : 1000 ≤ k)
    (hdeltaLower : (k : ℝ) < delta)
    (hdeltaUpper : delta ≤ ((k : ℝ) ^ 2 - k) / 2) :
    let r := fordR36 k delta
    let d := delta / (k : ℝ) ^ 2
    let d' := fordDeltaZero35 k r delta / (k : ℝ) ^ 2
    fordPotential36 d' ≤ fordPotential36 d - fordBeta36 k -
      (2 / 5) * fordBeta36 k ^ 2 +
        fordC36 k * (1 + (4 / 5) * fordBeta36 k) / d := by
  let r := fordR36 k delta
  let d := delta / (k : ℝ) ^ 2
  let d' := fordDeltaZero35 k r delta / (k : ℝ) ^ 2
  let beta := fordBeta36 k
  let c := fordC36 k
  let beta' := fordBetaPrime36 k d
  let model := d * (1 - (2 - d) / (2 - d ^ 2) * beta')
  dsimp only
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hkSq : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  have hdelta0 : 0 < delta := lt_of_lt_of_le (by positivity) hdeltaLower.le
  have hd0 : 0 < d := by dsimp [d]; positivity
  have hdLower : 1 / (k : ℝ) < d := by
    dsimp [d]
    rw [div_lt_div_iff₀ hkR hkSq]
    have hmul := mul_lt_mul_of_pos_right hdeltaLower hkR
    nlinarith
  have hdHalf : d ≤ 1 / 2 := by
    dsimp [d]
    rw [div_le_iff₀ hkSq]
    nlinarith
  have hbeta := fordBeta36_bounds hk
  have hbeta' := fordBetaPrime36_bounds hk hdLower
  have hc0 : 0 ≤ c := by dsimp [c, fordC36]; positivity
  have ha0 : 0 ≤ (2 - d) / (2 - d ^ 2) := by
    apply div_nonneg <;> nlinarith [sq_nonneg d]
  have haLe : (2 - d) / (2 - d ^ 2) ≤ 1 := by
    have hS : 0 < 2 - d ^ 2 := by nlinarith [sq_nonneg d]
    rw [div_le_one hS]
    have hdOne : d ≤ 1 := by linarith
    nlinarith [mul_nonneg hd0.le (sub_nonneg.mpr hdOne)]
  have hbeta'Small : (2 - d) / (2 - d ^ 2) * beta' < 1 := by
    have hmul : (2 - d) / (2 - d ^ 2) * beta' ≤ beta' := by
      nlinarith [mul_nonneg (sub_nonneg.mpr haLe) hbeta'.1.le]
    have htwoK : (2 : ℝ) / k ≤ 1 / 500 := by
      rw [div_le_div_iff₀ hkR (by norm_num)]
      nlinarith [show (1000 : ℝ) ≤ k by exact_mod_cast hk]
    exact lt_of_le_of_lt (hmul.trans (hbeta'.2.trans hbeta.2)) (by linarith)
  have hmodel0 : 0 < model := by
    dsimp [model]
    exact mul_pos hd0 (sub_pos.mpr hbeta'Small)
  have hmodelLe : model ≤ d := by
    dsimp [model]
    nlinarith [mul_nonneg ha0 hbeta'.1.le]
  have hd'Le : d' ≤ model := by
    have hcform : 16 / (7 * d * (k : ℝ) ^ 3) = c / d := by
      dsimp [c, fordC36]
      field_simp
    have h314 := fordEquation314 hk hdeltaLower hdeltaUpper
    change d' ≤ d * (1 - (2 - d) / (2 - d ^ 2) *
      (2 / (k : ℝ) - 32 / (21 * (k : ℝ) ^ 2) -
        16 / (7 * d * (k : ℝ) ^ 3))) at h314
    rw [hcform] at h314
    simpa [model, beta', fordBetaPrime36, beta, fordBeta36] using h314
  have hd'0 : 0 < d' := by
    have hlow := fordDeltaZero35_normalized_lower hk hdeltaLower hdeltaUpper
    have hfactor : 0 < 1 - 2 / (k : ℝ) := by
      have hk1000 : (1000 : ℝ) ≤ k := by exact_mod_cast hk
      rw [sub_pos]
      rw [div_lt_one hkR]
      linarith
    have : 0 < d * (1 - 2 / (k : ℝ)) := mul_pos hd0 hfactor
    exact lt_of_lt_of_le this (by simpa [r, d, d'] using hlow)
  have hmono : fordPotential36 d' ≤ fordPotential36 model :=
    fordPotential36_mono hd'0 hd'Le (hmodelLe.trans hdHalf)
  have hmodelStep : fordPotential36 model ≤
      fordPotential36 d - beta' - (2 / 5) * beta' ^ 2 := by
    simpa [model] using fordPotential36_model_step hd0 hdHalf hbeta'.1.le hbeta'Small
  have hprimeEq : beta' = beta - c / d := by
    simp [beta', beta, c, fordBetaPrime36]
  have hu0 : 0 ≤ c / d := by positivity
  have hreplace :
      -beta' - (2 / 5) * beta' ^ 2 ≤
        -beta - (2 / 5) * beta ^ 2 + c * (1 + (4 / 5) * beta) / d := by
    rw [hprimeEq]
    have hcdiv : c * (1 + (4 / 5) * beta) / d =
        (c / d) * (1 + (4 / 5) * beta) := by field_simp
    rw [hcdiv]
    nlinarith [sq_nonneg (c / d)]
  have hfinal : fordPotential36 d' ≤
      fordPotential36 d - beta - (2 / 5) * beta ^ 2 +
        c * (1 + (4 / 5) * beta) / d := by
    linarith [hmono, hmodelStep, hreplace]
  simpa [d', d, beta, c] using hfinal

#print axioms fordBeta36_bounds
#print axioms fordBetaPrime36_bounds
#print axioms fordPotential36_actual_step

end

end GafniTao
