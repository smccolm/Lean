import GafniTao.HeathBrownEP1Algebra

/-!
# Heath--Brown EP1: algebra on the large logarithmic strips

For derivative order `k`, Heath--Brown partitions the logarithmic scale by

`((k-1)^2+1)/k ≤ tau ≤ (k^2+1)/(k+1)`.

This file proves directly that each of the three exponents in the native
`k`-th derivative estimate is at most `-49/(80*tau^2)` on that strip.
The proof uses the exact breakpoint inequality and a factored monotonicity
calculation; no continuity or unformalized convexity assertion is used.
-/

namespace GafniTao

noncomputable section

def heathBrownEP1StripLower (k : ℕ) : ℝ :=
  (((k : ℝ) - 1) ^ 2 + 1) / k

def heathBrownEP1StripUpper (k : ℕ) : ℝ :=
  ((k : ℝ) ^ 2 + 1) / ((k : ℝ) + 1)

theorem heathBrownEP1StripUpper_lt_order
    {k : ℕ} (hk : 2 ≤ k) :
    heathBrownEP1StripUpper k < k := by
  have hkReal : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkOnePos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  unfold heathBrownEP1StripUpper
  rw [div_lt_iff₀ hkOnePos]
  nlinarith

theorem heathBrownEP1StripLower_pos
    {k : ℕ} (hk : 1 ≤ k) :
    0 < heathBrownEP1StripLower k := by
  have hkReal : (1 : ℝ) ≤ k := by exact_mod_cast hk
  unfold heathBrownEP1StripLower
  apply div_pos
  · nlinarith [sq_nonneg ((k : ℝ) - 1)]
  · positivity

/-- The source breakpoint estimate, rewritten at the lower end of strip
`k` by applying the published inequality to order `k-1`. -/
theorem heathBrown_EP1_lower_breakpoint
    {k : ℕ} (hk : 6 ≤ k) :
    (49 / 80 : ℝ) ≤
      heathBrownEP1StripLower k ^ 2 /
        ((k : ℝ) * ((k : ℝ) - 1)) := by
  have hkSub : 5 ≤ k - 1 := by omega
  have hbp := heathBrown_EP1_large_breakpoint hkSub
  have hkOne : 1 ≤ k := by omega
  have hkPos : (0 : ℝ) < k := by positivity
  have hkSubPos : (0 : ℝ) < (k : ℝ) - 1 := by
    have : (6 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  rw [Nat.cast_sub hkOne] at hbp
  norm_num at hbp
  have heq :
      (((k : ℝ) - 1) ^ 2 + 1) ^ 2 /
          (((k : ℝ) - 1) * (((k : ℝ) - 1) + 1) ^ 3) =
        ((((k : ℝ) - 1) ^ 2 + 1) / k) ^ 2 /
          ((k : ℝ) * ((k : ℝ) - 1)) := by
    field_simp [hkPos.ne', hkSubPos.ne']
    ring
  unfold heathBrownEP1StripLower
  rw [← heq]
  simpa only [sub_add_cancel] using hbp

/-- The constant middle term of the derivative estimate has the required
EP1 saving on the lower half of every large strip. -/
theorem heathBrown_EP1_large_constant
    {k : ℕ} {tau : ℝ} (hk : 6 ≤ k)
    (hlower : heathBrownEP1StripLower k ≤ tau) :
    (-1 / ((k : ℝ) * ((k : ℝ) - 1))) ≤
      -49 / (80 * tau ^ 2) := by
  have hkReal : (6 : ℝ) ≤ k := by exact_mod_cast hk
  have hkPos : (0 : ℝ) < k := by linarith
  have hkOnePos : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have hden : 0 < (k : ℝ) * ((k : ℝ) - 1) :=
    mul_pos hkPos hkOnePos
  have hLpos := heathBrownEP1StripLower_pos (show 1 ≤ k by omega)
  have htauPos : 0 < tau := lt_of_lt_of_le hLpos hlower
  have hbp := heathBrown_EP1_lower_breakpoint hk
  have hbpMul : (49 / 80 : ℝ) *
        ((k : ℝ) * ((k : ℝ) - 1)) ≤
      heathBrownEP1StripLower k ^ 2 :=
    (le_div_iff₀ hden).mp hbp
  have hsq : heathBrownEP1StripLower k ^ 2 ≤ tau ^ 2 := by
    nlinarith
  have hfrac : 49 / (80 * tau ^ 2) ≤
      1 / ((k : ℝ) * ((k : ℝ) - 1)) := by
    rw [div_le_div_iff₀ (by positivity : 0 < 80 * tau ^ 2) hden]
    norm_num
    nlinarith
  calc
    -1 / ((k : ℝ) * ((k : ℝ) - 1)) =
        -(1 / ((k : ℝ) * ((k : ℝ) - 1))) := by ring
    _ ≤ -(49 / (80 * tau ^ 2)) := neg_le_neg hfrac
    _ = -49 / (80 * tau ^ 2) := by ring

/-- On the upper half of a strip the sloping first exponent is controlled
by the same breakpoint calculation. -/
theorem heathBrown_EP1_large_sloping
    {k : ℕ} {tau : ℝ} (hk : 6 ≤ k)
    (hlower : (k : ℝ) - 1 ≤ tau)
    (hupper : tau ≤ heathBrownEP1StripUpper k) :
    (tau - (k : ℝ)) / ((k : ℝ) * ((k : ℝ) - 1)) ≤
      -49 / (80 * tau ^ 2) := by
  let K : ℝ := k
  let U : ℝ := heathBrownEP1StripUpper k
  have hK : (6 : ℝ) ≤ K := by dsimp only [K]; exact_mod_cast hk
  have hKpos : 0 < K := by linarith
  have hKmOnePos : 0 < K - 1 := by linarith
  have hKpOnePos : 0 < K + 1 := by linarith
  have hden : 0 < K * (K - 1) := mul_pos hKpos hKmOnePos
  have hUformula : U = (K ^ 2 + 1) / (K + 1) := by
    rfl
  have hUpos : 0 < U := by
    rw [hUformula]
    positivity
  have htauPos : 0 < tau := by
    have : 0 < K - 1 := hKmOnePos
    exact lt_of_lt_of_le this (by simpa only [K] using hlower)
  have hbp := heathBrown_EP1_large_breakpoint (show 5 ≤ k by omega)
  have heqU :
      ((k : ℝ) ^ 2 + 1) ^ 2 /
          ((k : ℝ) * ((k : ℝ) + 1) ^ 3) =
        U ^ 2 / (K * (K + 1)) := by
    rw [hUformula]
    dsimp only [K]
    field_simp [hKpos.ne', hKpOnePos.ne']
  have hbpU : (49 / 80 : ℝ) ≤ U ^ 2 / (K * (K + 1)) := by
    rw [← heqU]
    exact hbp
  have hbpMul : (49 / 80 : ℝ) * (K * (K + 1)) ≤ U ^ 2 :=
    (le_div_iff₀ (mul_pos hKpos hKpOnePos)).mp hbpU
  have hKU : K - U = (K - 1) / (K + 1) := by
    rw [hUformula]
    field_simp [hKpOnePos.ne']
    ring
  have hbreakProduct :
      (49 / 80 : ℝ) * (K * (K - 1)) ≤ (K - U) * U ^ 2 := by
    rw [hKU]
    have hratio : 0 ≤ (K - 1) / (K + 1) := by positivity
    have hmul := mul_le_mul_of_nonneg_right hbpMul hratio
    calc
      (49 / 80 : ℝ) * (K * (K - 1)) =
          ((49 / 80 : ℝ) * (K * (K + 1))) *
            ((K - 1) / (K + 1)) := by
              field_simp [hKpOnePos.ne']
      _ ≤ U ^ 2 * ((K - 1) / (K + 1)) := hmul
      _ = (K - 1) / (K + 1) * U ^ 2 := by ring
  have hUK : U < K := by
    dsimp only [U, K]
    exact heathBrownEP1StripUpper_lt_order (show 2 ≤ k by omega)
  have htauUpper : tau ≤ U := by simpa only [U] using hupper
  have htauLower : K - 1 ≤ tau := by simpa only [K] using hlower
  let a : ℝ := tau - (K - 1)
  let b : ℝ := U - (K - 1)
  have ha : 0 ≤ a := by dsimp only [a]; linarith
  have hb : 0 ≤ b := by dsimp only [b]; linarith
  have hbracket :
      0 ≤ tau ^ 2 + tau * U + U ^ 2 - K * (tau + U) := by
    have hbase : 0 ≤ (K - 1) * (K - 3) := by
      exact mul_nonneg (by linarith) (by linarith)
    have hcoef : 0 ≤ 2 * K - 3 := by linarith
    have hsquares : 0 ≤ a ^ 2 + a * b + b ^ 2 := by positivity
    have hid :
        tau ^ 2 + tau * U + U ^ 2 - K * (tau + U) =
          (K - 1) * (K - 3) + (2 * K - 3) * (a + b) +
            (a ^ 2 + a * b + b ^ 2) := by
      dsimp only [a, b]
      ring
    rw [hid]
    positivity
  have hmonotone : (K - U) * U ^ 2 ≤ (K - tau) * tau ^ 2 := by
    have hfactor := mul_nonneg (sub_nonneg.mpr htauUpper) hbracket
    nlinarith
  have hproduct :
      (49 / 80 : ℝ) * (K * (K - 1)) ≤ (K - tau) * tau ^ 2 :=
    hbreakProduct.trans hmonotone
  change (tau - K) / (K * (K - 1)) ≤ -49 / (80 * tau ^ 2)
  have hfrac : 49 / (80 * tau ^ 2) ≤ (K - tau) / (K * (K - 1)) := by
    rw [div_le_div_iff₀ (by positivity : 0 < 80 * tau ^ 2) hden]
    nlinarith
  calc
    (tau - K) / (K * (K - 1)) =
        -((K - tau) / (K * (K - 1))) := by ring
    _ ≤ -(49 / (80 * tau ^ 2)) := neg_le_neg hfrac
    _ = -49 / (80 * tau ^ 2) := by ring

/-- All three derivative-test savings are bounded by the EP1 target on a
large source strip. -/
theorem heathBrown_EP1_large_three_savings
    {k : ℕ} {tau : ℝ} (hk : 6 ≤ k)
    (hlower : heathBrownEP1StripLower k ≤ tau)
    (hupper : tau ≤ heathBrownEP1StripUpper k) :
    (tau - (k : ℝ)) / ((k : ℝ) * ((k : ℝ) - 1)) ≤
        -49 / (80 * tau ^ 2) ∧
      (-1 / ((k : ℝ) * ((k : ℝ) - 1))) ≤
        -49 / (80 * tau ^ 2) ∧
      (-2 * tau / ((k : ℝ) ^ 2 * ((k : ℝ) - 1))) ≤
        -49 / (80 * tau ^ 2) := by
  have hkReal : (6 : ℝ) ≤ k := by exact_mod_cast hk
  have htauPos : 0 < tau :=
    lt_of_lt_of_le (heathBrownEP1StripLower_pos (show 1 ≤ k by omega)) hlower
  by_cases hsplit : tau ≤ (k : ℝ) - 1
  · have hconstant := heathBrown_EP1_large_constant hk hlower
    have hkPos : (0 : ℝ) < k := by positivity
    have hkOnePos : (0 : ℝ) < (k : ℝ) - 1 := by linarith
    constructor
    · have hden : 0 < (k : ℝ) * ((k : ℝ) - 1) := by positivity
      apply le_trans ?_ hconstant
      rw [div_le_iff₀ hden]
      field_simp [hkPos.ne', hkOnePos.ne']
      nlinarith
    constructor
    · exact hconstant
    · apply le_trans ?_ hconstant
      have hden3 : 0 < (k : ℝ) ^ 2 * ((k : ℝ) - 1) :=
        mul_pos (sq_pos_of_pos hkPos) hkOnePos
      have hden2 : 0 < (k : ℝ) * ((k : ℝ) - 1) :=
        mul_pos hkPos hkOnePos
      have hhalf : (k : ℝ) / 2 ≤ heathBrownEP1StripLower k := by
        unfold heathBrownEP1StripLower
        rw [le_div_iff₀ hkPos]
        nlinarith [sq_nonneg ((k : ℝ) - 1)]
      have htauHalf : (k : ℝ) / 2 ≤ tau := hhalf.trans hlower
      rw [div_le_div_iff₀ hden3 hden2]
      nlinarith
  · have hsplit' : (k : ℝ) - 1 ≤ tau := le_of_not_ge hsplit
    have hslope := heathBrown_EP1_large_sloping hk hsplit' hupper
    have hkPos : (0 : ℝ) < k := by positivity
    have hkOnePos : (0 : ℝ) < (k : ℝ) - 1 := by linarith
    constructor
    · exact hslope
    constructor
    · apply le_trans ?_ hslope
      have hden : 0 < (k : ℝ) * ((k : ℝ) - 1) :=
        mul_pos hkPos hkOnePos
      rw [div_le_div_iff₀ hden hden]
      nlinarith
    · apply le_trans ?_ hslope
      have hden3 : 0 < (k : ℝ) ^ 2 * ((k : ℝ) - 1) :=
        mul_pos (sq_pos_of_pos hkPos) hkOnePos
      have hden2 : 0 < (k : ℝ) * ((k : ℝ) - 1) :=
        mul_pos hkPos hkOnePos
      have haux : 0 ≤
          (tau - ((k : ℝ) - 1)) * ((k : ℝ) + 2) := by positivity
      rw [div_le_div_iff₀ hden3 hden2]
      nlinarith

#print axioms heathBrown_EP1_lower_breakpoint
#print axioms heathBrown_EP1_large_constant
#print axioms heathBrown_EP1_large_sloping
#print axioms heathBrown_EP1_large_three_savings

end

end GafniTao
