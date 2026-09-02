import GafniTao.FordLemma36LowerIterate

/-!
# Ford Lemma 3.6: the numerical decrement after equation (3.21)

The decimal constants are represented by their exact rational values.  The
monotonicity argument is proved for the literal rational function appearing
in (3.21), rather than delegated to a numerical calculation.
-/

namespace GafniTao

noncomputable section

def fordDecrementShape36 (d : ℝ) : ℝ :=
  2 * d * ((2 - d) / (2 - d ^ 2) - 1 / 500)

theorem fordDecrementShape36_mono_on_half
    {a d : ℝ} (ha0 : 0 ≤ a) (had : a ≤ d) (hdHalf : d ≤ 1 / 2) :
    fordDecrementShape36 a ≤ fordDecrementShape36 d := by
  have hd0 : 0 ≤ d := ha0.trans had
  have haHalf : a ≤ 1 / 2 := had.trans hdHalf
  have hdenA : 0 < 2 - a ^ 2 := by nlinarith [sq_nonneg a]
  have hdenD : 0 < 2 - d ^ 2 := by nlinarith [sq_nonneg d]
  have hdenProd : 0 < (2 - a ^ 2) * (2 - d ^ 2) :=
    mul_pos hdenA hdenD
  have hfactor : 1 ≤ 2 - d - a + a * d := by
    nlinarith [mul_nonneg ha0 hd0]
  have hdenAUpper : 2 - a ^ 2 ≤ 2 := by nlinarith [sq_nonneg a]
  have hdenDUpper : 2 - d ^ 2 ≤ 2 := by nlinarith [sq_nonneg d]
  have hdenProdUpper : (2 - a ^ 2) * (2 - d ^ 2) ≤ 4 := by
    nlinarith [mul_nonneg hdenA.le hdenD.le,
      mul_le_mul hdenAUpper hdenDUpper hdenD.le (by norm_num : (0 : ℝ) ≤ 2)]
  have hratio : (1 / 500 : ℝ) ≤
      2 * (2 - d - a + a * d) / ((2 - a ^ 2) * (2 - d ^ 2)) := by
    rw [le_div_iff₀ hdenProd]
    nlinarith
  have hdiffIdentity :
      d * (2 - d) / (2 - d ^ 2) -
          a * (2 - a) / (2 - a ^ 2) =
        (d - a) *
          (2 * (2 - d - a + a * d) / ((2 - a ^ 2) * (2 - d ^ 2))) := by
    field_simp [hdenA.ne', hdenD.ne']
    ring
  have hcoreStrong :
      a * (2 - a) / (2 - a ^ 2) + (d - a) / 500 ≤
        d * (2 - d) / (2 - d ^ 2) := by
    have hmul := mul_le_mul_of_nonneg_left hratio (sub_nonneg.mpr had)
    have hmul' : (d - a) / 500 ≤
        (d - a) *
          (2 * (2 - d - a + a * d) / ((2 - a ^ 2) * (2 - d ^ 2))) := by
      nlinarith
    rw [← hdiffIdentity] at hmul'
    linarith
  have haIdentity : fordDecrementShape36 a =
      2 * (a * (2 - a) / (2 - a ^ 2) - a / 500) := by
    unfold fordDecrementShape36
    ring
  have hdIdentity : fordDecrementShape36 d =
      2 * (d * (2 - d) / (2 - d ^ 2) - d / 500) := by
    unfold fordDecrementShape36
    ring
  rw [haIdentity, hdIdentity]
  nlinarith

theorem fordDecrementShape36_at_cutoff :
    (479 / 25000 : ℝ) ≤ fordDecrementShape36 (24119 / 2500000) := by
  norm_num [fordDecrementShape36]

theorem fordDecrementShape36_source_predecessor
    {k n : ℕ} (hk : 1000 ≤ k) (hnLower : 2 ≤ n)
    (hnUpper : 100 * (n - 1) ≤ 197 * k)
    (habove : ∀ m, m < n - 2 → (k : ℝ) < fordDeltaSequence36 k m) :
    (479 / 25000 : ℝ) ≤ fordDecrementShape36 (fordDSequence36 k (n - 2)) := by
  have hlow := fordDSequence36_source_predecessor_lower hk hnLower hnUpper habove
  have hbounds := fordDSequence36_bounds_of_above hk (n := n - 2) habove
  have hhalf : fordDSequence36 k (n - 2) ≤ 1 / 2 := by
    calc
      fordDSequence36 k (n - 2) ≤ fordDSequence36 k 0 := hbounds.2
      _ ≤ (1 / 2 : ℝ) := (by
        rw [fordDSequence36_zero]
        have hk0 : (0 : ℝ) < k := by positivity
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * k)]
        nlinarith)
  exact fordDecrementShape36_at_cutoff.trans
    (fordDecrementShape36_mono_on_half (by norm_num) hlow hhalf)

theorem fordDSequence36_source_decrement
    {k n : ℕ} (hk : 1000 ≤ k) (hnLower : 2 ≤ n)
    (hnUpper : 100 * (n - 1) ≤ 197 * k)
    (habove : ∀ m, m < n - 2 → (k : ℝ) < fordDeltaSequence36 k m) :
    (479 / 25000 : ℝ) / (k : ℝ) ≤
      fordDSequence36 k (n - 2) - fordDSequence36 k (n - 1) := by
  have hk0 : (0 : ℝ) < k := by positivity
  have hkSq : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  have hlow := fordDSequence36_source_predecessor_lower hk hnLower hnUpper habove
  have hcurrentAbove : (k : ℝ) < fordDeltaSequence36 k (n - 2) := by
    have hscaled := mul_le_mul_of_nonneg_right hlow hkSq.le
    unfold fordDSequence36 at hscaled
    have hscaled' : (24119 / 2500000 : ℝ) * (k : ℝ) ^ 2 ≤
        fordDeltaSequence36 k (n - 2) := by
      convert hscaled using 1
      all_goals field_simp
    have hcut : (k : ℝ) < (24119 / 2500000 : ℝ) * (k : ℝ) ^ 2 := by
      have hkR : (1000 : ℝ) ≤ k := by exact_mod_cast hk
      nlinarith
    exact hcut.trans_le hscaled'
  have hbounds := fordDSequence36_bounds_of_above hk (n := n - 2) habove
  have hdeltaUpper : fordDeltaSequence36 k (n - 2) ≤
      ((k : ℝ) ^ 2 - k) / 2 := by
    have h := hbounds.2
    rw [fordDSequence36_zero] at h
    unfold fordDSequence36 at h
    have hscaled := mul_le_mul_of_nonneg_right h hkSq.le
    have hk0' : (k : ℝ) ≠ 0 := ne_of_gt hk0
    calc
      fordDeltaSequence36 k (n - 2) ≤
          ((k : ℝ) - 1) / (2 * k) * (k : ℝ) ^ 2 := by
        convert hscaled using 1
        all_goals field_simp [hk0']
      _ = ((k : ℝ) ^ 2 - k) / 2 := by
        field_simp [hk0']
  have h321 := fordEquation321_sequence hk hcurrentAbove hdeltaUpper
  have hshape := fordDecrementShape36_source_predecessor
    hk hnLower hnUpper habove
  have hdiv := div_le_div_of_nonneg_right hshape hk0.le
  have hindex : n - 2 + 1 = n - 1 := by omega
  rw [hindex] at h321
  calc
    (479 / 25000 : ℝ) / (k : ℝ) ≤
        fordDecrementShape36 (fordDSequence36 k (n - 2)) / (k : ℝ) := hdiv
    _ = (2 * fordDSequence36 k (n - 2) / (k : ℝ)) *
        ((2 - fordDSequence36 k (n - 2)) /
          (2 - fordDSequence36 k (n - 2) ^ 2) - 1 / 500) := by
      unfold fordDecrementShape36
      ring
    _ ≤ fordDSequence36 k (n - 2) - fordDSequence36 k (n - 1) := h321

theorem fordDeltaSequence36_source_decrement
    {k n : ℕ} (hk : 1000 ≤ k) (hnLower : 2 ≤ n)
    (hnUpper : 100 * (n - 1) ≤ 197 * k)
    (habove : ∀ m, m < n - 2 → (k : ℝ) < fordDeltaSequence36 k m) :
    (479 / 25000 : ℝ) * (k : ℝ) ≤
      fordDeltaSequence36 k (n - 2) - fordDeltaSequence36 k (n - 1) := by
  have hkSq : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  have h := fordDSequence36_source_decrement hk hnLower hnUpper habove
  unfold fordDSequence36 at h
  have hmul := mul_le_mul_of_nonneg_right h hkSq.le
  calc
    (479 / 25000 : ℝ) * (k : ℝ) =
        ((479 / 25000 : ℝ) / (k : ℝ)) * (k : ℝ) ^ 2 := by
      field_simp
    _ ≤ (fordDeltaSequence36 k (n - 2) / (k : ℝ) ^ 2 -
        fordDeltaSequence36 k (n - 1) / (k : ℝ) ^ 2) *
          (k : ℝ) ^ 2 := hmul
    _ = fordDeltaSequence36 k (n - 2) -
        fordDeltaSequence36 k (n - 1) := by field_simp

#print axioms fordDecrementShape36_mono_on_half
#print axioms fordDecrementShape36_at_cutoff
#print axioms fordDecrementShape36_source_predecessor
#print axioms fordDSequence36_source_decrement
#print axioms fordDeltaSequence36_source_decrement

end

end GafniTao
