import GafniTao.FordLemma36PotentialIteration

/-! # Ford Lemma 3.6: reciprocal geometric sum -/

namespace GafniTao

noncomputable section

theorem reciprocal_sum_of_contraction
    {d : ℕ → ℝ} {alpha : ℝ} {n : ℕ}
    (hn : 1 ≤ n) (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hd : ∀ m, m < n → 0 < d m)
    (hcontract : ∀ m, m + 1 < n → d (m + 1) ≤ d m * (1 - alpha)) :
    ∑ m ∈ Finset.range n, 1 / d m ≤ 1 / (alpha * d (n - 1)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => omega
      | succ n =>
          cases n with
          | zero =>
              have hd0 := hd 0 (by omega)
              have hden : 0 < alpha * d 0 := mul_pos halpha0 hd0
              simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
              rw [div_le_div_iff₀ hd0 hden]
              nlinarith [mul_nonneg (sub_nonneg.mpr halpha1) hd0.le]
          | succ m =>
              have hprevN : 1 ≤ m + 1 := by omega
              have hdPrev : ∀ j, j < m + 1 → 0 < d j := by
                intro j hj
                exact hd j (by omega)
              have hcontractPrev : ∀ j, j + 1 < m + 1 →
                  d (j + 1) ≤ d j * (1 - alpha) := by
                intro j hj
                exact hcontract j (by omega)
              have hsum := ih (m + 1) (by omega) hprevN hdPrev hcontractPrev
              have hsum' : ∑ x ∈ Finset.range (m + 1), 1 / d x ≤
                  1 / (alpha * d m) := by simpa using hsum
              have hdm := hd m (by omega)
              have hdnext := hd (m + 1) (by omega)
              have hcon := hcontract m (by omega)
              have hdenPrev : 0 < alpha * d m := mul_pos halpha0 hdm
              have hdenNext : 0 < alpha * d (m + 1) := mul_pos halpha0 hdnext
              have hrecip :
                  1 / (alpha * d m) ≤
                    (1 - alpha) / (alpha * d (m + 1)) := by
                rw [div_le_div_iff₀ hdenPrev hdenNext]
                nlinarith [mul_nonneg halpha0.le
                  (sub_nonneg.mpr (show d (m + 1) ≤ d m * (1 - alpha) from hcon))]
              rw [Finset.sum_range_succ]
              simp only [Nat.add_sub_cancel]
              calc
                ∑ x ∈ Finset.range (m + 1), 1 / d x + 1 / d (m + 1) ≤
                    1 / (alpha * d m) + 1 / d (m + 1) := by
                      exact add_le_add hsum' le_rfl
                _ ≤ (1 - alpha) / (alpha * d (m + 1)) +
                    1 / d (m + 1) := by linarith
                _ = 1 / (alpha * d (m + 1)) := by
                    field_simp [halpha0.ne', hdnext.ne']
                    ring

theorem fordDSequence36_reciprocal_sum
    {k n : ℕ} (hk : 1000 ≤ k) (hn : 1 ≤ n)
    (habove : ∀ m, m < n → (k : ℝ) < fordDeltaSequence36 k m) :
    ∑ m ∈ Finset.range n, 1 / fordDSequence36 k m ≤
      1 / (fordAlpha36 k * fordDSequence36 k (n - 1)) := by
  have halpha := fordAlpha36_bounds hk
  apply reciprocal_sum_of_contraction hn halpha.1 halpha.2.le
  · intro m hm
    exact (fordDSequence36_bounds_of_above hk
      (n := m) (fun j hj => habove j (by omega))).1
  · intro m hm
    exact fordDSequence36_contraction hk
      (n := m) (fun j hj => habove j (by omega))

theorem fordReciprocalCoeff36_ratio_bound
    {k : ℕ} (hk : 1000 ≤ k) :
    fordReciprocalCoeff36 k * (k : ℝ) / fordAlpha36 k ≤
      67 / (50 * (k : ℝ)) := by
  have hkR : (1000 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by positivity
  have halpha := (fordAlpha36_bounds hk).1
  have halphaForm : fordAlpha36 k =
      (84 * (k : ℝ) - 160) / (49 * (k : ℝ) ^ 2) := by
    unfold fordAlpha36 fordBeta36 fordC36
    field_simp
    ring
  have hcoeffForm : fordReciprocalCoeff36 k =
      16 * (5 * (k : ℝ) + 8) / (35 * (k : ℝ) ^ 4) := by
    unfold fordReciprocalCoeff36 fordC36
    field_simp
    ring
  have hlinear : 0 < 84 * (k : ℝ) - 160 := by nlinarith
  have hratioForm :
      fordReciprocalCoeff36 k * (k : ℝ) / fordAlpha36 k =
        112 * (5 * (k : ℝ) + 8) /
          (5 * (k : ℝ) * (84 * (k : ℝ) - 160)) := by
    rw [hcoeffForm, halphaForm]
    field_simp [halpha.ne', hk0.ne', hlinear.ne']
    ring
  rw [hratioForm]
  rw [div_le_div_iff₀ (by positivity :
    (0 : ℝ) < 5 * k * (84 * k - 160)) (by positivity : (0 : ℝ) < 50 * k)]
  nlinarith

theorem fordReciprocalError36_bound
    {k n : ℕ} (hk : 1000 ≤ k) (hn : 1 ≤ n)
    (habove : ∀ m, m < n → (k : ℝ) < fordDeltaSequence36 k m) :
    fordReciprocalCoeff36 k *
        ∑ m ∈ Finset.range n, 1 / fordDSequence36 k m ≤
      67 / (50 * (k : ℝ)) := by
  have hsum := fordDSequence36_reciprocal_sum hk hn habove
  have halpha := fordAlpha36_bounds hk
  have hk0 : (0 : ℝ) < k := by positivity
  have hlast := habove (n - 1) (by omega)
  have hdlast : 1 / (k : ℝ) < fordDSequence36 k (n - 1) := by
    unfold fordDSequence36
    have hkSq : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
    rw [div_lt_div_iff₀ hk0 hkSq]
    have hmul := mul_lt_mul_of_pos_right hlast hk0
    nlinarith
  have hden : 0 < fordAlpha36 k * fordDSequence36 k (n - 1) :=
    mul_pos halpha.1 (lt_of_lt_of_le (by positivity) hdlast.le)
  have hrecip :
      1 / (fordAlpha36 k * fordDSequence36 k (n - 1)) ≤
        (k : ℝ) / fordAlpha36 k := by
    rw [div_le_div_iff₀ hden halpha.1]
    have hkd : 1 < (k : ℝ) * fordDSequence36 k (n - 1) := by
      have := (div_lt_iff₀ hk0).mp hdlast
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hkd.le halpha.1.le
    nlinarith
  have hcoeff0 : 0 ≤ fordReciprocalCoeff36 k := by
    unfold fordReciprocalCoeff36 fordC36
    positivity
  calc
    fordReciprocalCoeff36 k *
        ∑ m ∈ Finset.range n, 1 / fordDSequence36 k m ≤
      fordReciprocalCoeff36 k *
        (1 / (fordAlpha36 k * fordDSequence36 k (n - 1))) :=
          mul_le_mul_of_nonneg_left hsum hcoeff0
    _ ≤ fordReciprocalCoeff36 k * ((k : ℝ) / fordAlpha36 k) :=
          mul_le_mul_of_nonneg_left hrecip hcoeff0
    _ = fordReciprocalCoeff36 k * (k : ℝ) / fordAlpha36 k := by ring
    _ ≤ 67 / (50 * (k : ℝ)) := fordReciprocalCoeff36_ratio_bound hk

#print axioms reciprocal_sum_of_contraction
#print axioms fordDSequence36_reciprocal_sum
#print axioms fordReciprocalCoeff36_ratio_bound
#print axioms fordReciprocalError36_bound

end

end GafniTao
