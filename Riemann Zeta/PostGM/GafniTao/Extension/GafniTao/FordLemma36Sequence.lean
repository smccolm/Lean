import GafniTao.FordLemma36Equation318

/-! # Ford Lemma 3.6: normalized canonical sequence -/

namespace GafniTao

noncomputable section

def fordDSequence36 (k n : ℕ) : ℝ :=
  fordDeltaSequence36 k n / (k : ℝ) ^ 2

@[simp] theorem fordDSequence36_zero (k : ℕ) :
    fordDSequence36 k 0 = ((k : ℝ) - 1) / (2 * k) := by
  unfold fordDSequence36
  simp only [fordDeltaSequence36_zero]
  unfold fordDeltaInitial35
  field_simp

@[simp] theorem fordDSequence36_succ (k n : ℕ) :
    fordDSequence36 k (n + 1) =
      fordDeltaZero35 k (fordRSequence36 k n) (fordDeltaSequence36 k n) /
        (k : ℝ) ^ 2 := by
  simp [fordDSequence36]

theorem fordDSequence36_bounds_of_above
    {k n : ℕ} (hk : 1000 ≤ k)
    (habove : ∀ m, m < n → (k : ℝ) < fordDeltaSequence36 k m) :
    0 < fordDSequence36 k n ∧
      fordDSequence36 k n ≤ fordDSequence36 k 0 := by
  induction n with
  | zero =>
      have hkR : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
      simp only [fordDSequence36_zero]
      exact ⟨by positivity, le_rfl⟩
  | succ n ih =>
      have habovePrev : ∀ m, m < n → (k : ℝ) < fordDeltaSequence36 k m := by
        intro m hm
        exact habove m (by omega)
      have hprev := ih habovePrev
      have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
      have hkSq : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
      have hdeltaLower := habove n (by omega)
      have hdeltaUpper :
          fordDeltaSequence36 k n ≤ ((k : ℝ) ^ 2 - k) / 2 := by
        have hnorm := hprev.2
        unfold fordDSequence36 at hnorm
        rw [fordDeltaSequence36_zero, fordDeltaInitial35] at hnorm
        exact (div_le_div_iff_of_pos_right hkSq).mp hnorm
      have hlow := fordDeltaZero35_normalized_lower hk hdeltaLower hdeltaUpper
      have hcontract := fordEquation318 hk hdeltaLower hdeltaUpper
      have hfactor : 0 < 1 - 2 / (k : ℝ) := by
        rw [sub_pos, div_lt_one hkR]
        exact_mod_cast (show 2 < k by omega)
      have hnext0 : 0 < fordDSequence36 k (n + 1) := by
        have hprod : 0 < fordDSequence36 k n * (1 - 2 / (k : ℝ)) :=
          mul_pos hprev.1 hfactor
        apply lt_of_lt_of_le hprod
        simpa [fordDSequence36, fordRSequence36] using hlow
      have halpha := fordAlpha36_bounds hk
      have hnextPrev : fordDSequence36 k (n + 1) ≤ fordDSequence36 k n := by
        calc
          fordDSequence36 k (n + 1) ≤
              fordDSequence36 k n * (1 - fordAlpha36 k) := by
                simpa [fordDSequence36, fordRSequence36] using hcontract
          _ ≤ fordDSequence36 k n := by
                nlinarith [mul_nonneg hprev.1.le halpha.1.le]
      exact ⟨hnext0, hnextPrev.trans hprev.2⟩

theorem fordDSequence36_contraction
    {k n : ℕ} (hk : 1000 ≤ k)
    (habove : ∀ m, m ≤ n → (k : ℝ) < fordDeltaSequence36 k m) :
    fordDSequence36 k (n + 1) ≤
      fordDSequence36 k n * (1 - fordAlpha36 k) := by
  have hbounds := fordDSequence36_bounds_of_above hk
    (n := n) (fun m hm => habove m hm.le)
  have hdeltaUpper :
      fordDeltaSequence36 k n ≤ ((k : ℝ) ^ 2 - k) / 2 := by
    have hkSq : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
    have hnorm := hbounds.2
    unfold fordDSequence36 at hnorm
    rw [fordDeltaSequence36_zero, fordDeltaInitial35] at hnorm
    exact (div_le_div_iff_of_pos_right hkSq).mp hnorm
  simpa [fordDSequence36, fordRSequence36] using
    fordEquation318 hk (habove n le_rfl) hdeltaUpper

theorem fordDSequence36_lower_step
    {k n : ℕ} (hk : 1000 ≤ k)
    (habove : ∀ m, m ≤ n → (k : ℝ) < fordDeltaSequence36 k m) :
    fordDSequence36 k n * (1 - 2 / (k : ℝ)) ≤
      fordDSequence36 k (n + 1) := by
  have hbounds := fordDSequence36_bounds_of_above hk
    (n := n) (fun m hm => habove m hm.le)
  have hkSq : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  have hdeltaUpper :
      fordDeltaSequence36 k n ≤ ((k : ℝ) ^ 2 - k) / 2 := by
    have hnorm := hbounds.2
    unfold fordDSequence36 at hnorm
    rw [fordDeltaSequence36_zero, fordDeltaInitial35] at hnorm
    exact (div_le_div_iff_of_pos_right hkSq).mp hnorm
  simpa [fordDSequence36, fordRSequence36] using
    fordDeltaZero35_normalized_lower hk (habove n le_rfl) hdeltaUpper

#print axioms fordDSequence36_bounds_of_above
#print axioms fordDSequence36_contraction
#print axioms fordDSequence36_lower_step

end

end GafniTao
