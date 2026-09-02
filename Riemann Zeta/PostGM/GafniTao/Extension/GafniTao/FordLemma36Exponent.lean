import GafniTao.FordLemma36Crossing

/-!
# Ford Lemma 3.6: unconditional permissible-exponent bound

This is the complete exponent half of Ford's Lemma 3.6.  It combines the
above-`k` iteration, the first crossing, and the invariant below-`k` branch.
The indexing here is zero-based: index `n` represents Ford's `Delta_(n+1)`.
-/

namespace GafniTao

noncomputable section

theorem fordLemma36_delta_exponent
    {k n : ℕ} (hk : 1000 ≤ k) (hnLower : 2 * k - 1 ≤ n)
    (hnUpper : (((n + 1 : ℕ) : ℝ)) ≤
      (k : ℝ) / 2 * (1 / 2 + Real.log (3 * (k : ℝ) / 8)) + 1) :
    fordDeltaSequence36 k n ≤
      (3 / 8 : ℝ) * (k : ℝ) ^ 2 * Real.exp
        (1 / 2 - 2 * (((n + 1 : ℕ) : ℝ)) / (k : ℝ) +
          169 / (100 * (k : ℝ))) := by
  by_cases habovePrev : ∀ m, m < n → (k : ℝ) < fordDeltaSequence36 k m
  · have hnorm := fordLemma36_delta_exponent_of_previous_above
      hk hnLower habovePrev hnUpper
    unfold fordDSequence36 at hnorm
    have hkSq : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
    simpa [mul_assoc, mul_left_comm, mul_comm] using (div_le_iff₀ hkSq).mp hnorm
  · have hex : ∃ m, m < n ∧ fordDeltaSequence36 k m ≤ (k : ℝ) := by
      rw [not_forall] at habovePrev
      obtain ⟨m, hm⟩ := habovePrev
      rw [Classical.not_imp] at hm
      exact ⟨m, hm.1, le_of_not_gt hm.2⟩
    let m : ℕ := Nat.find hex
    have hmSpec : m < n ∧ fordDeltaSequence36 k m ≤ (k : ℝ) := Nat.find_spec hex
    have hbefore : ∀ q, q < m → (k : ℝ) < fordDeltaSequence36 k q := by
      intro q hq
      by_contra hqNot
      have hqSpec : q < n ∧ fordDeltaSequence36 k q ≤ (k : ℝ) :=
        ⟨hq.trans hmSpec.1, le_of_not_gt hqNot⟩
      have := Nat.find_min' hex hqSpec
      omega
    have hmPos : 0 < fordDeltaSequence36 k m := by
      have hnorm := (fordDSequence36_bounds_of_above hk hbefore).1
      unfold fordDSequence36 at hnorm
      have hkSq : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
      rcases div_pos_iff.mp hnorm with hpos | hneg
      · exact hpos.1
      · exact False.elim ((not_lt_of_ge hkSq.le) hneg.2)
    have hnPos : 1 ≤ n := by omega
    have hmnPred : m ≤ n - 1 := by omega
    have hpred := fordDeltaSequence36_pos_le_of_pos_le
      hk hmnPred hmPos hmSpec.2
    have hbelow := fordLemma36_delta_exponent_of_prev_below
      (k := k) (m := n - 1) hk hpred.1 hpred.2
      (by simpa [show n - 1 + 2 = n + 1 by omega] using hnUpper)
    simpa [show n - 1 + 1 = n by omega,
      show n - 1 + 2 = n + 1 by omega] using hbelow

#print axioms fordLemma36_delta_exponent

end

end GafniTao
