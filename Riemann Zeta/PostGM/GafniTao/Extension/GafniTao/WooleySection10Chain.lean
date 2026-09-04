import GafniTao.WooleySection10Step

/-!
# The finite Section 10 iteration chain

This file iterates the corrected source transition as a relation.  Keeping
the chain in `Prop` permits the existential selections made by Lemma 9.3
without introducing a noncomputable state generator.  The endpoint theorem
records exactly the scale and accumulated-weight facts used after (10.8).
-/

namespace GafniTao

noncomputable section

/-- A chain of `n` consecutive Lemma-9.3 transitions. -/
inductive WooleyIterationChain
    (k p : ℕ) (Lambda D delta theta : ℝ)
    (K : ℕ → ℕ → ℕ → ℝ) :
    ℕ → ℕ → ℕ → ℕ → Prop
  | nil (a b r : ℕ)
      (ha : delta * theta ≤ (a : ℝ))
      (hb : (k : ℝ) ^ 2 * (delta * theta) ≤ (b : ℝ))
      (hrel : r * a ≤ (k - r + 1) * b)
      (hr : 1 ≤ r) (hrk : r ≤ k - 1) :
      WooleyIterationChain k p Lambda D delta theta K 0 a b r
  | cons {n a b r aPrime bPrime rPrime : ℕ} {rho : ℝ}
      (htransition : WooleyIterationTransition
        k p Lambda D delta theta K a b r aPrime bPrime rPrime rho)
      (htail : WooleyIterationChain
        k p Lambda D delta theta K n aPrime bPrime rPrime) :
      WooleyIterationChain k p Lambda D delta theta K (n + 1) a b r

/-- If the source transition is available at every admissible node, it may
be selected finitely many times. -/
theorem wooley_iterationChain_exists
    {k p n a b r : ℕ} {Lambda D delta theta : ℝ}
    {K : ℕ → ℕ → ℕ → ℝ}
    (hstep : ∀ a b r : ℕ,
      delta * theta ≤ (a : ℝ) →
      (k : ℝ) ^ 2 * (delta * theta) ≤ (b : ℝ) →
      r * a ≤ (k - r + 1) * b →
      1 ≤ r → r ≤ k - 1 →
      WooleyIterationStep k p Lambda D delta theta K a b r)
    (ha : delta * theta ≤ (a : ℝ))
    (hb : (k : ℝ) ^ 2 * (delta * theta) ≤ (b : ℝ))
    (hrel : r * a ≤ (k - r + 1) * b)
    (hr : 1 ≤ r) (hrk : r ≤ k - 1) :
    WooleyIterationChain k p Lambda D delta theta K n a b r := by
  induction n generalizing a b r with
  | zero => exact .nil a b r ha hb hrel hr hrk
  | succ n ih =>
      obtain ⟨aPrime, bPrime, rPrime, rho,
        haPrime, hbPrime, hrelPrime, hrPrime, hrPrimeTop,
        hrho, hrhoOne, hgrowth, hupper, hceil, hweighted, hbound⟩ :=
        hstep a b r ha hb hrel hr hrk
      exact .cons
        ⟨haPrime, hbPrime, hrelPrime, hrPrime, hrPrimeTop,
          hrho, hrhoOne, hgrowth, hupper, hceil, hweighted, hbound⟩
        (ih haPrime hbPrime hrelPrime hrPrime hrPrimeTop)

/-- Endpoint and accumulated-weight ledger for (10.3)--(10.5).  The
quantity `R` is the product of the selected `rho` values. -/
theorem WooleyIterationChain.endpoint
    {k p n a b r : ℕ} {Lambda D delta theta : ℝ}
    {K : ℕ → ℕ → ℕ → ℝ}
    (hchain : WooleyIterationChain
      k p Lambda D delta theta K n a b r) :
    ∃ aFinal bFinal rFinal : ℕ, ∃ R : ℝ,
      delta * theta ≤ (aFinal : ℝ) ∧
      (k : ℝ) ^ 2 * (delta * theta) ≤ (bFinal : ℝ) ∧
      rFinal * aFinal ≤ (k - rFinal + 1) * bFinal ∧
      1 ≤ rFinal ∧ rFinal ≤ k - 1 ∧
      0 < R ∧ R ≤ 1 ∧
      (b : ℝ) ≤ R * (bFinal : ℝ) ∧
      bFinal ≤ k ^ (2 * n) * b := by
  induction hchain with
  | nil a b r ha hb hrel hr hrk =>
      refine ⟨a, b, r, 1, ha, hb, hrel, hr, hrk, by norm_num,
        le_rfl, ?_, ?_⟩
      · simp
      · simp
  | @cons n a b r aPrime bPrime rPrime rho htransition htail ih =>
      rcases htransition with
        ⟨haPrime, hbPrime, hrelPrime, hrPrime, hrPrimeTop,
          hrho, hrhoOne, hgrowth, hupper, hceil, hweighted, hbound⟩
      obtain ⟨aFinal, bFinal, rFinal, R,
        haFinal, hbFinal, hrelFinal, hrFinal, hrFinalTop,
        hRpos, hRone, hweightedTail, hscaleTail⟩ := ih
      refine ⟨aFinal, bFinal, rFinal, rho * R,
        haFinal, hbFinal, hrelFinal, hrFinal, hrFinalTop,
        mul_pos hrho hRpos, ?_, ?_, ?_⟩
      · nlinarith
      · calc
          (b : ℝ) ≤ rho * (bPrime : ℝ) := hweighted
          _ ≤ rho * (R * (bFinal : ℝ)) :=
            mul_le_mul_of_nonneg_left hweightedTail hrho.le
          _ = (rho * R) * (bFinal : ℝ) := by ring
      · calc
          bFinal ≤ k ^ (2 * n) * bPrime := hscaleTail
          _ ≤ k ^ (2 * n) * (k ^ 2 * b) :=
            Nat.mul_le_mul_left _ hupper
          _ = k ^ (2 * (n + 1)) * b := by
            rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
            simp only [mul_assoc]

#print axioms wooley_iterationChain_exists
#print axioms WooleyIterationChain.endpoint

end

end GafniTao
