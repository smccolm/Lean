import GafniTao.FordLemma36Rounding

/-! # Ford Lemma 3.6: admissibility of the rounded step -/

namespace GafniTao

noncomputable section

/-- While `Delta` lies in the range used in Ford Lemma 3.6, the rounded
choice of `r` satisfies every arithmetic entry condition of Lemma 3.5. -/
theorem fordLemma35Admissible_rounded
    {k : ℕ} {delta : ℝ} (hk : 26 ≤ k)
    (hdeltaLower : (k : ℝ) ≤ delta)
    (hdeltaUpper : delta ≤ fordDeltaInitial35 k) :
    4 ≤ fordR36 k delta ∧ fordR36 k delta ≤ k ∧
    0 ≤ fordY35 k (fordR36 k delta) delta ∧
    2 * delta ≤ (k : ℝ) ^ 2 - k ∧
    1 / (((k + 1 : ℕ) : ℝ)) ≤
      fordPhiStar35 k (fordR36 k delta) delta := by
  have hupper : delta ≤ ((k : ℝ) ^ 2 - k) / 2 := by
    simpa [fordDeltaInitial35] using hdeltaUpper
  have hr := fordR36_bounds hk hdeltaLower hupper
  exact ⟨hr.1, hr.2,
    fordY35_rounded_nonneg hk hdeltaLower hupper,
    by nlinarith,
    fordPhiStar35_rounded_lower hk hdeltaLower hupper⟩

def fordDeltaSequence36 (k : ℕ) : ℕ → ℝ
  | 0 => fordDeltaInitial35 k
  | n + 1 =>
      let delta := fordDeltaSequence36 k n
      fordDeltaZero35 k (fordR36 k delta) delta

def fordRSequence36 (k n : ℕ) : ℕ :=
  fordR36 k (fordDeltaSequence36 k n)

@[simp] theorem fordDeltaSequence36_zero (k : ℕ) :
    fordDeltaSequence36 k 0 = fordDeltaInitial35 k := rfl

@[simp] theorem fordDeltaSequence36_succ (k n : ℕ) :
    fordDeltaSequence36 k (n + 1) =
      fordDeltaZero35 k (fordRSequence36 k n) (fordDeltaSequence36 k n) := rfl

theorem fordDeltaSequence35_rounded_eq (k n : ℕ) :
    fordDeltaSequence35 k (fordRSequence36 k) n = fordDeltaSequence36 k n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [fordDeltaSequence35_succ, fordDeltaSequence36_succ, ih]

theorem fordLemma35AdmissibleAt_rounded
    {k n : ℕ} (hk : 26 ≤ k)
    (hlower : (k : ℝ) ≤ fordDeltaSequence36 k n)
    (hupper : fordDeltaSequence36 k n ≤ fordDeltaInitial35 k) :
    FordLemma35AdmissibleAt k (fordRSequence36 k) n := by
  have h := fordLemma35Admissible_rounded hk hlower hupper
  simpa [FordLemma35AdmissibleAt, fordRSequence36,
    fordDeltaSequence35_rounded_eq] using h

#print axioms fordLemma35Admissible_rounded
#print axioms fordDeltaSequence35_rounded_eq
#print axioms fordLemma35AdmissibleAt_rounded

end

end GafniTao
