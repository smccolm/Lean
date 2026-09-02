import GafniTao.FordLemma35Quantitative
import GafniTao.FordLemma36Moment

/-!
# Ford Lemma 3.6 with a literal coefficient recurrence

The exponent sequence is Ford's canonical rounded sequence.  In contrast to
the earlier existential statement, `fordMomentCoefficient36 k n` is the
actual coefficient obtained after `n` recursive steps, including every
finite endpoint below the quantitative PNT threshold.
-/

namespace GafniTao

noncomputable section

def fordMomentCoefficient36 (k : ℕ) : ℕ → ℝ
  | 0 => (k.factorial : ℝ)
  | n + 1 => fordStepGlobalCoefficient ((n + 1) * k) k
      (fordMomentCoefficient36 k n)

@[simp] theorem fordMomentCoefficient36_zero (k : ℕ) :
    fordMomentCoefficient36 k 0 = (k.factorial : ℝ) := rfl

@[simp] theorem fordMomentCoefficient36_succ (k n : ℕ) :
    fordMomentCoefficient36 k (n + 1) =
      fordStepGlobalCoefficient ((n + 1) * k) k
        (fordMomentCoefficient36 k n) := rfl

/-- Exact-coefficient analogue of the Lemma 3.5 induction. -/
theorem fordDeltaSequence36_moment_bound_quantitative
    {k n : ℕ} (hk : 1000 ≤ k) (hn : n + 1 ≤ k ^ 2) :
    FordVinogradovMomentBound ((n + 1) * k) k
      (fordMomentCoefficient36 k n) (fordDeltaSequence36 k n) := by
  induction n with
  | zero =>
      simpa using fordVinogradovMomentBound_initial k
  | succ n ih =>
      have hnprev : n + 1 ≤ k ^ 2 := by omega
      have hmoment := ih hnprev
      have hadm := fordLemma35AdmissibleAt_rounded_all (k := k) (n := n) hk
      have hadm' :
          4 ≤ fordRSequence36 k n ∧ fordRSequence36 k n ≤ k ∧
          0 ≤ fordY35 k (fordRSequence36 k n) (fordDeltaSequence36 k n) ∧
          2 * fordDeltaSequence36 k n ≤ (k : ℝ) ^ 2 - k ∧
          1 / (((k + 1 : ℕ) : ℝ)) ≤
            fordPhiStar35 k (fordRSequence36 k n)
              (fordDeltaSequence36 k n) := by
        simpa [FordLemma35AdmissibleAt, fordDeltaSequence35_rounded_eq]
          using hadm
      rcases hadm' with ⟨hr, hrk, hy, hdelta, hstar⟩
      have hks : k ≤ (n + 1) * k :=
        Nat.le_mul_of_pos_left k (by omega)
      have hstep := ford_lemma_3_5_one_step_global_quantitative hk hr hrk hks
        hy hdelta hstar hmoment
      simpa [Nat.succ_eq_add_one, add_mul, fordRSequence36,
        fordDeltaSequence36_succ] using hstep

/-- One-based source form with the explicit recurrence coefficient. -/
theorem fordLemma36_moment_bound_quantitative
    {k n : ℕ} (hk : 1000 ≤ k) (hnLower : 1 ≤ n) (hnUpper : n ≤ k ^ 2) :
    FordVinogradovMomentBound (n * k) k
      (fordMomentCoefficient36 k (n - 1))
      (fordDeltaSequence36 k (n - 1)) := by
  have hnEq : (n - 1) + 1 = n := by omega
  simpa [hnEq] using
    (fordDeltaSequence36_moment_bound_quantitative
      (k := k) (n := n - 1) hk (by omega))

#print axioms fordDeltaSequence36_moment_bound_quantitative
#print axioms fordLemma36_moment_bound_quantitative

end

end GafniTao
