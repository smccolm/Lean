import GafniTao.FordLemma65OneStep
import GafniTao.FordLemma35InitialMoment

/-!
# Ford Lemma 6.5: iterated exponent decay

The source iteration repeatedly replaces `Delta` by
`Delta (1-1/k)` while increasing the moment index by `k`.  Coefficients are
allowed to enlarge at each step; they remain fixed with respect to the
endpoint and therefore have no effect on the zeta exponent.
-/

namespace GafniTao

noncomputable section

def fordDeltaSequence65 (k : ℕ) : ℕ → ℝ
  | 0 => fordDeltaInitial35 k
  | n + 1 => fordDelta65 k (fordDeltaSequence65 k n)

@[simp] theorem fordDeltaSequence65_zero (k : ℕ) :
    fordDeltaSequence65 k 0 = fordDeltaInitial35 k := rfl

@[simp] theorem fordDeltaSequence65_succ (k n : ℕ) :
    fordDeltaSequence65 k (n + 1) =
      fordDelta65 k (fordDeltaSequence65 k n) := rfl

theorem fordDeltaSequence65_closed
    (k n : ℕ) :
    fordDeltaSequence65 k n =
      fordDeltaInitial35 k * (1 - 1 / (k : ℝ)) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [fordDeltaSequence65_succ, ih]
      unfold fordDelta65
      rw [pow_succ]
      ring

/-- Every term of the Lemma-6.5 sequence has a genuine all-endpoint
Vinogradov moment estimate. -/
theorem fordDeltaSequence65_moment_bound
    {k n : ℕ} (hk : 4 ≤ k) :
    ∃ C : ℝ,
      FordVinogradovMomentBound ((n + 1) * k) k C
        (fordDeltaSequence65 k n) := by
  induction n with
  | zero =>
      refine ⟨(k.factorial : ℝ), ?_⟩
      simpa using fordVinogradovMomentBound_initial k
  | succ n ih =>
      obtain ⟨C, hC⟩ := ih
      have hs : 2 ≤ (n + 1) * k := by
        have : k ≤ (n + 1) * k := Nat.le_mul_of_pos_left k (by omega)
        omega
      obtain ⟨C', _hcoeff, hstep⟩ :=
        ford_lemma_6_5_one_step_global hk hs hC
      refine ⟨C', ?_⟩
      simpa [Nat.succ_eq_add_one, add_mul] using hstep

/-- One-based source form: a moment estimate for `J_{nk,k}` with the exact
geometric exponent after `n-1` applications. -/
theorem ford_lemma_6_5_iterated
    {k n : ℕ} (hk : 4 ≤ k) (hn : 1 ≤ n) :
    ∃ C : ℝ,
      FordVinogradovMomentBound (n * k) k C
        (fordDeltaInitial35 k * (1 - 1 / (k : ℝ)) ^ (n - 1)) := by
  have hindex : (n - 1) + 1 = n := by omega
  obtain ⟨C, hC⟩ := fordDeltaSequence65_moment_bound
    (k := k) (n := n - 1) hk
  refine ⟨C, ?_⟩
  simpa [hindex, fordDeltaSequence65_closed] using hC

#print axioms fordDeltaSequence65_closed
#print axioms fordDeltaSequence65_moment_bound
#print axioms ford_lemma_6_5_iterated

end

end GafniTao
