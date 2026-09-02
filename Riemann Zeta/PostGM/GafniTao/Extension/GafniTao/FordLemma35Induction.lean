import GafniTao.FordLemma35OneStep

/-!
# Ford Lemma 3.5: recursive exponent induction

The indexing in this file starts at zero: `fordDeltaSequence35 k r 0` is
Ford's `Delta_1`, and the step using `r n` produces `Delta_{n+2}`.
Because the audited-PNT form of Lemma 3.4 is eventual, the coefficient is
allowed to enlarge when the omitted finite prefix is repaired.  The source
exponent recursion remains literal.
-/

namespace GafniTao

noncomputable section

def fordDeltaSequence35 (k : ℕ) (r : ℕ → ℕ) : ℕ → ℝ
  | 0 => fordDeltaInitial35 k
  | n + 1 => fordDeltaZero35 k (r n) (fordDeltaSequence35 k r n)

@[simp] theorem fordDeltaSequence35_zero (k : ℕ) (r : ℕ → ℕ) :
    fordDeltaSequence35 k r 0 = fordDeltaInitial35 k := rfl

@[simp] theorem fordDeltaSequence35_succ
    (k : ℕ) (r : ℕ → ℕ) (n : ℕ) :
    fordDeltaSequence35 k r (n + 1) =
      fordDeltaZero35 k (r n) (fordDeltaSequence35 k r n) := rfl

/-- The exact source-side admissibility data needed at each recursive step.
These are arithmetic properties of Ford's chosen `r_n` and `Delta_n`, not a
moment-bound certificate. -/
def FordLemma35AdmissibleAt (k : ℕ) (r : ℕ → ℕ) (n : ℕ) : Prop :=
  4 ≤ r n ∧ r n ≤ k ∧
  0 ≤ fordY35 k (r n) (fordDeltaSequence35 k r n) ∧
  2 * fordDeltaSequence35 k r n ≤ (k : ℝ) ^ 2 - k ∧
  1 / (((k + 1 : ℕ) : ℝ)) ≤
    fordPhiStar35 k (r n) (fordDeltaSequence35 k r n)

theorem fordDeltaSequence35_moment_bound
    {k n : ℕ} {r : ℕ → ℕ} {eta omega : ℝ}
    (hk : 26 ≤ k) (hn : n + 1 ≤ k ^ 2)
    (hadm : ∀ m, m < n → FordLemma35AdmissibleAt k r m)
    (homegaLower : 1 / (3 * Real.log k) ≤ omega)
    (homegaUpper : omega ≤ 1 / 2) (hetaEq : eta = 1 + omega) :
    ∃ C : ℝ,
      FordVinogradovMomentBound ((n + 1) * k) k C
        (fordDeltaSequence35 k r n) := by
  induction n with
  | zero =>
      refine ⟨(k.factorial : ℝ), ?_⟩
      simpa using fordVinogradovMomentBound_initial k
  | succ n ih =>
      have hnprev : n + 1 ≤ k ^ 2 := by omega
      have hadmPrev : ∀ m, m < n → FordLemma35AdmissibleAt k r m := by
        intro m hm
        exact hadm m (by omega)
      obtain ⟨C, hC⟩ := ih hnprev hadmPrev
      rcases hadm n (by omega) with ⟨hr, hrk, hy, hdelta, hstar⟩
      have hks : k ≤ (n + 1) * k := by
        exact Nat.le_mul_of_pos_left k (by omega)
      obtain ⟨C', _hcoeff, hglobal⟩ := ford_lemma_3_5_one_step_global
        hk hr hrk hks hy hdelta hstar homegaLower homegaUpper hetaEq hC
      refine ⟨C', ?_⟩
      simpa [Nat.succ_eq_add_one, add_mul] using hglobal

/-- Consequence in the source's one-based notation: for every admissible
recursive exponent through `Delta_n`, a fixed coefficient exists for
`J_{nk,k}`.  This is the exponent content of Lemma 3.5 with the finite-prefix
constant honestly enlarged. -/
theorem ford_lemma_3_5_exponent_recursion
    {k n : ℕ} {r : ℕ → ℕ} {eta omega : ℝ}
    (hk : 26 ≤ k) (hnLower : 1 ≤ n) (hnUpper : n ≤ k ^ 2)
    (hadm : ∀ m, m < n - 1 → FordLemma35AdmissibleAt k r m)
    (homegaLower : 1 / (3 * Real.log k) ≤ omega)
    (homegaUpper : omega ≤ 1 / 2) (hetaEq : eta = 1 + omega) :
    ∃ C : ℝ,
      FordVinogradovMomentBound (n * k) k C
        (fordDeltaSequence35 k r (n - 1)) := by
  have hnEq : (n - 1) + 1 = n := by omega
  simpa [hnEq] using fordDeltaSequence35_moment_bound
    (k := k) (n := n - 1) (r := r) (eta := eta) (omega := omega)
    hk (by omega) hadm homegaLower homegaUpper hetaEq

#print axioms fordDeltaSequence35_moment_bound
#print axioms ford_lemma_3_5_exponent_recursion

end

end GafniTao
