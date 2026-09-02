import GafniTao.FordLemma35Phi

/-!
# Ford Lemma 3.5: the maximal admissible index

Ford defines `delta_0(k,r,Delta)` by taking `j` maximal subject to (3.8).
Here that choice is an explicit bounded search, so both admissibility and
maximality remain available to later estimates.
-/

namespace GafniTao

noncomputable section

/-- The maximal integer `j` in Ford's range satisfying (3.8). -/
def fordJ35 (k r : ℕ) (delta : ℝ) : ℕ :=
  Nat.findGreatest
    (fun j => 2 ≤ j ∧
      (((j - 1) * (j - 2) : ℕ) : ℝ) ≤ fordY35 k r delta)
    (9 * r / 10)

theorem fordY35_eq_source
    {k r : ℕ} (delta : ℝ) (hrk : r ≤ k) :
    fordY35 k r delta =
      2 * delta - (((k - r) * (k - r + 1) : ℕ) : ℝ) := by
  unfold fordY35
  push_cast [Nat.cast_sub hrk]
  ring

theorem two_le_nine_mul_div_ten {r : ℕ} (hr : 4 ≤ r) :
    2 ≤ 9 * r / 10 := by omega

theorem fordJ35_admissible
    {k r : ℕ} {delta : ℝ} (hr : 4 ≤ r)
    (hy : 0 ≤ fordY35 k r delta) :
    2 ≤ fordJ35 k r delta ∧
      (((fordJ35 k r delta - 1) * (fordJ35 k r delta - 2) : ℕ) : ℝ) ≤
        fordY35 k r delta := by
  unfold fordJ35
  exact Nat.findGreatest_spec
    (P := fun j => 2 ≤ j ∧
      (((j - 1) * (j - 2) : ℕ) : ℝ) ≤ fordY35 k r delta)
    (two_le_nine_mul_div_ten hr) ⟨by omega, by norm_num; exact hy⟩

theorem fordJ35_lower
    {k r : ℕ} {delta : ℝ} (hr : 4 ≤ r)
    (hy : 0 ≤ fordY35 k r delta) :
    2 ≤ fordJ35 k r delta :=
  (fordJ35_admissible hr hy).1

theorem fordJ35_upper {k r : ℕ} {delta : ℝ} :
    fordJ35 k r delta ≤ 9 * r / 10 := by
  unfold fordJ35
  exact Nat.findGreatest_le _

theorem fordJ35_ten_mul_le_nine_mul {k r : ℕ} {delta : ℝ} :
    10 * fordJ35 k r delta ≤ 9 * r := by
  have := fordJ35_upper (k := k) (r := r) (delta := delta)
  omega

theorem fordJ35_equation_3_8
    {k r : ℕ} {delta : ℝ} (hr : 4 ≤ r) (hrk : r ≤ k)
    (hy : 0 ≤ fordY35 k r delta) :
    (((fordJ35 k r delta - 1) * (fordJ35 k r delta - 2) : ℕ) : ℝ) ≤
      2 * delta - (((k - r) * (k - r + 1) : ℕ) : ℝ) := by
  rw [← fordY35_eq_source delta hrk]
  exact (fordJ35_admissible hr hy).2

/-- Maximality of Ford's chosen `j`: any larger integer still lying in the
allowed `9r/10` range violates (3.8). -/
theorem fordJ35_maximal
    {k r i : ℕ} {delta : ℝ}
    (hji : fordJ35 k r delta < i) (hi : i ≤ 9 * r / 10) :
    ¬(2 ≤ i ∧ (((i - 1) * (i - 2) : ℕ) : ℝ) ≤ fordY35 k r delta) := by
  intro hadm
  exact (Nat.findGreatest_is_greatest hji hi) hadm

/-- Ford's `delta_0(k,r,Delta)`, with the maximal source schedule unfolded. -/
def fordDeltaZero35 (k r : ℕ) (delta : ℝ) : ℝ :=
  let j := fordJ35 k r delta
  let Φ := fordCanonicalPhiSchedule k r j delta
  fordDeltaPrime34 k r delta (Φ.phi 1)

theorem fordDeltaZero35_eq
    (k r : ℕ) (delta : ℝ) :
    fordDeltaZero35 k r delta =
      fordDeltaPrime34 k r delta
        ((fordCanonicalPhiSchedule k r (fordJ35 k r delta) delta).phi 1) := rfl

#print axioms fordJ35_admissible
#print axioms fordJ35_equation_3_8
#print axioms fordJ35_maximal
#print axioms fordDeltaZero35_eq

end

end GafniTao
