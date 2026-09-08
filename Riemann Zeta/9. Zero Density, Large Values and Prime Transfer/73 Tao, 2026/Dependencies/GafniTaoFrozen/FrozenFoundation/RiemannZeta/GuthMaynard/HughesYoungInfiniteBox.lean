import RiemannZeta.GuthMaynard.HughesYoungInfiniteDyadic
import RiemannZeta.GuthMaynard.HughesYoungBoxScaleSplit

open Complex Finset Filter MeasureTheory Set Topology
open scoped BigOperators ContDiff FourierTransform Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Exact finite realization of each infinite Hughes--Young dyadic box

Every cutoff in equation (69) is compactly supported.  Consequently each
box of the infinite AFE series is literally a finite DFI box.  The natural
bound below is deliberately independent of the reduced coefficients.
-/

/-- The `hughesYoungFullDyadicBound` definition used by the source-facing construction in `HughesYoungInfiniteBox`. -/
noncomputable def hughesYoungFullDyadicBound (i : ℕ) : ℕ :=
  Nat.ceil (2 * hughesYoungFullDyadicScale i)

theorem hughesYoungFullDyadicBound_pos (i : ℕ) :
    0 < hughesYoungFullDyadicBound i := by
  unfold hughesYoungFullDyadicBound
  exact Nat.ceil_pos.mpr
    (mul_pos (by norm_num) (hughesYoungFullDyadicScale_pos i))

theorem two_mul_hughesYoungFullDyadicScale_le_bound (i : ℕ) :
    2 * hughesYoungFullDyadicScale i ≤
      (hughesYoungFullDyadicBound i : ℝ) := by
  unfold hughesYoungFullDyadicBound
  exact Nat.le_ceil _

theorem hughesYoungFullDyadicCutoff_eq_zero_of_bound_lt
    {a m i : ℕ} (ha : 0 < a) (hm : hughesYoungFullDyadicBound i < m) :
    hughesYoungFullDyadicCutoff i ((a * m : ℕ) : ℝ) = 0 := by
  by_contra hne
  have hsupp := support_hughesYoungDyadicCutoffAt_subset
    (hughesYoungFullDyadicScale_pos i) hne
  have haOne : 1 ≤ a := ha
  have hmNat : m ≤ a * m := by
    simpa only [one_mul] using Nat.mul_le_mul_right m haOne
  have hmReal : (m : ℝ) ≤ ((a * m : ℕ) : ℝ) := by exact_mod_cast hmNat
  have hboundReal : (hughesYoungFullDyadicBound i : ℝ) < (m : ℝ) := by
    exact_mod_cast hm
  linarith [hsupp.2, two_mul_hughesYoungFullDyadicScale_le_bound i]

/-- One complete dyadic term after the smooth height average. -/
noncomputable def hughesYoungFullDyadicIntegratedTerm
    (T c H : ℝ) (h k i j : ℕ) (p : ℕ × ℕ) : ℂ :=
  ∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
    hughesYoungFullDyadicArithmeticTerm T t c H h k i j p

/-- A complete dyadic box of the infinite opened AFE, already averaged in
the height variable. -/
noncomputable def hughesYoungFullDyadicIntegratedBox
    (T c H : ℝ) (h k i j : ℕ) : ℂ :=
  ∑' p : ℕ × ℕ,
    hughesYoungFullDyadicIntegratedTerm T c H h k i j p

theorem hughesYoungFullDyadicIntegratedTerm_eq_source
    (T c H : ℝ) {h k i j m n : ℕ} (hh : 0 < h) (hk : 0 < k) :
    hughesYoungFullDyadicIntegratedTerm T c H h k i j (m, n) =
      (hughesYoungFullDyadicCutoff i
          ((hughesYoungReducedLeft h k * m : ℕ) : ℝ) : ℂ) *
        (hughesYoungFullDyadicCutoff j
          ((hughesYoungReducedRight h k * n : ℕ) : ℝ) : ℂ) *
        divisorWeight m * divisorWeight n *
        hughesYoungIntegratedSourceWeight T c H h k
          ((h * m : ℕ) : ℝ) ((k * n : ℕ) : ℝ) := by
  unfold hughesYoungFullDyadicIntegratedTerm
    hughesYoungFullDyadicArithmeticTerm
  rw [show (fun t : ℝ => (hughesYoungHeightWeight T t : ℂ) *
      ((hughesYoungFullDyadicCutoff i
          ((hughesYoungReducedLeft h k * m : ℕ) : ℝ) : ℂ) *
        (hughesYoungFullDyadicCutoff j
          ((hughesYoungReducedRight h k * n : ℕ) : ℝ) : ℂ) *
        hughesYoungFiniteArithmeticTerm T t c H h k (m, n))) =
      fun t : ℝ =>
        ((hughesYoungFullDyadicCutoff i
            ((hughesYoungReducedLeft h k * m : ℕ) : ℝ) : ℂ) *
          (hughesYoungFullDyadicCutoff j
            ((hughesYoungReducedRight h k * n : ℕ) : ℝ) : ℂ)) *
        ((hughesYoungHeightWeight T t : ℂ) *
          hughesYoungFiniteArithmeticTerm T t c H h k (m, n)) by
    funext t
    ring]
  rw [integral_const_mul,
    integral_hughesYoungFiniteArithmeticTerm_eq_source T c H hh hk]
  ring

theorem hughesYoungFullDyadicIntegratedTerm_eq_zero_of_left_bound
    (T c H : ℝ) {h k i j m n : ℕ} (hh : 0 < h)
    (hm : hughesYoungFullDyadicBound i < m) :
    hughesYoungFullDyadicIntegratedTerm T c H h k i j (m, n) = 0 := by
  unfold hughesYoungFullDyadicIntegratedTerm
    hughesYoungFullDyadicArithmeticTerm
  rw [hughesYoungFullDyadicCutoff_eq_zero_of_bound_lt
    (hughesYoungReducedLeft_pos (k := k) hh) hm]
  simp

theorem hughesYoungFullDyadicIntegratedTerm_eq_zero_of_right_bound
    (T c H : ℝ) {h k i j m n : ℕ} (hh : 0 < h) (hk : 0 < k)
    (hn : hughesYoungFullDyadicBound j < n) :
    hughesYoungFullDyadicIntegratedTerm T c H h k i j (m, n) = 0 := by
  unfold hughesYoungFullDyadicIntegratedTerm
    hughesYoungFullDyadicArithmeticTerm
  rw [hughesYoungFullDyadicCutoff_eq_zero_of_bound_lt
    (hughesYoungReducedRight_pos hh hk) hn]
  simp

theorem hughesYoungFullDyadicIntegratedTerm_eq_zero_of_left_zero
    (T c H : ℝ) (h k i j n : ℕ) :
    hughesYoungFullDyadicIntegratedTerm T c H h k i j (0, n) = 0 := by
  unfold hughesYoungFullDyadicIntegratedTerm
  simp only [hughesYoungFiniteArithmeticTerm_eq_zero_of_left,
    hughesYoungFullDyadicArithmeticTerm, mul_zero, integral_zero]

theorem hughesYoungFullDyadicIntegratedTerm_eq_zero_of_right_zero
    (T c H : ℝ) (h k i j m : ℕ) :
    hughesYoungFullDyadicIntegratedTerm T c H h k i j (m, 0) = 0 := by
  unfold hughesYoungFullDyadicIntegratedTerm
  simp only [hughesYoungFiniteArithmeticTerm_eq_zero_of_right,
    hughesYoungFullDyadicArithmeticTerm, mul_zero, integral_zero]

theorem hughesYoungFullDyadicCutoff_physical_left
    {h k m i : ℕ} (hh : 0 < h) :
    hughesYoungDyadicCutoffAt
        ((hughesYoungCommonDivisor h k : ℝ) *
          hughesYoungFullDyadicScale i) ((h * m : ℕ) : ℝ) =
      hughesYoungFullDyadicCutoff i
        ((hughesYoungReducedLeft h k * m : ℕ) : ℝ) := by
  have hd : (0 : ℝ) < hughesYoungCommonDivisor h k := by
    exact_mod_cast hughesYoungCommonDivisor_pos hh
  have hfactor : (h : ℝ) =
      (hughesYoungCommonDivisor h k : ℝ) *
        (hughesYoungReducedLeft h k : ℝ) := by
    exact_mod_cast (hughesYoungCommonDivisor_mul_reducedLeft h k).symm
  unfold hughesYoungFullDyadicCutoff
  push_cast
  rw [hfactor]
  convert hughesYoungDyadicCutoffAt_mul_cancel
    (d := (hughesYoungCommonDivisor h k : ℝ))
    (X := hughesYoungFullDyadicScale i)
    (x := (hughesYoungReducedLeft h k : ℝ) * (m : ℝ)) hd using 1
  all_goals ring_nf

theorem hughesYoungFullDyadicCutoff_physical_right
    {h k n j : ℕ} (hh : 0 < h) :
    hughesYoungDyadicCutoffAt
        ((hughesYoungCommonDivisor h k : ℝ) *
          hughesYoungFullDyadicScale j) ((k * n : ℕ) : ℝ) =
      hughesYoungFullDyadicCutoff j
        ((hughesYoungReducedRight h k * n : ℕ) : ℝ) := by
  have hd : (0 : ℝ) < hughesYoungCommonDivisor h k := by
    exact_mod_cast hughesYoungCommonDivisor_pos hh
  have hfactor : (k : ℝ) =
      (hughesYoungCommonDivisor h k : ℝ) *
        (hughesYoungReducedRight h k : ℝ) := by
    exact_mod_cast (hughesYoungCommonDivisor_mul_reducedRight h k).symm
  unfold hughesYoungFullDyadicCutoff
  push_cast
  rw [hfactor]
  convert hughesYoungDyadicCutoffAt_mul_cancel
    (d := (hughesYoungCommonDivisor h k : ℝ))
    (X := hughesYoungFullDyadicScale j)
    (x := (hughesYoungReducedRight h k : ℝ) * (n : ℝ)) hd using 1
  all_goals ring_nf

theorem hughesYoungFullDyadicIntegratedBox_eq_finiteSum
    (T c H : ℝ) {h k i j : ℕ} (hh : 0 < h) (hk : 0 < k) :
    hughesYoungFullDyadicIntegratedBox T c H h k i j =
      ∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound i),
        ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound j),
          hughesYoungFullDyadicIntegratedTerm T c H h k i j (m, n) := by
  unfold hughesYoungFullDyadicIntegratedBox
  rw [tsum_eq_sum (s := Finset.Icc (1, 1)
    (hughesYoungFullDyadicBound i, hughesYoungFullDyadicBound j))]
  · rw [Finset.Icc_prod_def, Finset.sum_product]
  · intro p hp
    rcases p with ⟨m, n⟩
    by_cases hm0 : m = 0
    · subst m
      exact hughesYoungFullDyadicIntegratedTerm_eq_zero_of_left_zero
        T c H h k i j n
    by_cases hn0 : n = 0
    · subst n
      exact hughesYoungFullDyadicIntegratedTerm_eq_zero_of_right_zero
        T c H h k i j m
    have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    by_cases hm : m ≤ hughesYoungFullDyadicBound i
    · by_cases hn : n ≤ hughesYoungFullDyadicBound j
      · exfalso
        apply hp
        simp [Prod.le_def, hm1, hn1, hm, hn]
      · exact hughesYoungFullDyadicIntegratedTerm_eq_zero_of_right_bound
          T c H hh hk (Nat.lt_of_not_ge hn)
    · exact hughesYoungFullDyadicIntegratedTerm_eq_zero_of_left_bound
        T c H hh (Nat.lt_of_not_ge hm)

/-- The diagonal portion of one complete smooth dyadic box. -/
noncomputable def hughesYoungFullDyadicDiagonalBox
    (T c H : ℝ) (h k i j : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound i),
    ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound j),
      if quadraticDivisorShift h k m n = 0 then
        hughesYoungFullDyadicIntegratedTerm T c H h k i j (m, n)
      else 0

/-- Every complete infinite-series box is exactly its diagonal part plus
the literal finite off-diagonal DFI box at the same two smooth scales. -/
theorem hughesYoungFullDyadicIntegratedBox_eq_diagonal_add_offDiagonal
    (T c H : ℝ) {h k i j : ℕ} (hh : 0 < h) (hk : 0 < k) :
    hughesYoungFullDyadicIntegratedBox T c H h k i j =
      hughesYoungFullDyadicDiagonalBox T c H h k i j +
        hughesYoungLocalizedOffDiagonalBox T c H
          (hughesYoungFullDyadicScale i)
          (hughesYoungFullDyadicScale j) h k
          (hughesYoungFullDyadicBound i)
          (hughesYoungFullDyadicBound j) := by
  rw [hughesYoungFullDyadicIntegratedBox_eq_finiteSum T c H hh hk]
  unfold hughesYoungFullDyadicDiagonalBox
    hughesYoungLocalizedOffDiagonalBox
    finiteQuadraticDivisorOffDiagonal
    hughesYoungPreReducedIntegratedBoxWeight
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [hughesYoungFullDyadicIntegratedTerm_eq_source T c H hh hk]
  dsimp only
  rw [
    hughesYoungFullDyadicCutoff_physical_left hh,
    hughesYoungFullDyadicCutoff_physical_right hh]
  by_cases hs : quadraticDivisorShift h k m n = 0
  · simp [hs]
  · simp only [hs, if_false]
    ring

end RiemannZeta.GuthMaynard
