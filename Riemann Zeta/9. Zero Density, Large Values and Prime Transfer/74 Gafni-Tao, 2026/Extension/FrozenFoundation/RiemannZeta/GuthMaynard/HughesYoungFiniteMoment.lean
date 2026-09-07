import RiemannZeta.GuthMaynard.HughesYoungBoxScaleSplit

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators ContDiff FourierTransform Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Exact finite moment bookkeeping

This file keeps the analytic limit separate from the finite arithmetic
identity.  The latter is the object to which the diagonal estimate and the
DFI off-diagonal estimate are applied.
-/

/-- The exact finite rectangle of the opened Hughes--Young moment, already
integrated in the height variable. -/
noncomputable def hughesYoungFiniteRectIntegratedMoment
    (T c H : ℝ) (M N : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
        ∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungFiniteArithmeticTerm T t c H h k (m, n)

/-- The exact diagonal portion of one finite `(h,k)` rectangle. -/
noncomputable def hughesYoungFiniteDiagonalBox
    (T c H : ℝ) (h k M N : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
    if quadraticDivisorShift h k m n = 0 then
      ∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungFiniteArithmeticTerm T t c H h k (m, n)
    else 0

theorem hughesYoungFiniteRectIntegratedMoment_eq_diagonal_add_offDiagonal
    (T c H : ℝ) (M N : ℕ) :
    hughesYoungFiniteRectIntegratedMoment T c H M N =
      ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          (hughesYoungFiniteDiagonalBox T c H h k M N +
            hughesYoungFiniteOffDiagonalBox T c H h k M N) := by
  classical
  unfold hughesYoungFiniteRectIntegratedMoment
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro k hk
  unfold hughesYoungFiniteDiagonalBox hughesYoungFiniteOffDiagonalBox
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hs : quadraticDivisorShift h k m n = 0
  · simp [hs]
  · simp [hs]

/-- The diagonal box is the literal integrated source sum on `hm=kn`.
This form is used when regrouping by the common product. -/
theorem hughesYoungFiniteDiagonalBox_eq_source
    (T c H : ℝ) {h k M N : ℕ} (hh : 0 < h) (hk : 0 < k) :
    hughesYoungFiniteDiagonalBox T c H h k M N =
      ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
        if quadraticDivisorShift h k m n = 0 then
          divisorWeight m * divisorWeight n *
            hughesYoungIntegratedSourceWeight T c H h k
              ((h * m : ℕ) : ℝ) ((k * n : ℕ) : ℝ)
        else 0 := by
  unfold hughesYoungFiniteDiagonalBox
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hs : quadraticDivisorShift h k m n = 0
  · simp only [hs, if_true]
    exact integral_hughesYoungFiniteArithmeticTerm_eq_source T c H hh hk
  · simp [hs]

end RiemannZeta.GuthMaynard
