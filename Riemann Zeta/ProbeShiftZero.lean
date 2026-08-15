import RiemannZeta.GuthMaynard.DFIErrorOptimization

open Complex Finset Set Filter Topology MeasureTheory
open scoped BigOperators Topology
open Classical

namespace RiemannZeta.GuthMaynard

theorem test_f_shift_eq_zero
    {f : ℝ → ℝ → ℂ} {X Y : ℝ} (hbox : DFILocalizedBox f X Y)
    (h : ℕ) (hY : 1 ≤ Y) (hh : 2 * X < h) :
    ∀ x : ℝ, f x (x - h) = 0 := by
  intro x
  by_contra hne
  have hmem : (x, x - (h : ℝ)) ∈
      Function.support (Function.uncurry f) := hne
  have hs := hbox.support_subset hmem
  have hypos : 0 < x - (h : ℝ) := by linarith [hs.2.1]
  have hxupper : x ≤ 2 * X := hs.1.2
  exact (not_lt_of_ge hxupper) (hh.trans (by linarith))

theorem test_central_zero
    {f : ℝ → ℝ → ℂ} {X Y : ℝ} (hbox : DFILocalizedBox f X Y)
    (h : ℕ) (hY : 1 ≤ Y) (hh : 2 * X < h)
    (a b qx qy : ℕ) :
    dfiEquation27CentralIntegral a b qx qy f h = 0 := by
  have hfzero := test_f_shift_eq_zero hbox h hY hh
  unfold dfiEquation27CentralIntegral
  simp_rw [dfiEquation27C, hfzero]
  simp

theorem test_series_zero
    {f : ℝ → ℝ → ℂ} {X Y : ℝ} (hbox : DFILocalizedBox f X Y)
    (h : ℕ) (hY : 1 ≤ Y) (hh : 2 * X < h)
    (a b : ℕ) :
    dfiEquation27CentralSeries a b h f = 0 := by
  unfold dfiEquation27CentralSeries
  simp_rw [dfiEquation27CentralSummand,
    test_central_zero hbox h hY hh a b]
  simp

theorem test_source_zero
    {f : ℝ → ℝ → ℂ} {X Y : ℝ} (hbox : DFILocalizedBox f X Y)
    (h : ℕ) (hY : 1 ≤ Y) (hh : 2 * X < h)
    (a b M N : ℕ) :
    dfiDyadicShiftedDivisorSum f a b M N (h : ℤ) = 0 := by
  unfold dfiDyadicShiftedDivisorSum
  apply Finset.sum_eq_zero
  intro m hm
  apply Finset.sum_eq_zero
  intro n hn
  by_cases hs : quadraticDivisorShift a b m n = (h : ℤ)
  · rw [if_pos hs]
    have hreal : (a : ℝ) * m - (b : ℝ) * n = h := by
      unfold quadraticDivisorShift at hs
      exact_mod_cast hs
    have hfzero := test_f_shift_eq_zero hbox h hY hh ((a : ℝ) * m)
    have hy : (a : ℝ) * m - h = (b : ℝ) * n := by linarith
    rw [hy] at hfzero
    simp [hfzero]
  · simp [hs]

end RiemannZeta.GuthMaynard
