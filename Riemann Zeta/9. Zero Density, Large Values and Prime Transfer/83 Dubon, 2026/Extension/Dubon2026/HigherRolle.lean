import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Order.Fin.Basic

/-! # Repeated Rolle theorem for the logarithmic sublevel estimates -/

namespace Dubon2026

open Set
open scoped ContDiff

theorem exists_iteratedDeriv_eq_zero_of_ordered_zeros (n : ℕ) (f : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (x : Fin (n + 1) → ℝ) (hx : StrictMono x)
    (hz : ∀ i, f (x i) = 0) :
    ∃ t ∈ Icc (x 0) (x (Fin.last n)), iteratedDeriv n f t = 0 := by
  induction n generalizing f with
  | zero =>
    refine ⟨x 0, ?_, ?_⟩
    · simp
    · simpa only [iteratedDeriv_zero] using hz 0
  | succ n ih =>
    have hbetween (i : Fin (n + 1)) :
        ∃ t ∈ Ioo (x i.castSucc) (x i.succ), deriv f t = 0 := by
      apply exists_deriv_eq_zero (hx Fin.castSucc_lt_succ) hf.continuous.continuousOn
      rw [hz, hz]
    choose y hy hyzero using hbetween
    have hymono : StrictMono y := by
      intro i j hij
      have hmiddle : x i.succ ≤ x j.castSucc := hx.monotone (by simpa using hij)
      exact (hy i).2.trans_le hmiddle |>.trans (hy j).1
    obtain ⟨t, ht, hzero⟩ := ih (deriv f) (contDiff_infty_iff_deriv.mp hf).2 y hymono hyzero
    refine ⟨t, ⟨?_, ?_⟩, ?_⟩
    · exact (hy 0).1.le.trans ht.1
    · exact ht.2.trans (hy (Fin.last n)).2.le
    · simpa only [iteratedDeriv_succ'] using hzero

end Dubon2026
