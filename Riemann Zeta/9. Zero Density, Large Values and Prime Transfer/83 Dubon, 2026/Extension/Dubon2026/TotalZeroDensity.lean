import Dubon2026.RegularZeroDensity
import Dubon2026.RegularAbscissae
import Dubon2026.TotalVerticalZeros
import Dubon2026.JessenMass

/-! # The full-height total zero count has the source's actual supported-length density -/

namespace Dubon2026

open Filter Set
open scoped Topology

theorem tendsto_totalVerticalZeroDensity {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 = 1) :
    Tendsto (fun T => (totalVerticalZeroCount a N hN (ha.trans_ne one_ne_zero) T : ℝ) /
      (2 * T)) atTop (𝓝 (Real.log (lastIndex a N) / (2 * Real.pi))) := by
  have ha0 := ha.trans_ne one_ne_zero
  obtain ⟨l, u, hlu, hb⟩ := exists_zero_containing_vertical_strip hN ha0
  have hleft (v : ℝ) := exists_regular_abscissa hN ha0
    (show min l (-v) - 1 < min l (-v) by linarith)
  have hright (v : ℝ) := exists_regular_abscissa hN ha0
    (show max u v < max u v + 1 by linarith)
  choose L hL hLzero hLder hLcont using hleft
  choose U hU hUzero hUder hUcont using hright
  have hLl (v : ℝ) : L v < l := (hL v).2.trans_le (min_le_left _ _)
  have huU (v : ℝ) : u < U v := lt_of_le_of_lt (le_max_left _ _) (hU v).1
  have hbound (v : ℝ) (s : ℂ) (hs : dirichletSum a N s = 0) :
      L v < s.re ∧ s.re < U v := ⟨(hLl v).trans (hb s hs).1, (hb s hs).2.trans (huU v)⟩
  have hlim (v : ℝ) :
      Tendsto (fun T => (totalVerticalZeroCount a N hN ha0 T : ℝ) / (2 * T)) atTop
        (𝓝 ((derivWithin (jessenFunction a N) (Ioi (U v)) (U v) -
          derivWithin (jessenFunction a N) (Ioi (L v)) (L v)) / (2 * Real.pi))) := by
    simpa only [totalVerticalZeroCount_eq_strip hN ha0 (hbound v)] using
      tendsto_zeroDensity_regular_endpoints hN ha ((hLl v).trans (hlu.trans (huU v))).le
        (hLzero v) (hUzero v) (hLder v) (hUder v)
  have hbot : Tendsto L atTop atBot := tendsto_atBot_mono' _
    (Filter.Eventually.of_forall fun v => ((hL v).2.trans_le (min_le_right _ _)).le)
    tendsto_neg_atTop_atBot
  have htop : Tendsto U atTop atTop := tendsto_atTop_mono' _
    (Filter.Eventually.of_forall fun v => (lt_of_le_of_lt (le_max_right _ _) (hU v).1).le)
    tendsto_id
  have he (v : ℝ) := tendsto_nhds_unique (hlim v) (hlim 0)
  have hs := (((tendsto_jessen_derivatives_atTop hN ha).2.comp htop).sub
    ((tendsto_jessen_derivatives_atBot hN ha0).2.comp hbot)).div_const (2 * Real.pi)
  simp only [zero_sub, neg_neg] at hs
  have heq : (derivWithin (jessenFunction a N) (Ioi (U 0)) (U 0) -
      derivWithin (jessenFunction a N) (Ioi (L 0)) (L 0)) / (2 * Real.pi) =
        Real.log (lastIndex a N) / (2 * Real.pi) := by
    apply tendsto_nhds_unique (l := atTop (α := ℝ)) tendsto_const_nhds
    simpa only [Function.comp_def, he] using hs
  rw [← heq]
  exact hlim 0

end Dubon2026
