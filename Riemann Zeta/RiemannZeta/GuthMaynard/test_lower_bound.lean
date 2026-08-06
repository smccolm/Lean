import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Instances.Complex

open Complex

namespace RiemannZeta.GuthMaynard

lemma zeta_lower_bound_test : ∃ (c_0 : ℝ), c_0 > 0 ∧
    ∀ (t : ℝ), t ≥ 1 →
      c_0 ≤ ‖riemannZeta (2 + I * (t + 1/2))‖ := by
  use 1 / 4
  constructor
  · norm_num
  · intro t ht
    have hRe : (2 + I * (t + 1/2)).re > 1 := by
      simp only [add_re, ofReal_re, mul_re, I_re, zero_mul, I_im]
      norm_num
    have hZeta := zeta_eq_tsum_one_div_nat_add_one_cpow hRe
    rw [hZeta]
    sorry

end RiemannZeta.GuthMaynard
