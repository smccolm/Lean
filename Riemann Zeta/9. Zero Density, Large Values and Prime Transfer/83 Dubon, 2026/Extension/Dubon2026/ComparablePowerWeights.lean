import Dubon2026.DyadicPrimes

/-! # Uniform comparison of real power weights on the actual dyadic prime interval -/

namespace Dubon2026

open Set Filter

theorem abs_log_div_le_log_two {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxy : x ≤ 2 * y) (hyx : y ≤ 2 * x) : |Real.log (x / y)| ≤ Real.log 2 := by
  have hratio : (1 / 2 : ℝ) ≤ x / y ∧ x / y ≤ 2 := by
    constructor
    · apply (le_div_iff₀ hy).mpr
      linarith
    · exact (div_le_iff₀ hy).mpr (by linarith)
  apply abs_le.mpr
  constructor
  · have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hratio.1
    simpa only [Real.log_div one_ne_zero (by norm_num : (2 : ℝ) ≠ 0), Real.log_one,
      zero_sub] using hh
  · exact Real.log_le_log (div_pos hx hy) hratio.2

theorem real_power_ratio_bounds {x y s M : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxy : x ≤ 2 * y) (hyx : y ≤ 2 * x) (hs : |s| ≤ M) :
    Real.exp (-(M * Real.log 2)) ≤ x ^ s / y ^ s ∧
      x ^ s / y ^ s ≤ Real.exp (M * Real.log 2) := by
  have hlog := abs_log_div_le_log_two hx hy hxy hyx
  have hb : |Real.log (x / y) * s| ≤ M * Real.log 2 := by
    rw [abs_mul, mul_comm M]
    exact mul_le_mul hlog hs (abs_nonneg _) (Real.log_nonneg (by norm_num))
  rw [← Real.div_rpow hx.le hy.le, Real.rpow_def_of_pos (div_pos hx hy)]
  exact ⟨Real.exp_le_exp.mpr (abs_le.mp hb).1, Real.exp_le_exp.mpr (abs_le.mp hb).2⟩

/-- The literal H2 max/min comparison for the zeta coefficients, uniform on each compact interval. -/
theorem primeCoefficientComparability_one (α : ℝ) :
    PrimeCoefficientComparability (fun _ => (1 : ℂ)) dyadicPrimes α := by
  intro l u _ _
  let M := max |l| |u|
  let K := Real.exp (M * Real.log 2)
  have hM : 0 ≤ M := (abs_nonneg l).trans (le_max_left _ _)
  have hK : 1 ≤ K := Real.one_le_exp_iff.mpr (mul_nonneg hM (Real.log_nonneg (by norm_num)))
  refine ⟨K, hK, Eventually.of_forall ?_⟩
  intro N σ hσ p hp q hq
  have hp' := mem_dyadicPrimes.mp hp
  have hq' := mem_dyadicPrimes.mp hq
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp'.1.pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq'.1.pos
  have hpN : (p : ℝ) ≤ N := by exact_mod_cast hp'.2.2
  have hqN : (q : ℝ) ≤ N := by exact_mod_cast hq'.2.2
  have hs : |-σ| ≤ M := by
    rw [abs_neg]
    apply abs_le.mpr
    have hl := (neg_abs_le l).trans hσ.1
    have hu := hσ.2.trans (le_abs_self u)
    have hMl : |l| ≤ M := le_max_left _ _
    have hMu : |u| ≤ M := le_max_right _ _
    constructor <;> linarith
  have hb := real_power_ratio_bounds hp0 hq0 (by linarith [hq'.2.1])
    (by linarith [hp'.2.1]) hs
  simpa only [norm_one, one_mul, K, Real.exp_neg] using hb

end Dubon2026
