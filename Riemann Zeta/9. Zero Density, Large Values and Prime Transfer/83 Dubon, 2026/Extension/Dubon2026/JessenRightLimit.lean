import Dubon2026.JessenStieltjes
import Dubon2026.ConvexAsymptotes

/-! # Right-end asymptotics of the actual normalized Jessen function -/

namespace Dubon2026

open Set Filter
open scoped Topology

theorem tendsto_coefficientEnergy_atTop (a : ℕ → ℂ) {N : ℕ} (hN : 1 ≤ N) :
    Tendsto (coefficientEnergy a N) atTop (𝓝 (‖a 1‖ ^ 2)) := by
  change Tendsto (fun σ => coefficientEnergy a N σ) atTop (𝓝 (‖a 1‖ ^ 2))
  have hterm (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      Tendsto (fun σ : ℝ => ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)) atTop
        (𝓝 (if n = 1 then ‖a n‖ ^ 2 else 0)) := by
    by_cases h : n = 1
    · subst n
      simp only [Nat.cast_one, Real.one_rpow, mul_one, ite_true]
      exact tendsto_const_nhds
    · have hn' : 1 < n := by have := (Finset.mem_Icc.mp hn).1; omega
      have hnR : (1 : ℝ) < n := by exact_mod_cast hn'
      have hr := (tendsto_rpow_atBot_of_base_gt_one (n : ℝ) hnR).comp
        (tendsto_id.const_mul_atTop_of_neg (show (-2 : ℝ) < 0 by norm_num))
      simpa only [if_neg h, mul_zero] using hr.const_mul (‖a n‖ ^ 2)
  simpa [coefficientEnergy, hN] using tendsto_finsetSum (Finset.Icc 1 N) hterm

theorem tendsto_jessenFunction_atTop {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 = 1) :
    Tendsto (jessenFunction a N) atTop (𝓝 0) := by
  have he : Tendsto (coefficientEnergy a N) atTop (𝓝 1) := by
    simpa only [ha, norm_one, one_pow] using tendsto_coefficientEnergy_atTop a hN
  have hu : Tendsto (fun σ => Real.log (coefficientEnergy a N σ) / 2) atTop (𝓝 0) := by
    simpa only [Real.log_one, zero_div] using
      (Real.continuousAt_log one_ne_zero).tendsto.comp he |>.div_const 2
  exact tendsto_const_nhds.squeeze hu (fun σ => (jessenFunction_bounds hN ha σ).1)
    (fun σ => (jessenFunction_bounds hN ha σ).2)

theorem tendsto_jessen_derivatives_atTop {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 = 1) :
    Tendsto (fun x => derivWithin (jessenFunction a N) (Iio x) x) atTop (𝓝 0) ∧
      Tendsto (fun x => derivWithin (jessenFunction a N) (Ioi x) x) atTop (𝓝 0) := by
  apply tendsto_convex_derivatives_atTop (convexOn_jessenFunction hN (ha.trans_ne one_ne_zero))
  simpa only [zero_mul, sub_zero] using tendsto_jessenFunction_atTop hN ha

theorem tendsto_jessenStieltjes_atTop {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 = 1) :
    Tendsto (jessenStieltjes hN (ha.trans_ne one_ne_zero)) atTop (𝓝 0) := by
  change Tendsto (fun x => jessenStieltjes hN (ha.trans_ne one_ne_zero) x) atTop (𝓝 0)
  simpa only [jessenStieltjes_apply] using (tendsto_jessen_derivatives_atTop hN ha).2

end Dubon2026
