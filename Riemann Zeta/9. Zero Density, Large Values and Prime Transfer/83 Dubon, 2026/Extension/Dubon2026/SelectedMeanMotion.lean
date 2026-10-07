import Dubon2026.FiniteHeightSecants
import Dubon2026.SecantLimit
import Dubon2026.JessenMean

/-! # Genuine vertical mean-motion limits at differentiable zero-free abscissae -/

namespace Dubon2026

open Filter Set
open scoped Topology

theorem tendsto_verticalLogDerivMean_selected {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 = 1) {σ d : ℝ}
    (hσ : ∀ s : ℂ, s.re = σ → dirichletSum a N s ≠ 0)
    (hd : HasDerivAt (jessenFunction a N) d σ) {H : ℝ → ℝ}
    (hH : Tendsto H atTop atTop)
    (hh : ∀ᶠ T : ℝ in atTop, ∀ s : ℂ, |s.im| = H T → dirichletSum a N s ≠ 0) :
    Tendsto (fun T => verticalLogDerivMean a N σ (H T)) atTop (𝓝 d) := by
  apply tendsto_of_approximate_secants
    (F := fun T x => verticalLogMean a N x (H T)) (G := jessenFunction a N)
    (e := fun T => Real.pi * (2 : ℝ) ^ N / H T)
    (fun x => (tendsto_verticalLogMean_jessen hN (ha.trans_ne one_ne_zero) x).comp hH)
    (hH.const_div_atTop (Real.pi * (2 : ℝ) ^ N)) hd
  · intro l hl
    filter_upwards [hH.eventually (eventually_gt_atTop (0 : ℝ)), hh] with T hT ht
    simpa only [slope_def_field] using finiteHeight_left_secant_le hN ha hl hT
      (fun y _ => hσ _ (by simp)) ht
  · intro u hu
    filter_upwards [hH.eventually (eventually_gt_atTop (0 : ℝ)), hh] with T hT ht
    simpa only [slope_def_field] using finiteHeight_right_secant_ge hN ha hu hT
      (fun y _ => hσ _ (by simp)) ht

end Dubon2026
