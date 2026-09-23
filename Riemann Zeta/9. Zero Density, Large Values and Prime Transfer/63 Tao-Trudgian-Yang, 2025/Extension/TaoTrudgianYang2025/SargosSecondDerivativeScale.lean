import TaoTrudgianYang2025.SargosQuarticCurvature
import Mathlib.Analysis.Real.Pi.Bounds

/-! An explicit scale bound for the actual second-derivative estimate. -/

noncomputable section

open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

theorem sargos_second_derivative_scale {N L α : ℝ}
    (hN : 0 ≤ N) (hL : L ≤ N) (hα : 0 < α) (hα1 : α ≤ 1)
    (hscale : 1 ≤ N*α) :
    (L*(6*Real.pi*α)/(2*Real.pi)+2)*
      (2*Real.pi/Real.sqrt α+2*(Real.sqrt α/(2*Real.pi*α)+1)) ≤
        64*N*Real.sqrt α := by
  have hp : 0 < Real.pi := Real.pi_pos
  have hs : 0 < Real.sqrt α := Real.sqrt_pos.2 hα
  have hs1 : Real.sqrt α ≤ 1 := by nlinarith [Real.sq_sqrt hα.le,Real.sqrt_nonneg α]
  have hsq := Real.sq_sqrt hα.le
  have hpis : 1 ≤ 2*Real.pi := by linarith [Real.pi_gt_three]
  have hinv : 1 ≤ 1/Real.sqrt α := (le_div_iff₀ hs).2 (by simpa using hs1)
  have hfrac : Real.sqrt α/(2*Real.pi*α) ≤ 1/Real.sqrt α := by
    apply (div_le_div_iff₀ (by positivity : 0 < 2*Real.pi*α) hs).2
    nlinarith
  have hpi : 2*Real.pi/Real.sqrt α ≤ 8/Real.sqrt α :=
    div_le_div_of_nonneg_right (by linarith [Real.pi_lt_four]) hs.le
  have hfactor : 2*Real.pi/Real.sqrt α+
      2*(Real.sqrt α/(2*Real.pi*α)+1) ≤ 12/Real.sqrt α := by
    calc
      _ ≤ 8/Real.sqrt α+2*(1/Real.sqrt α+1/Real.sqrt α) := by linarith
      _ = _ := by ring
  have hfirst : L*(6*Real.pi*α)/(2*Real.pi)+2 ≤ 5*N*α := by
    have he : L*(6*Real.pi*α)/(2*Real.pi) = 3*L*α := by field_simp; ring
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_right hL hα.le]
  have hfirst0 : 0 ≤ 5*N*α := by positivity
  calc
    _ ≤ (5*N*α)*(12/Real.sqrt α) := mul_le_mul hfirst hfactor (by positivity) hfirst0
    _ = (60*N)*(α/Real.sqrt α) := by ring
    _ = 60*N*Real.sqrt α := by
      have hid : α/Real.sqrt α = Real.sqrt α :=
        (div_eq_iff hs.ne').2 (by nlinarith [hsq])
      rw [hid]
    _ ≤ _ := by nlinarith

end TaoTrudgianYang2025
