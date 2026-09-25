import Mathlib.Analysis.Real.Pi.Bounds
import GuthMaynard.SecondDerivative

/-! Explicit second-derivative scale without a long-interval assumption. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem second_derivative_scale_bound {N C α : ℝ}
    (hN : 0 ≤ N) (hC : 0 ≤ C) (hα : 0 < α) (hα1 : α ≤ 1) :
    (N*(2*Real.pi*(C*α))/(2*Real.pi)+2)*
      (2*Real.pi/Real.sqrt α+2*(Real.sqrt α/(2*Real.pi*α)+1)) ≤
        12*(C*N*Real.sqrt α+2/Real.sqrt α) := by
  have hs : 0 < Real.sqrt α := Real.sqrt_pos.2 hα
  have hsq := Real.sq_sqrt hα.le
  have hs1 : Real.sqrt α ≤ 1 := by
    nlinarith [Real.sqrt_nonneg α]
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
  have hfirst : N*(2*Real.pi*(C*α))/(2*Real.pi)+2 = C*N*α+2 := by
    field_simp
  rw [hfirst]
  calc
    _ ≤ (C*N*α+2)*(12/Real.sqrt α) :=
      mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ = 12*(C*N*(α/Real.sqrt α)+2/Real.sqrt α) := by ring
    _ = _ := by rw [Real.div_sqrt]

end TaoTrudgianYang2025
