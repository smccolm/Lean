import TaoTrudgianYang2025.SargosQuarticDualConjugation
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! The actual reciprocal-quartic parameter substitution and its scalar derivatives. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace TaoTrudgianYang2025

def sargosQuarticParameterMap (p : ℝ × ℝ) : ℝ × ℝ :=
  (1/(4*p.1),-p.2/(16*p.1^4))

theorem sargosQuarticParameterMap_involutive {α : ℝ} (hα : α ≠ 0) (γ : ℝ) :
    sargosQuarticParameterMap (sargosQuarticParameterMap (α,γ)) = (α,γ) := by
  unfold sargosQuarticParameterMap
  apply Prod.ext <;> dsimp
  all_goals field_simp [hα]
  norm_num

theorem sargosQuarticParameterMap_injOn :
    InjOn sargosQuarticParameterMap {p : ℝ × ℝ | p.1 ≠ 0} := by
  intro p hp q hq he
  have hh := congrArg sargosQuarticParameterMap he
  rw [sargosQuarticParameterMap_involutive hp p.2,
    sargosQuarticParameterMap_involutive hq q.2] at hh
  exact hh

theorem sargosQuarticParameterMap_sextic {α : ℝ} (hα : α ≠ 0) (γ t : ℝ) :
    γ^2*t^6/(16*α^7) =
      4*(sargosQuarticParameterMap (α,γ)).2^2/
        (sargosQuarticParameterMap (α,γ)).1*t^6 := by
  unfold sargosQuarticParameterMap
  dsimp
  field_simp [hα]
  ring

theorem sargosQuarticParameter_reciprocal_deriv {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun t : ℝ => 1/(4*t)) (-1/(4*x^2)) x := by
  convert (hasDerivAt_inv hx).const_mul (1/4) using 1
  · ext t
    dsimp
    ring
  · dsimp
    ring

theorem sargosQuarticParameter_vertical_deriv (x y : ℝ) :
    HasDerivAt (fun t : ℝ => -t/(16*x^4)) (-1/(16*x^4)) y := by
  simpa only [id_eq,Pi.neg_apply,neg_div] using ((hasDerivAt_id y).neg.div_const (16*x^4))

theorem sargosQuarticParameter_jacobian_product (x : ℝ) :
    |(-1/(4*x^2))| * |(-1/(16*x^4))| = 1/(64*x^6) := by
  rw [neg_div,neg_div,abs_neg,abs_neg,
    abs_of_nonneg (by positivity : 0 ≤ 1/(4*x^2)),
    abs_of_nonneg (by positivity : 0 ≤ 1/(16*x^4))]
  ring

end TaoTrudgianYang2025
