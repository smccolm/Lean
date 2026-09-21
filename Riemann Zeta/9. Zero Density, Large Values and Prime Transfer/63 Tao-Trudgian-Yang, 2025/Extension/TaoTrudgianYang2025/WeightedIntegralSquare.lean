import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Weighted integral Cauchy--Schwarz with visible integrability

The real inequality follows by integrating a nonnegative square and
minimizing its center. It will be applied to the actual Gaussian weight
and the norm of the finite divisor polynomial.
-/

noncomputable section

open MeasureTheory

namespace TaoTrudgianYang2025

theorem integral_weighted_sq_le
    (g f : ℝ → ℝ) (hg : ∀ x, 0 ≤ g x) (hgi : Integrable g)
    (hgf : Integrable (fun x => g x*f x))
    (hgf2 : Integrable (fun x => g x*(f x)^2))
    (hmass : 0 < ∫ x : ℝ, g x) :
    (∫ x : ℝ, g x*f x)^2 ≤ (∫ x : ℝ, g x)*(∫ x : ℝ, g x*(f x)^2) := by
  let G : ℝ := ∫ x : ℝ, g x
  let F : ℝ := ∫ x : ℝ, g x*f x
  let Q : ℝ := ∫ x : ℝ, g x*(f x)^2
  let r : ℝ := F/G
  have hnonneg : 0 ≤ ∫ x : ℝ, g x*(f x-r)^2 :=
    integral_nonneg (fun x => mul_nonneg (hg x) (sq_nonneg _))
  have heq : (fun x : ℝ => g x*(f x-r)^2) =
      (fun x : ℝ => g x*(f x)^2 - (2*r)*(g x*f x) + r^2*g x) := by
    funext x
    ring
  have hlin : Integrable (fun x : ℝ => (2*r)*(g x*f x)) := hgf.const_mul (2*r)
  have hsub : Integrable (fun x : ℝ => g x*(f x)^2-(2*r)*(g x*f x)) :=
    hgf2.sub hlin
  rw [heq,integral_add hsub (hgi.const_mul (r^2)),
    integral_sub hgf2 hlin,integral_const_mul,integral_const_mul] at hnonneg
  change 0 ≤ Q-2*r*F+r^2*G at hnonneg
  have hG : 0 < G := hmass
  have halgebra : (Q-2*r*F+r^2*G)*G = Q*G-F^2 := by
    dsimp [r]
    field_simp [hG.ne']
    ring
  have h := mul_nonneg hnonneg hG.le
  rw [halgebra] at h
  change F^2 ≤ G*Q
  nlinarith

end TaoTrudgianYang2025
