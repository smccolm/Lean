import TaoTrudgianYang2025.PhaseSecondDerivativeIntegral

/-!
# Weighted second-derivative integral bounds

Integration by parts consumes the uniform primitive bound on every prefix.
The curvature bound belongs to the actual phase, not to an auxiliary carrier.
-/

noncomputable section

open Set MeasureTheory
open scoped ContDiff FourierTransform

namespace TaoTrudgianYang2025

theorem IntervalC1Bound.fourierChar_of_negative_curvature
    {f : ℝ → ℂ} {φ : ℝ → ℝ} {a b M m : ℝ} {J : Set ℝ}
    (hf : IntervalC1Bound f a b M) (hab : a ≤ b) (hm : 0 < m)
    (hJ : IsOpen J) (hsub : Icc a b ⊆ J)
    (hφ : ∀ x ∈ J, ContDiffAt ℝ 2 φ x)
    (hcurv : ∀ x ∈ J, deriv (deriv φ) x ≤ -m) :
    ‖∫ x in a..b, f x*(𝐞 (φ x) : ℂ)‖ ≤
      2*M*(2/Real.pi+2)/Real.sqrt m := by
  have h := hf.integral_mul_of_primitive_bound hab hJ hsub
    (k := fun x => (𝐞 (φ x) : ℂ))
    (by
      intro x hx
      have hc := (hφ x hx).continuousAt
      simp only [Real.fourierChar_apply]
      fun_prop)
    (B := (2/Real.pi+2)/Real.sqrt m) (by
      intro x hx
      have hs : Icc a x ⊆ J := fun y hy => hsub ⟨hy.1,hy.2.trans hx.2⟩
      exact norm_fourierCharIntegral_le_of_negative_curvature hx.1 hm
        (fun y hy => hφ y (hs hy)) (fun y hy => hcurv y (hs hy)))
  convert h using 1
  ring

end TaoTrudgianYang2025

