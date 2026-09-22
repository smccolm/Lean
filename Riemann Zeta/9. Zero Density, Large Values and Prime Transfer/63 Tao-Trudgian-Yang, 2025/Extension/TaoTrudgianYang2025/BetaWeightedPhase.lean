import TaoTrudgianYang2025.BetaWeightedPrimitive
import TaoTrudgianYang2025.AtkinsonFirstDerivative

/-!
# Weighted Fourier-character integrals away from a stationary point

The sign alternatives and the Fourier normalization are explicit.
The result consumes the actual carrier and a genuine amplitude bound.
-/

noncomputable section

open Complex MeasureTheory Set
open scoped ContDiff FourierTransform

namespace TaoTrudgianYang2025

theorem norm_fourierCharIntegral_le_of_slope_gap
    {φ : ℝ → ℝ} {a b lam : ℝ} (hab : a ≤ b) (hlam : 0 < lam)
    (hφ : ∀ x ∈ Icc a b, ContDiffAt ℝ 2 φ x)
    (hmono : AntitoneOn (deriv φ) (Icc a b))
    (hgap : (∀ x ∈ Icc a b, lam ≤ deriv φ x) ∨
      (∀ x ∈ Icc a b, deriv φ x ≤ -lam)) :
    ‖∫ x in a..b, (𝐞 (φ x) : ℂ)‖ ≤ 1/(lam*Real.pi) := by
  have he : (fun x => Complex.exp (2*Real.pi*I*(φ x : ℂ))) =
      (fun x => (𝐞 (φ x) : ℂ)) := by
    funext x
    simp only [Real.fourierChar_apply]
    congr 1
    push_cast
    ring
  rw [← he]
  rcases hgap with hp | hn
  · exact norm_phaseIntegral_le_of_positive_slope hab hlam hφ hp hmono
  · exact norm_phaseIntegral_le_of_negative_slope hab hlam hφ hn hmono

theorem IntervalC1Bound.fourierChar_of_slope_gap
    {f : ℝ → ℂ} {φ : ℝ → ℝ} {a b M lam : ℝ} {J : Set ℝ}
    (hf : IntervalC1Bound f a b M) (hab : a ≤ b) (hlam : 0 < lam)
    (hJ : IsOpen J) (hsub : Icc a b ⊆ J)
    (hφ : ∀ x ∈ J, ContDiffAt ℝ 2 φ x)
    (hmono : AntitoneOn (deriv φ) J)
    (hgap : (∀ x ∈ J, lam ≤ deriv φ x) ∨
      (∀ x ∈ J, deriv φ x ≤ -lam)) :
    ‖∫ x in a..b, f x*(𝐞 (φ x) : ℂ)‖ ≤ 2*M/(lam*Real.pi) := by
  have h := hf.integral_mul_of_primitive_bound hab hJ hsub
    (k := fun x => (𝐞 (φ x) : ℂ))
    (by
      intro x hx
      have hc := (hφ x hx).continuousAt
      simp only [Real.fourierChar_apply]
      fun_prop)
    (B := 1/(lam*Real.pi)) (by
      intro x hx
      have hsubx : Icc a x ⊆ J := fun y hy => hsub ⟨hy.1,hy.2.trans hx.2⟩
      apply norm_fourierCharIntegral_le_of_slope_gap hx.1 hlam
        (fun y hy => hφ y (hsubx hy))
        (fun y hy z hz hyz => hmono (hsubx hy) (hsubx hz) hyz)
      rcases hgap with hp | hn
      · exact Or.inl (fun y hy => hp y (hsubx hy))
      · exact Or.inr (fun y hy => hn y (hsubx hy)))
  convert h using 1
  ring

end TaoTrudgianYang2025
