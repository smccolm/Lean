import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

open Set
open scoped ContDiff Topology

namespace RiemannZeta.GuthMaynard

/-!
# The source weight in Duke--Friedlander--Iwaniec

This file formalizes equation (2) of Duke--Friedlander--Iwaniec, *A
quadratic divisor problem*.  The paper considers a smooth compactly supported
weight on the positive quadrant and assumes, for every pair of derivative
orders `i,j`,

`x^i y^j ‖f^(i,j)(x,y)‖ ≪_(i,j)
  (1+x/X)⁻¹ (1+y/Y)⁻¹ P^(i+j)`.

The order-dependent constant is exposed by `DFIEquation2.derivativeBound`.
It is not a uniform constant and it is not allowed to depend on `x` or `y`.
-/

/-- The mixed derivative `∂ₓ^i ∂ᵧ^j f(x,y)` occurring in DFI equation (2).
The definition differentiates first in `y` and then in `x`; smoothness makes
this agree with the paper's ordinary mixed partial derivative. -/
noncomputable def dfiMixedDeriv (i j : ℕ) (f : ℝ → ℝ → ℂ) (x y : ℝ) : ℂ :=
  iteratedDeriv i (fun x' => iteratedDeriv j (f x') y) x

@[simp]
theorem dfiMixedDeriv_zero_zero (f : ℝ → ℝ → ℂ) (x y : ℝ) :
    dfiMixedDeriv 0 0 f x y = f x y := by
  simp [dfiMixedDeriv]

/-- The literal analytic content of DFI equation (2), including the source
domain, smoothness, compact support, scale hypotheses, and the fact that the
implicit constant may depend on the two derivative orders only. -/
structure DFIEquation2 (f : ℝ → ℝ → ℂ) (P X Y : ℝ) : Prop where
  one_le_P : 1 ≤ P
  one_le_X : 1 ≤ X
  one_le_Y : 1 ≤ Y
  smooth : ContDiff ℝ ∞ (Function.uncurry f)
  compactSupport : HasCompactSupport (Function.uncurry f)
  support_pos : Function.support (Function.uncurry f) ⊆ Ioi 0 ×ˢ Ioi 0
  derivativeBound : ∀ i j : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ x y : ℝ, 0 < x → 0 < y →
      |x| ^ i * |y| ^ j * ‖dfiMixedDeriv i j f x y‖ ≤
        C * (1 + x / X)⁻¹ * (1 + y / Y)⁻¹ * P ^ (i + j)

/-- Equation (2) at derivative order `(0,0)`.  This is the pointwise decay
estimate used before differentiating the localized DFI weight. -/
theorem DFIEquation2.exists_norm_bound
    {f : ℝ → ℝ → ℂ} {P X Y : ℝ} (hf : DFIEquation2 f P X Y) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ℝ, 0 < x → 0 < y →
      ‖f x y‖ ≤ C * (1 + x / X)⁻¹ * (1 + y / Y)⁻¹ := by
  obtain ⟨C, hC, hbound⟩ := hf.derivativeBound 0 0
  refine ⟨C, hC, fun x y hx hy => ?_⟩
  simpa using hbound x y hx hy

end RiemannZeta.GuthMaynard
