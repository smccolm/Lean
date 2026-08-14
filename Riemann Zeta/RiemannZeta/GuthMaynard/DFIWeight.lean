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

/-- A chosen family of the order-dependent implicit constants in DFI
equation (2).  Keeping this profile explicit is essential for a quantitative
version of Theorem 1: rescaling `f` rescales these constants and hence the
error constant. -/
structure DFIEquation2Profile (f : ℝ → ℝ → ℂ)
    (P X Y : ℝ) (C : ℕ → ℕ → ℝ) : Prop where
  positive : ∀ i j, 0 < C i j
  bound : ∀ i j x y, 0 < x → 0 < y →
    |x| ^ i * |y| ^ j * ‖dfiMixedDeriv i j f x y‖ ≤
      C i j * (1 + x / X)⁻¹ * (1 + y / Y)⁻¹ * P ^ (i + j)

/-- Every source equation-(2) hypothesis admits one explicit derivative
constant profile.  Later error constants are defined from finitely many
entries of this profile rather than being falsely independent of `f`. -/
theorem DFIEquation2.exists_profile
    {f : ℝ → ℝ → ℂ} {P X Y : ℝ} (hf : DFIEquation2 f P X Y) :
    ∃ C : ℕ → ℕ → ℝ, DFIEquation2Profile f P X Y C := by
  choose C hC hbound using hf.derivativeBound
  exact ⟨C, ⟨hC, hbound⟩⟩

/-- The maximum equation-(2) constant required through mixed derivative
order `J` in both variables. -/
noncomputable def dfiEquation2FiniteConstant
    (C : ℕ → ℕ → ℝ) (J : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (J + 1), ∑ j ∈ Finset.range (J + 1), C i j

theorem DFIEquation2Profile.finiteConstant_pos
    {f : ℝ → ℝ → ℂ} {P X Y : ℝ} {C : ℕ → ℕ → ℝ}
    (hC : DFIEquation2Profile f P X Y C) (J : ℕ) :
    0 < dfiEquation2FiniteConstant C J := by
  unfold dfiEquation2FiniteConstant
  apply Finset.sum_pos
  · intro i hi
    exact Finset.sum_pos (fun j hj => hC.positive i j) ⟨0, by simp⟩
  · exact ⟨0, by simp⟩

/-- Every derivative constant in the square `i,j ≤ J` is bounded by the
finite profile constant used in the later DFI error theorem. -/
theorem DFIEquation2Profile.le_finiteConstant
    {f : ℝ → ℝ → ℂ} {P X Y : ℝ} {C : ℕ → ℕ → ℝ}
    (hC : DFIEquation2Profile f P X Y C)
    {i j J : ℕ} (hi : i ≤ J) (hj : j ≤ J) :
    C i j ≤ dfiEquation2FiniteConstant C J := by
  unfold dfiEquation2FiniteConstant
  have hiMem : i ∈ Finset.range (J + 1) := by simp [hi]
  have hjMem : j ∈ Finset.range (J + 1) := by simp [hj]
  exact (Finset.single_le_sum (fun k hk => (hC.positive i k).le) hjMem).trans
    (Finset.single_le_sum
      (fun k hk => Finset.sum_nonneg (fun l hl => (hC.positive k l).le)) hiMem)

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
