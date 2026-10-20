/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
import Dubon2026.CuspVerticalProfile
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold

/-! Analytic input to the actual original Hecke period pairing.
Selected from TauCetiProject/TauCeti 199786c594817a82fdd2fab04d3ae4cc5eb837d5,
with Chris Birkbeck's Apache-2.0 source contributions retained.
DUB-17/18 -> modular Galois association -> integral Hecke finiteness ->
period injectivity and adjointness -> convergent, additive cusp integrals.
Only declarations needed by that dependency chain are selected.
-/

namespace Dubon2026
open Complex Filter Topology UpperHalfPlane
open scoped Manifold

/-- The restriction of `F : ℍ → ℂ` to the positive imaginary axis, `t ↦ F (i t)`. Since
`i t` lies in `ℍ` only for `t > 0`, the restriction is extended by `0` on `t ≤ 0`. -/
noncomputable def sourceResToImagAxis (F : ℍ → ℂ) : ℝ → ℂ :=
  fun t ↦ if ht : 0 < t then F ⟨Complex.I * t, by simpa using ht⟩ else 0

/-- The characteristic equation of `sourceResToImagAxis` on its domain of interest. -/
@[simp]
theorem sourceResToImagAxis_of_pos (F : ℍ → ℂ) {t : ℝ} (ht : 0 < t) :
    sourceResToImagAxis F t = F ⟨Complex.I * t, by simpa using ht⟩ := dif_pos ht

/-- Off the positive axis the restriction is `0` by convention. -/
@[simp]
theorem sourceResToImagAxis_of_nonpos (F : ℍ → ℂ) {t : ℝ} (ht : t ≤ 0) :
    sourceResToImagAxis F t = 0 := dif_neg (not_lt.mpr ht)

/-! ### The restriction commutes with the pointwise operations

Each identity is unconditional in `t`: off the positive axis both sides are `0`.
-/

/-- The restriction of `0` is `0`. -/
@[simp]
theorem sourceResToImagAxis_zero : sourceResToImagAxis 0 = 0 := by
  funext t
  rcases le_or_gt t 0 with ht | ht <;> simp [sourceResToImagAxis_of_pos, sourceResToImagAxis_of_nonpos, ht]

/-- The restriction commutes with negation. -/
@[simp]
theorem sourceResToImagAxis_neg (F : ℍ → ℂ) : sourceResToImagAxis (-F) = -sourceResToImagAxis F := by
  funext t
  rcases le_or_gt t 0 with ht | ht <;> simp [sourceResToImagAxis_of_pos, sourceResToImagAxis_of_nonpos, ht]

/-- The restriction commutes with addition. -/
@[simp]
theorem sourceResToImagAxis_add (F G : ℍ → ℂ) :
    sourceResToImagAxis (F + G) = sourceResToImagAxis F + sourceResToImagAxis G := by
  funext t
  rcases le_or_gt t 0 with ht | ht <;> simp [sourceResToImagAxis_of_pos, sourceResToImagAxis_of_nonpos, ht]

/-- The restriction commutes with subtraction. -/
@[simp]
theorem sourceResToImagAxis_sub (F G : ℍ → ℂ) :
    sourceResToImagAxis (F - G) = sourceResToImagAxis F - sourceResToImagAxis G := by
  funext t
  rcases le_or_gt t 0 with ht | ht <;> simp [sourceResToImagAxis_of_pos, sourceResToImagAxis_of_nonpos, ht]

/-- The restriction commutes with pointwise multiplication. -/
@[simp]
theorem sourceResToImagAxis_mul (F G : ℍ → ℂ) :
    sourceResToImagAxis (F * G) = sourceResToImagAxis F * sourceResToImagAxis G := by
  funext t
  rcases le_or_gt t 0 with ht | ht <;> simp [sourceResToImagAxis_of_pos, sourceResToImagAxis_of_nonpos, ht]

/-- The restriction commutes with scalar multiplication, by any scalar acting on `ℂ` and
fixing `0` (in particular complex, real and rational scalars). The scalar generality follows
Mathlib's `Set.indicator_const_smul` and `Function.extend_smul`. -/
@[simp]
theorem sourceResToImagAxis_smul {α : Type*} [SMulZeroClass α ℂ] (c : α) (F : ℍ → ℂ) :
    sourceResToImagAxis (c • F) = c • sourceResToImagAxis F := by
  funext t
  rcases le_or_gt t 0 with ht | ht <;> simp [sourceResToImagAxis_of_pos, sourceResToImagAxis_of_nonpos, ht]

/-! ### Behaviour at `i∞` -/

/-- Along the imaginary axis, `i t` tends to `i∞` as `t → ∞`. -/
theorem sourceTendsto_imaginaryAxis :
    Tendsto (fun t : ℝ ↦ ofComplex (Complex.I * t)) atTop atImInfty := by
  simpa only [mul_comm Complex.I] using tendsto_cuspVerticalPoint

/-- **An asymptotic bound at `i∞` restricts to the imaginary axis**: if `F = O(G)` along
`atImInfty`, then `sourceResToImagAxis F = O(t ↦ G (i t))` along `atTop`. -/
theorem sourceIsBigO_resToImagAxis {E : Type*} [Norm E] {F : ℍ → ℂ} {G : ℍ → E}
    (h : F =O[atImInfty] G) :
    sourceResToImagAxis F =O[atTop] fun t ↦ G (ofComplex (Complex.I * t)) := by
  refine (h.comp_tendsto sourceTendsto_imaginaryAxis).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [Function.comp_apply, sourceResToImagAxis_of_pos _ ht,
    ofComplex_apply_of_im_pos (by simpa using ht)]

/-! ### Differentiability -/

/-- The restriction is real-differentiable at `t > 0` whenever `F ∘ ofComplex` is: the
restriction is its composite with `t ↦ i t`, so only real differentiability at the
corresponding point is used — holomorphy is not needed. -/
theorem sourceDifferentiableAt_resToImagAxis (F : ℍ → ℂ) {t : ℝ} (ht : 0 < t)
    (hF : DifferentiableAt ℝ (fun z : ℂ ↦ F (ofComplex z)) (Complex.I * t)) :
    DifferentiableAt ℝ (sourceResToImagAxis F) t := by
  have h_diff : DifferentiableAt ℝ (fun t : ℝ ↦ F (ofComplex (Complex.I * t))) t := by
    have hmul : DifferentiableAt ℝ (fun s : ℝ ↦ Complex.I * s) t :=
      Complex.ofRealCLM.differentiableAt.const_mul _
    simpa only [Function.comp_def] using hF.comp t hmul
  refine h_diff.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds ht] with s hs
  rw [sourceResToImagAxis_of_pos F hs, ofComplex_apply_of_im_pos (by simp [hs])]

/-- The manifold-differentiable case, which is how modular forms supply the hypothesis. -/
@[fun_prop]
theorem sourceDifferentiableAt_resToImagAxis_of_mDiffAt (F : ℍ → ℂ) {t : ℝ} (ht : 0 < t)
    (hF : MDiffAt F ⟨Complex.I * t, by simpa using ht⟩) :
    DifferentiableAt ℝ (sourceResToImagAxis F) t :=
  sourceDifferentiableAt_resToImagAxis F ht ((mdifferentiableAt_iff.mp hF).restrictScalars ℝ)


end Dubon2026
