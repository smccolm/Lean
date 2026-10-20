/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.Complex.Convex

/-! A primitive for the actual holomorphic period integrand on the upper half-plane.
Selected from TauCetiProject/TauCeti 199786c594817a82fdd2fab04d3ae4cc5eb837d5.
Exact dependency: DUB-17 Theorem 2.6 and DUB-18 Corollary 8.2 -> modular Galois
association -> integral Hecke finiteness -> injective original period pairing ->
additive cusp integrals. A common holomorphic primitive supplies the cusp-integral
additivity proof. Only complex-valued integrands required by that chain are used.
The incidental extension of primitives from intersecting balls is omitted.
-/

namespace Dubon2026
noncomputable section
open Complex MeasureTheory Set UpperHalfPlane
open scoped Interval Manifold
variable {f : ℂ → ℂ}

-- This proof adapts
-- `Complex.IsConservativeOn.eventually_nhds_wedgeIntegral_sub_wedgeIntegral` from
-- `Mathlib.Analysis.Complex.HasPrimitives` from a ball to the upper half-plane.
/-- Wedge integrals based at a point of the upper half-plane are additive along any intermediate
point there.  Equivalently, the integral around the rectangle left between the three wedge paths
vanishes. -/
theorem sourceConservative_wedgeIntegral_sub
    (hf : IsConservativeOn f upperHalfPlaneSet) (hcont : ContinuousOn f upperHalfPlaneSet)
    {b z w : ℂ} (hb : b ∈ upperHalfPlaneSet) (hz : z ∈ upperHalfPlaneSet)
    (hw : w ∈ upperHalfPlaneSet) :
    wedgeIntegral b w f - wedgeIntegral b z f = wedgeIntegral z w f := by
  set I₁ := ∫ x in b.re..w.re, f (x + b.im * Complex.I)
  set I₂ := Complex.I • ∫ y in b.im..w.im, f (w.re + y * Complex.I)
  set I₃ := ∫ x in b.re..z.re, f (x + b.im * Complex.I)
  set I₄ := Complex.I • ∫ y in b.im..z.im, f (z.re + y * Complex.I)
  set I₅ := ∫ x in z.re..w.re, f (x + z.im * Complex.I)
  set I₆ := Complex.I • ∫ y in z.im..w.im, f (w.re + y * Complex.I)
  set I₇ := ∫ x in z.re..w.re, f (x + b.im * Complex.I)
  set I₈ := Complex.I • ∫ y in b.im..z.im, f (w.re + y * Complex.I)
  have integrableHoriz (x₁ x₂ y : ℝ) (hy : 0 < y) :
      IntervalIntegrable (fun x : ℝ ↦ f (x + y * Complex.I)) volume x₁ x₂ :=
    (hcont.comp (by fun_prop) (fun _ _ ↦ by simpa using hy)).intervalIntegrable
  have integrableVert (x y₁ y₂ : ℝ) (hy₁ : 0 < y₁) (hy₂ : 0 < y₂) :
      IntervalIntegrable (fun y : ℝ ↦ f (x + y * Complex.I)) volume y₁ y₂ := by
    apply ContinuousOn.intervalIntegrable
    apply hcont.comp (by fun_prop)
    intro y hy
    rcases mem_uIcc.mp hy with hy | hy
    · have : 0 < y := hy₁.trans_le hy.1
      simpa using this
    · have : 0 < y := hy₂.trans_le hy.1
      simpa using this
  have hI₁ : I₁ = I₃ + I₇ := by
    rw [intervalIntegral.integral_add_adjacent_intervals]
    · exact integrableHoriz _ _ _ hb
    · exact integrableHoriz _ _ _ hb
  have hI₂ : I₂ = I₈ + I₆ := by
    rw [← smul_add, intervalIntegral.integral_add_adjacent_intervals]
    · exact integrableVert _ _ _ hb hz
    · exact integrableVert _ _ _ hz hw
  have hrect : Rectangle (z.re + b.im * Complex.I) (w.re + z.im * Complex.I) ⊆
      upperHalfPlaneSet := by
    apply (convex_halfSpace_im_gt 0).rectangle_subset
    · simpa using hb
    · simpa using hz
    · simpa using hz
    · simpa using hb
  have hI₀ : I₇ - I₅ + I₈ - I₄ = 0 := by
    simpa [← add_eq_zero_iff_eq_neg, wedgeIntegral_add_wedgeIntegral_eq] using
      hf (z.re + b.im * Complex.I) (w.re + z.im * Complex.I) hrect
  grind [wedgeIntegral]

/-- The wedge integral of a holomorphic function from an upper-half-plane base point has derivative
equal to the function at every point of the upper half-plane. -/
theorem sourceHolomorphic_hasDerivAt_wedgeIntegral
    (hf : DifferentiableOn ℂ f upperHalfPlaneSet) (b : UpperHalfPlane) {z : ℂ}
    (hz : z ∈ upperHalfPlaneSet) :
    HasDerivAt (fun w ↦ wedgeIntegral (b : ℂ) w f) (f z) z := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_upperHalfPlaneSet z hz
  have hlocal : HasDerivAt (fun w ↦ wedgeIntegral z w f) (f z) z :=
    (hf.isConservativeOn.mono hball).hasDerivAt_wedgeIntegral
      (hf.continuousOn.mono hball) (Metric.mem_ball_self hr)
  refine (hlocal.const_add (wedgeIntegral (b : ℂ) z f)).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hz] with w hw
  have hadd := sourceConservative_wedgeIntegral_sub hf.isConservativeOn
    hf.continuousOn b.coe_im_pos hz hw
  grind


/-- Every original holomorphic upper-half-plane integrand has a common primitive, constructed by its wedge integral. -/
theorem sourceUpperHalfPlane_exists_primitive {F : ℍ → ℂ} (hF : MDiff F) :
    ∃ Φ : ℂ → ℂ, ∀ τ : ℍ, HasDerivAt Φ (F τ) τ := by
  refine ⟨fun z => wedgeIntegral (UpperHalfPlane.I : ℂ) z (F ∘ ofComplex), fun τ => ?_⟩
  simpa only [Function.comp_apply, ofComplex_apply] using
    sourceHolomorphic_hasDerivAt_wedgeIntegral
      (UpperHalfPlane.mdifferentiable_iff.mp hF) UpperHalfPlane.I τ.2

end
end Dubon2026
