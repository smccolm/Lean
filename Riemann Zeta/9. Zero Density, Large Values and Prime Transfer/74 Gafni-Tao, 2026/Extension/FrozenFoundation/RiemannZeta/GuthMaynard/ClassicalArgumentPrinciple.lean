import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import RiemannZeta.External.PNT.RectangleArgumentPrinciple
import RiemannZeta.GuthMaynard.ClassicalDensity

open Complex Finset MeromorphicOn Set

namespace RiemannZeta.GuthMaynard

/-!
# Rectangle argument principle for the classical density argument

This module connects the PNT+ rectangle-residue infrastructure to the
pole-free Ingham detector used by this project.  Boundary nonvanishing and
finite analytic order remain explicit because they are the genuine hypotheses
needed before a Littlewood rectangle may be selected.
-/

/-- A concrete linear vertical-growth bound for zeta on the classical strip.
This is the project-native counterpart of the strip bound used by the imported
rectangle machinery. -/
theorem norm_riemannZeta_le_twenty_mul_abs_im_on_classical_strip
    {s : ℂ} (hre : s.re ∈ Set.Ico (1 / 2 : ℝ) 3) (him : 1 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 20 * |s.im| := by
  have hre_quarter : (1 / 4 : ℝ) ≤ s.re := by linarith [hre.1]
  have hre_nonneg : 0 ≤ s.re := by linarith [hre.1]
  have hre_le : s.re ≤ 3 * |s.im| := by nlinarith [hre.2, him]
  calc
    ‖riemannZeta s‖ ≤ 5 * ‖s‖ :=
      norm_riemannZeta_le_five_mul_norm hre_quarter him
    _ ≤ 5 * (|s.re| + |s.im|) := by
      exact mul_le_mul_of_nonneg_left (Complex.norm_le_abs_re_add_abs_im s) (by norm_num)
    _ ≤ 20 * |s.im| := by
      rw [abs_of_nonneg hre_nonneg]
      nlinarith

/-- The multiplicity-aware argument principle for an analytic function on a
closed rectangle.  The contour integral of its logarithmic derivative is the
finite sum of its analytic orders inside the rectangle. -/
theorem analytic_rectangle_logDeriv_integral_eq_order_sum
    {f : ℂ → ℂ} {z w : ℂ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (hf : AnalyticOnNhd ℂ f (Rectangle z w))
    (hfiniteOrder : ∀ p ∈ Rectangle z w, meromorphicOrderAt f p ≠ ⊤)
    (hnoBoundaryZeros :
      Disjoint (RectangleBorder z w)
        (MeromorphicOn.divisor f (Rectangle z w)).support) :
    RectangleIntegral' (logDeriv f) z w =
      ∑ p ∈ (divisor_support_rectangle_finite f z w).toFinset,
        ((MeromorphicOn.divisor f (Rectangle z w)) p : ℂ) := by
  exact rectangleIntegral_logDeriv_eq_sum_meromorphicOrderAt
    zRe_le_wRe zIm_le_wIm hf.meromorphicOn hf.meromorphicOn.logDeriv
    hfiniteOrder hnoBoundaryZeros

/-- Argument-principle specialization to the globally analytic, pole-free
Ingham detector.  The remaining hypotheses say that the selected contour has
no detector zero on its boundary and that the detector is not locally
identically zero at an interior point. -/
theorem regularizedInghamZeroDetector_rectangle_argumentPrinciple
    (X : ℕ) {z w : ℂ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (hfiniteOrder : ∀ p ∈ Rectangle z w,
      meromorphicOrderAt (regularizedInghamZeroDetector X) p ≠ ⊤)
    (hnoBoundaryZeros :
      Disjoint (RectangleBorder z w)
        (MeromorphicOn.divisor (regularizedInghamZeroDetector X)
          (Rectangle z w)).support) :
    RectangleIntegral' (logDeriv (regularizedInghamZeroDetector X)) z w =
      ∑ p ∈
        (divisor_support_rectangle_finite
          (regularizedInghamZeroDetector X) z w).toFinset,
        ((MeromorphicOn.divisor (regularizedInghamZeroDetector X)
          (Rectangle z w)) p : ℂ) := by
  apply analytic_rectangle_logDeriv_integral_eq_order_sum
      zRe_le_wRe zIm_le_wIm _ hfiniteOrder hnoBoundaryZeros
  intro p _
  exact analytic_regularizedInghamZeroDetector X p

end RiemannZeta.GuthMaynard
