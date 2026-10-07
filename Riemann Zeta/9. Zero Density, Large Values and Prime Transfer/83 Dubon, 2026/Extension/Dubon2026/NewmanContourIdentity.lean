import Dubon2026.NewmanDecay

/-! # Exact assembly and subtraction of the genuine Newman half-contours -/

namespace Dubon2026

open Complex Set Filter MeasureTheory
open scoped Topology

noncomputable section

/-- The Tauberian rectangle lies in its declared closed half-plane. -/
theorem newman_rectangle_subset {d R : ℝ} (hd : 0 ≤ d) (hR : 0 ≤ R) :
    Rectangle ((-d : ℂ) - R * I) ((R : ℂ) + R * I) ⊆ {z : ℂ | -d ≤ z.re} := by
  intro z hz
  have hre : ((-d : ℂ) - R * I).re ≤ ((R : ℂ) + R * I).re := by simp; linarith
  have him : ((-d : ℂ) - R * I).im ≤ ((R : ℂ) + R * I).im := by simp; linarith
  simpa using ((mem_Rect hre him z).mp hz).1

/-- Positive widths and height put the origin strictly inside the actual rectangle. -/
theorem newman_rectangle_origin {d R : ℝ} (hd : 0 < d) (hR : 0 < R) :
    Rectangle ((-d : ℂ) - R * I) ((R : ℂ) + R * I) ∈ 𝓝 (0 : ℂ) := by
  simp [rectangle_mem_nhds_iff, mem_reProdIm, uIoo_of_le (show -d ≤ R by linarith),
    uIoo_of_le (show -R ≤ R by linarith), hd, hR]

/-- The actual weighted integrand is integrable on all four edges, despite its interior pole. -/
theorem newman_contour_border_integrable {G : ℂ → ℂ} {d R : ℝ}
    (hd : 0 < d) (hR : 0 < R) (hG : ContinuousOn G {z : ℂ | -d ≤ z.re}) (T : ℝ) :
    RectangleBorderIntegrable (newmanContourIntegrand G T R)
      ((-d : ℂ) - R * I) ((R : ℂ) + R * I) := by
  apply ContinuousOn.rectangleBorder_integrable
  apply continuousOn_newmanContourIntegrand
    (hG.mono ((rectangleBorder_subset_rectangle _ _).trans (newman_rectangle_subset hd.le hR.le)))
  intro z hz hz0
  exact not_mem_rectangleBorder_of_rectangle_mem_nhds (newman_rectangle_origin hd hR) (hz0 ▸ hz)

/-- Cauchy's formula is the exact sum of the two actual three-edge contours. -/
theorem newman_half_contour_formula {G : ℂ → ℂ} {d R : ℝ}
    (hd : 0 < d) (hR : 0 < R) (hG : DifferentiableOn ℂ G {z : ℂ | -d ≤ z.re}) (T : ℝ) :
    (1 / (2 * Real.pi * I)) *
      (newmanRightContour (newmanContourIntegrand G T R) R +
        newmanLeftContour (newmanContourIntegrand G T R) d R) = G 0 := by
  have hre : ((-d : ℂ) - R * I).re ≤ ((R : ℂ) + R * I).re := by simp; linarith
  have him : ((-d : ℂ) - R * I).im ≤ ((R : ℂ) + R * I).im := by simp; linarith
  have hh := newman_rectangle_formula hre him (newman_rectangle_origin hd hR)
    (hG.mono (newman_rectangle_subset hd.le hR.le)) T R
  rw [RectangleIntegral', smul_eq_mul,
    newman_rectangle_split hd.le hR.le (newman_contour_border_integrable hd hR hG.continuousOn T)] at hh
  exact hh

/-- Subtraction of actual right contours follows from edge integrability. -/
theorem newmanRightContour_sub {F H : ℂ → ℂ} {d R : ℝ} (hd : 0 ≤ d) (hR : 0 ≤ R)
    (hF : RectangleBorderIntegrable F ((-d : ℂ) - R * I) ((R : ℂ) + R * I))
    (hH : RectangleBorderIntegrable H ((-d : ℂ) - R * I) ((R : ℂ) + R * I)) :
    newmanRightContour (F - H) R = newmanRightContour F R - newmanRightContour H R := by
  have hz : uIcc 0 R ⊆ uIcc (-d) R := by
    rw [uIcc_of_le hR, uIcc_of_le (by linarith : -d ≤ R)]
    exact Icc_subset_Icc (by linarith) le_rfl
  have hbF : IntervalIntegrable (fun x : ℝ => F ((x : ℂ) + (-R : ℝ) * I)) volume 0 R := by
    apply IntervalIntegrable.mono_set (b := R) (a := -d) (by simpa using hF.1) hz
  have htF : IntervalIntegrable (fun x : ℝ => F ((x : ℂ) + R * I)) volume 0 R := by
    apply IntervalIntegrable.mono_set (b := R) (a := -d) (by simpa using hF.2.1) hz
  have hvF : IntervalIntegrable (fun y : ℝ => F ((R : ℂ) + y * I)) volume (-R) R := by simpa using hF.2.2.1
  have hbH : IntervalIntegrable (fun x : ℝ => H ((x : ℂ) + (-R : ℝ) * I)) volume 0 R := by
    apply IntervalIntegrable.mono_set (b := R) (a := -d) (by simpa using hH.1) hz
  have htH : IntervalIntegrable (fun x : ℝ => H ((x : ℂ) + R * I)) volume 0 R := by
    apply IntervalIntegrable.mono_set (b := R) (a := -d) (by simpa using hH.2.1) hz
  have hvH : IntervalIntegrable (fun y : ℝ => H ((R : ℂ) + y * I)) volume (-R) R := by simpa using hH.2.2.1
  simp only [newmanRightContour, HIntegral, VIntegral, Pi.sub_apply]
  rw [intervalIntegral.integral_sub hbF hbH, intervalIntegral.integral_sub htF htH,
    intervalIntegral.integral_sub hvF hvH, smul_sub]
  abel

end
end Dubon2026
