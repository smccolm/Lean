import Dubon2026.SourceOriginalGlobalArcPartner
import Mathlib.Algebra.Order.Group.Pointwise.Interval

/-! DUB-17/18 -> original Abel-Jacobi -> C1 arc reversal.
Identify the endpoint parameters in the exact power and reciprocal arc
intervals. These lemmas are consumed by the affine boundary presentations.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.ArcAffine
noncomputable section
open Set

theorem endpoints_of_image_mono {m c a b x y : ℝ} (hm : 0 < m) (hxy : x ≤ y)
    (h : Icc a b = (fun t : ℝ => m * t + c) '' Icc x y) : a = m * x + c ∧ b = m * y + c := by
  have himg : (fun t : ℝ => m * t + c) '' Icc x y = Icc (m * x + c) (m * y + c) :=
    image_affine_Icc' hm c x y
  rw [himg] at h
  have hne : m * x + c ≤ m * y + c := by nlinarith
  have hab : a ≤ b := by
    have hne' : (Icc a b).Nonempty := by rw [h]; exact nonempty_Icc.mpr hne
    exact nonempty_Icc.mp hne'
  exact (Icc_eq_Icc_iff hab).mp h

theorem endpoints_of_image_anti {m c a b x y : ℝ} (hm : m < 0) (hxy : x ≤ y)
    (h : Icc a b = (fun t : ℝ => m * t + c) '' Icc x y) : a = m * y + c ∧ b = m * x + c := by
  have himg : (fun t : ℝ => m * t + c) '' Icc x y = Icc (m * y + c) (m * x + c) := by
    ext s
    simp only [mem_image, mem_Icc]
    constructor
    · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
      exact ⟨by nlinarith, by nlinarith⟩
    · rintro ⟨h1, h2⟩
      refine ⟨(s - c) / m, ⟨?_, ?_⟩, ?_⟩
      · rw [le_div_iff_of_neg hm]; linarith
      · rw [div_le_iff_of_neg hm]; linarith
      · show m * ((s - c) / m) + c = s
        have hm0 : m ≠ 0 := hm.ne
        field_simp
        ring
  rw [himg] at h
  have hne : m * y + c ≤ m * x + c := by nlinarith
  have hab : a ≤ b := by
    have hne' : (Icc a b).Nonempty := by rw [h]; exact nonempty_Icc.mpr hne
    exact nonempty_Icc.mp hne'
  exact (Icc_eq_Icc_iff hab).mp h

end
end Dubon2026.SourceFunctionField.CellGeometry.ArcAffine
