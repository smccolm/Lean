import Dubon2026.SourceOriginalArcOrientations

/-! DUB-17/18 -> original Abel-Jacobi -> actual C1 arc reversal.
Only the affine inverse identities, interval maps and slope signs used by
that reversal are retained. Composition and interval-image monotonicity
use native Mathlib results directly.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.ArcAffine
noncomputable section
open Set

theorem affine_inv_apply {m c : ℝ} (hm : m ≠ 0) (t : ℝ) : (m * t + c - c) / m = t := by
  field_simp
  ring

theorem affine_apply_inv {m c : ℝ} (hm : m ≠ 0) (u : ℝ) : m * ((u - c) / m) + c = u := by
  field_simp
  ring

theorem strictMono_affine_inv {m c : ℝ} (hm : 0 < m) : StrictMono fun u : ℝ => (u - c) / m :=
  fun _ _ h => by
    show _ / m < _ / m
    exact div_lt_div_of_pos_right (by linarith) hm

theorem strictAnti_affine_inv {m c : ℝ} (hm : m < 0) : StrictAnti fun u : ℝ => (u - c) / m :=
  fun _ _ h => by
    show _ / m < _ / m
    exact div_lt_div_of_neg_of_lt hm (by linarith)

theorem affine_mapsTo_pos {m c u₀ u₁ : ℝ} (hm : 0 < m) :
    MapsTo (fun t : ℝ => m * t + c) (Icc u₀ u₁) (Icc (m * u₀ + c) (m * u₁ + c)) := by
  intro t ht
  exact ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩

theorem affine_mapsTo_neg {m c u₀ u₁ : ℝ} (hm : m < 0) :
    MapsTo (fun t : ℝ => m * t + c) (Icc u₀ u₁) (Icc (m * u₁ + c) (m * u₀ + c)) := by
  intro t ht
  exact ⟨by nlinarith [ht.2], by nlinarith [ht.1]⟩

theorem affine_inv_mapsTo_pos {m c u₀ u₁ : ℝ} (hm : 0 < m) :
    MapsTo (fun u : ℝ => (u - c) / m) (Icc (m * u₀ + c) (m * u₁ + c)) (Icc u₀ u₁) := by
  intro u hu
  constructor
  · rw [le_div_iff₀ hm]; linarith [hu.1]
  · rw [div_le_iff₀ hm]; linarith [hu.2]

theorem affine_inv_mapsTo_neg {m c u₀ u₁ : ℝ} (hm : m < 0) :
    MapsTo (fun u : ℝ => (u - c) / m) (Icc (m * u₁ + c) (m * u₀ + c)) (Icc u₀ u₁) := by
  intro u hu
  constructor
  · rw [le_div_iff_of_neg hm]; linarith [hu.2]
  · rw [div_le_iff_of_neg hm]; linarith [hu.1]

theorem strictMonoOn_affine_pos {m c : ℝ} (hm : 0 < m) (s : Set ℝ) :
    StrictMonoOn (fun t : ℝ => m * t + c) s :=
  fun _ _ _ _ hab => by
    show m * _ + c < m * _ + c
    nlinarith

theorem strictAntiOn_affine_neg {m c : ℝ} (hm : m < 0) (s : Set ℝ) :
    StrictAntiOn (fun t : ℝ => m * t + c) s :=
  fun _ _ _ _ hab => by
    show m * _ + c < m * _ + c
    nlinarith

end
end Dubon2026.SourceFunctionField.CellGeometry.ArcAffine
