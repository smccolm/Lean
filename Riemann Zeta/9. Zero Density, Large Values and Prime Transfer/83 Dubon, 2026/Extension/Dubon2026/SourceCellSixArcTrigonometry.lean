import Dubon2026.SourceCellRectangleSmoothness
import Dubon2026.SourceCellBoundaryGeometry

/-! DUB-17/18 -> original Abel-Jacobi -> paired analytic cell dissection.
The exact six-arc radial rectangle has prescribed split side segments,
endpoints, smooth pieces and segment-valued subarcs. These properties feed
ordinary grid-cell construction and neighboring-cell pairing.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.RectSixArcs
open Real RectRadial

theorem tan_cornerAngle (u v : ℝ) : Real.tan (cornerAngle u v) = v / u := by
  rw [cornerAngle, Real.tan_arctan]

theorem cot_cornerAngle (u v : ℝ) :
    Real.cos (cornerAngle u v) / Real.sin (cornerAngle u v) = u / v := by
  have h := tan_cornerAngle u v
  rw [Real.tan_eq_sin_div_cos] at h
  rw [← inv_div (Real.sin (cornerAngle u v)) (Real.cos (cornerAngle u v)), h, inv_div]

theorem r6_tan_pi_add (x : ℝ) : Real.tan (π + x) = Real.tan x := by
  rw [add_comm π x, Real.tan_add_pi]

theorem r6_tan_two_pi_sub (x : ℝ) : Real.tan (2 * π - x) = -Real.tan x := by
  rw [show 2 * π - x = π - x + π by ring, Real.tan_add_pi, Real.tan_pi_sub]

theorem r6_tan_two_pi : Real.tan (2 * π) = 0 := by
  rw [two_mul, Real.tan_add_pi, Real.tan_pi]

theorem r6_tan_sub_two_pi (x : ℝ) : Real.tan (x - 2 * π) = Real.tan x := by
  rw [show x - 2 * π = x - π - π by ring, Real.tan_sub_pi, Real.tan_sub_pi]

theorem r6_cot_pi_sub (x : ℝ) :
    Real.cos (π - x) / Real.sin (π - x) = -(Real.cos x / Real.sin x) := by
  rw [Real.cos_pi_sub, Real.sin_pi_sub, neg_div]

theorem r6_cot_pi_add (x : ℝ) :
    Real.cos (π + x) / Real.sin (π + x) = Real.cos x / Real.sin x := by
  rw [add_comm π x, Real.cos_add_pi, Real.sin_add_pi, neg_div_neg_eq]

theorem r6_cot_sub_pi (x : ℝ) :
    Real.cos (x - π) / Real.sin (x - π) = Real.cos x / Real.sin x := by
  rw [Real.cos_sub_pi, Real.sin_sub_pi, neg_div_neg_eq]

theorem r6_cot_two_pi_sub (x : ℝ) :
    Real.cos (2 * π - x) / Real.sin (2 * π - x) = -(Real.cos x / Real.sin x) := by
  rw [show 2 * π - x = π - x + π by ring, Real.cos_add_pi, Real.sin_add_pi, neg_div_neg_eq,
    r6_cot_pi_sub]

theorem r6_tan_strictMonoOn_shifted :
    StrictMonoOn Real.tan (Set.Ioo (π / 2) (3 * π / 2)) := by
  intro x hx y hy hxy
  have hx' : x - π ∈ Set.Ioo (-(π / 2)) (π / 2) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hy' : y - π ∈ Set.Ioo (-(π / 2)) (π / 2) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have h1 : Real.tan (x - π) < Real.tan (y - π) := Real.strictMonoOn_tan hx' hy' (by linarith)
  rwa [Real.tan_sub_pi, Real.tan_sub_pi] at h1

theorem r6_tan_strictMonoOn_shifted2 :
    StrictMonoOn Real.tan (Set.Ioo (3 * π / 2) (5 * π / 2)) := by
  intro x hx y hy hxy
  have hx' : x - 2 * π ∈ Set.Ioo (-(π / 2)) (π / 2) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hy' : y - 2 * π ∈ Set.Ioo (-(π / 2)) (π / 2) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have h1 : Real.tan (x - 2 * π) < Real.tan (y - 2 * π) :=
    Real.strictMonoOn_tan hx' hy' (by linarith)
  rwa [r6_tan_sub_two_pi, r6_tan_sub_two_pi] at h1

theorem r6_cot_lt_cot {u u' : ℝ} (h0 : 0 < u) (hπ : u' < π) (huu : u < u') :
    Real.cos u' / Real.sin u' < Real.cos u / Real.sin u := by
  have hsu : 0 < Real.sin u := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith)
  have hsu' : 0 < Real.sin u' := Real.sin_pos_of_pos_of_lt_pi (by linarith) hπ
  rw [div_lt_div_iff₀ hsu' hsu]
  have h1 : 0 < Real.sin (u' - u) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  rw [Real.sin_sub] at h1
  nlinarith


end Dubon2026.SourceFunctionField.CellGeometry.RectSixArcs
