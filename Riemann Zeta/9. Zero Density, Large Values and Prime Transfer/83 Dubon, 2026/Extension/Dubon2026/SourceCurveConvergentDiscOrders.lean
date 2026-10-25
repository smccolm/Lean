import Dubon2026.SourceCurveConvergentDiscGerms

/-! DUB-17/18 -> auxiliary cover analytic charts -> a true local order map.
The represented field is faithful. Its nonzero elements have finite order
throughout the connected disk, and its meromorphic orders satisfy the
valuation laws needed by the native normalized-place constructor. -/
namespace Dubon2026.SourceCurve.AnalyticDisc
noncomputable section
open SourceFunctionField.CuspTaylor Filter Metric
open scoped Topology
variable {E : Type*} [Field E] [Algebra ℂ E]
variable (e : E →ₐ[ℂ] realizedField) {R : ℝ} (hR : 0 < R) (G : E → ℂ → ℂ)
variable (hm : ∀ a, MeromorphicOn (G a) (ball 0 R))
variable (hr : ∀ a, Represents (e a).val (G a))
include hR hm hr

theorem order_ne_top (a : E) (ha : a ≠ 0) {z : ℂ} (hz : z ∈ ball 0 R) :
    meromorphicOrderAt (G a) z ≠ ⊤ :=
  order_ne_top_on_disc hR (hm a) (hr a)
    ((map_ne_zero (realizedField.val.comp e)).mpr ha) hz

theorem order_zero {z : ℂ} (hz : z ∈ ball 0 R) :
    meromorphicOrderAt (G 0) z = ⊤ := by
  have he := realize_const e hR G hm hr 0 hz
  rw [map_zero] at he
  rw [meromorphicOrderAt_congr he]
  simp only [meromorphicOrderAt_const, if_true]

theorem order_eq_top_iff (a : E) {z : ℂ} (hz : z ∈ ball 0 R) :
    meromorphicOrderAt (G a) z = ⊤ ↔ a = 0 := by
  constructor
  · intro he
    by_contra ha
    exact order_ne_top e hR G hm hr a ha hz he
  · rintro rfl
    exact order_zero e hR G hm hr hz

theorem order_const (c : ℂ) (hc : c ≠ 0) {z : ℂ} (hz : z ∈ ball 0 R) :
    meromorphicOrderAt (G (algebraMap ℂ E c)) z = 0 := by
  rw [meromorphicOrderAt_congr (realize_const e hR G hm hr c hz)]
  simp only [meromorphicOrderAt_const, if_neg hc]

theorem order_mul (a b : E) {z : ℂ} (hz : z ∈ ball 0 R) :
    meromorphicOrderAt (G (a * b)) z =
      meromorphicOrderAt (G a) z + meromorphicOrderAt (G b) z := by
  rw [meromorphicOrderAt_congr (realize_mul e hR G hm hr a b hz),
    meromorphicOrderAt_mul (hm a z hz) (hm b z hz)]

theorem order_add (a b : E) {z : ℂ} (hz : z ∈ ball 0 R) :
    min (meromorphicOrderAt (G a) z) (meromorphicOrderAt (G b) z) ≤
      meromorphicOrderAt (G (a + b)) z := by
  rw [meromorphicOrderAt_congr (realize_add e hR G hm hr a b hz)]
  exact meromorphicOrderAt_add (hm a z hz) (hm b z hz)

end
end Dubon2026.SourceCurve.AnalyticDisc
