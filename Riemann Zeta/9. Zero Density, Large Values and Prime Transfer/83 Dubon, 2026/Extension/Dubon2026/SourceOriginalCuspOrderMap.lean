import Dubon2026.SourceOriginalCuspDiscFunctions

/-! DUB-17/18 -> original torsion cardinality -> actual cusp place chart.
The chosen original cusp functions give a genuine meromorphic-order
valuation law at every point of their common disk. Connected uniqueness
derives all algebra laws; nonzero original functions have finite order.
An order-one original uniformizer will supply nontriviality locally.
-/
namespace Dubon2026.SourceFunctionField.CuspLabels
noncomputable section
open Filter Metric
open scoped Topology
variable (N : ℕ) [NeZero N] (ζ : ℂˣ) (hζ : IsPrimitiveRoot (ζ : ℂ) N)
variable (s : {s // s ∈ labels N})

/-- Meromorphic order of the actual original cusp realization at a disk point. -/
def discOrder (z : ℂ) (f : modularFunctionFieldOver N ℂ) : WithTop ℤ :=
  meromorphicOrderAt (discRealize N ζ hζ s f) z

theorem discOrder_zero {z : ℂ} (hz : z ∈ ball 0 (discRadius N ζ hζ s)) :
    discOrder N ζ hζ s z 0 = ⊤ := by
  have he := discRealize_const N ζ hζ s 0 hz
  rw [map_zero] at he
  change meromorphicOrderAt _ _ = _
  rw [meromorphicOrderAt_congr he]
  simp only [meromorphicOrderAt_const, if_true]

theorem discOrder_eq_top_iff {z : ℂ} (hz : z ∈ ball 0 (discRadius N ζ hζ s))
    (f : modularFunctionFieldOver N ℂ) : discOrder N ζ hζ s z f = ⊤ ↔ f = 0 := by
  constructor
  · intro he
    by_contra hf
    exact discRealize_order_ne_top N ζ hζ s f hf hz he
  · rintro rfl
    exact discOrder_zero N ζ hζ s hz

theorem discOrder_const {z : ℂ} (hz : z ∈ ball 0 (discRadius N ζ hζ s))
    (c : ℂ) (hc : c ≠ 0) :
    discOrder N ζ hζ s z (algebraMap ℂ (modularFunctionFieldOver N ℂ) c) = 0 := by
  change meromorphicOrderAt _ _ = _
  rw [meromorphicOrderAt_congr (discRealize_const N ζ hζ s c hz)]
  simp only [meromorphicOrderAt_const, if_neg hc]

theorem discOrder_mul {z : ℂ} (hz : z ∈ ball 0 (discRadius N ζ hζ s))
    (f g : modularFunctionFieldOver N ℂ) :
    discOrder N ζ hζ s z (f * g) = discOrder N ζ hζ s z f + discOrder N ζ hζ s z g := by
  unfold discOrder
  rw [meromorphicOrderAt_congr (discRealize_mul N ζ hζ s f g hz),
    meromorphicOrderAt_mul (discRealize_meromorphicOn N ζ hζ s f z hz)
      (discRealize_meromorphicOn N ζ hζ s g z hz)]

theorem discOrder_add {z : ℂ} (hz : z ∈ ball 0 (discRadius N ζ hζ s))
    (f g : modularFunctionFieldOver N ℂ) :
    min (discOrder N ζ hζ s z f) (discOrder N ζ hζ s z g) ≤ discOrder N ζ hζ s z (f + g) := by
  unfold discOrder
  rw [meromorphicOrderAt_congr (discRealize_add N ζ hζ s f g hz)]
  exact meromorphicOrderAt_add (discRealize_meromorphicOn N ζ hζ s f z hz)
    (discRealize_meromorphicOn N ζ hζ s g z hz)

theorem discRealize_sub_const (f : modularFunctionFieldOver N ℂ) (c : ℂ)
    {z : ℂ} (hz : z ∈ ball 0 (discRadius N ζ hζ s)) :
    discRealize N ζ hζ s (f - algebraMap ℂ (modularFunctionFieldOver N ℂ) c) =ᶠ[𝓝[≠] z]
      (fun u => discRealize N ζ hζ s f u - c) := by
  have ha := discRealize_add N ζ hζ s f (algebraMap ℂ (modularFunctionFieldOver N ℂ) (-c)) hz
  have hc := discRealize_const N ζ hζ s (-c) hz
  filter_upwards [ha, hc] with u hu hv
  rw [map_neg] at hv
  simpa only [map_neg, sub_eq_add_neg, Pi.add_apply, hv] using hu

end
end Dubon2026.SourceFunctionField.CuspLabels
