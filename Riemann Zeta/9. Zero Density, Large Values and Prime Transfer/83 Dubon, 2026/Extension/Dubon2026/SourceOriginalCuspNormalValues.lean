import Dubon2026.SourceOriginalCuspOrderMap
import Mathlib.Analysis.Meromorphic.NormalForm

/-! DUB-17/18 -> original torsion cardinality -> actual cusp place chart.
Native meromorphic normal form supplies consistent finite values for the
actual cusp functions. The original uniformizer has order one and hence
an analytic normal form with a nonzero derivative at the cusp. Nearby
uniformizer differences therefore have order one, deriving nontriviality
and exact normalization for the forthcoming place family.
-/
namespace Dubon2026.SourceFunctionField.CuspLabels
noncomputable section
open Filter Metric
open scoped Topology
variable (N : ℕ) [NeZero N] (ζ : ℂˣ) (hζ : IsPrimitiveRoot (ζ : ℂ) N)
variable (s : {s // s ∈ labels N})

/-- The native meromorphic normal form of the actual original cusp function. -/
def discNormal (f : modularFunctionFieldOver N ℂ) : ℂ → ℂ :=
  toMeromorphicNFOn (discRealize N ζ hζ s f) (ball 0 (discRadius N ζ hζ s))

theorem discNormal_germ (f : modularFunctionFieldOver N ℂ)
    {z : ℂ} (hz : z ∈ ball 0 (discRadius N ζ hζ s)) :
    discNormal N ζ hζ s f =ᶠ[𝓝[≠] z] discRealize N ζ hζ s f :=
  (discRealize_meromorphicOn N ζ hζ s f).toMeromorphicNFOn_eq_self_on_nhdsNE hz

theorem discNormal_normalForm (f : modularFunctionFieldOver N ℂ)
    {z : ℂ} (hz : z ∈ ball 0 (discRadius N ζ hζ s)) :
    MeromorphicNFAt (discNormal N ζ hζ s f) z :=
  meromorphicNFOn_toMeromorphicNFOn _ _ hz

theorem discNormal_order (f : modularFunctionFieldOver N ℂ)
    {z : ℂ} (hz : z ∈ ball 0 (discRadius N ζ hζ s)) :
    meromorphicOrderAt (discNormal N ζ hζ s f) z = discOrder N ζ hζ s z f :=
  meromorphicOrderAt_congr (discNormal_germ N ζ hζ s f hz)

theorem discNormal_uniformizer_order :
    meromorphicOrderAt (discNormal N ζ hζ s (place N ℂ ζ hζ s).uniformizer) 0 = (1 : ℤ) := by
  rw [discNormal_order N ζ hζ s _ (mem_ball_self (discRadius_pos N ζ hζ s))]
  change meromorphicOrderAt (discRealize N ζ hζ s _) 0 = _
  rw [discRealize_order_zero N ζ hζ s _ (place N ℂ ζ hζ s).uniformizer_ne_zero,
    (place N ℂ ζ hζ s).ord_uniformizer]

theorem discNormal_uniformizer_analytic :
    AnalyticAt ℂ (discNormal N ζ hζ s (place N ℂ ζ hζ s).uniformizer) 0 := by
  apply (discNormal_normalForm N ζ hζ s _ (mem_ball_self (discRadius_pos N ζ hζ s))).meromorphicOrderAt_nonneg_iff_analyticAt.mp
  rw [discNormal_uniformizer_order]
  norm_num

theorem discNormal_uniformizer_zero :
    discNormal N ζ hζ s (place N ℂ ζ hζ s).uniformizer 0 = 0 := by
  by_contra hne
  have ho := (discNormal_normalForm N ζ hζ s _ (mem_ball_self
    (discRadius_pos N ζ hζ s))).meromorphicOrderAt_eq_zero_iff.mpr hne
  rw [discNormal_uniformizer_order] at ho
  norm_num at ho

theorem discNormal_uniformizer_deriv_ne_zero :
    deriv (discNormal N ζ hζ s (place N ℂ ζ hζ s).uniformizer) 0 ≠ 0 := by
  have ha := discNormal_uniformizer_analytic N ζ hζ s
  have horder : analyticOrderAt (discNormal N ζ hζ s (place N ℂ ζ hζ s).uniformizer) 0 = (1 : ℕ∞) := by
    apply WithTop.map_injective (Nat.cast_injective (R := ℤ))
    change (analyticOrderAt (discNormal N ζ hζ s (place N ℂ ζ hζ s).uniformizer) 0).map
      (Nat.cast : ℕ → ℤ) = (1 : ℕ∞).map (Nat.cast : ℕ → ℤ)
    rw [← ha.meromorphicOrderAt_eq, discNormal_uniformizer_order]
    rfl
  exact ha.deriv.analyticOrderAt_eq_zero.mp
    (analyticOrderAt_deriv_of_pos ha (n := 0) (by simpa only [Nat.cast_zero, zero_add] using horder))

theorem discOrder_sub_uniformizer_one {z : ℂ} (hz : z ∈ ball 0 (discRadius N ζ hζ s))
    (ha : AnalyticAt ℂ (discNormal N ζ hζ s (place N ℂ ζ hζ s).uniformizer) z)
    (hd : deriv (discNormal N ζ hζ s (place N ℂ ζ hζ s).uniformizer) z ≠ 0) :
    discOrder N ζ hζ s z ((place N ℂ ζ hζ s).uniformizer -
      algebraMap ℂ (modularFunctionFieldOver N ℂ)
        (discNormal N ζ hζ s (place N ℂ ζ hζ s).uniformizer z)) = (1 : ℤ) := by
  unfold discOrder
  rw [meromorphicOrderAt_congr (discRealize_sub_const N ζ hζ s _ _ hz)]
  have he := (discNormal_germ N ζ hζ s (place N ℂ ζ hζ s).uniformizer hz).sub
    (Filter.EventuallyEq.rfl (f := fun _ : ℂ => discNormal N ζ hζ s (place N ℂ ζ hζ s).uniformizer z))
  change meromorphicOrderAt (discRealize N ζ hζ s (place N ℂ ζ hζ s).uniformizer -
    fun _ : ℂ => discNormal N ζ hζ s (place N ℂ ζ hζ s).uniformizer z) z = _
  rw [← meromorphicOrderAt_congr he, (ha.sub analyticAt_const).meromorphicOrderAt_eq]
  have ho := ha.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hd
  change analyticOrderAt (discNormal N ζ hζ s (place N ℂ ζ hζ s).uniformizer -
    fun _ : ℂ => discNormal N ζ hζ s (place N ℂ ζ hζ s).uniformizer z) z = 1 at ho
  rw [ho]
  rfl

end
end Dubon2026.SourceFunctionField.CuspLabels
