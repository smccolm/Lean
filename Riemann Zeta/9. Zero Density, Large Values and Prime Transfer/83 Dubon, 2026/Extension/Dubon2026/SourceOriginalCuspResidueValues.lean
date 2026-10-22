import Dubon2026.SourceOriginalCuspPlaceFamily
import Dubon2026.SourceOriginalPlaceEvaluation

/-! DUB-17/18 -> original torsion cardinality -> actual cusp place chart.
For an original place constructed from the cusp order map, its literal
residue evaluation equals the native normal-form value of the original
function. Positive order of the difference from its analytic value proves
the regular case; both prescribed conventions give zero at poles.
-/
namespace Dubon2026.SourceFunctionField.CuspLabels
noncomputable section
open Filter Metric SourceCurve
open scoped Topology
variable (N : ℕ) [NeZero N] (ζ : ℂˣ) (hζ : IsPrimitiveRoot (ζ : ℂ) N)
variable (s : {s // s ∈ labels N})

theorem eval_eq_discNormal {z : ℂ} (hz : z ∈ ball 0 (discRadius N ζ hζ s))
    (P : Place ℂ (modularFunctionFieldOver N ℂ))
    (hmem : ∀ f, f ∈ P.toValuationSubring ↔ 0 ≤ discOrder N ζ hζ s z f)
    (horder : ∀ f, f ≠ 0 → discOrder N ζ hζ s z f = (P.ord f : WithTop ℤ))
    (f : modularFunctionFieldOver N ℂ) :
    originalPlaceEval N ℂ P f = discNormal N ζ hζ s f z := by
  have hn := discNormal_normalForm N ζ hζ s f hz
  by_cases hf : f ∈ P.toValuationSubring
  · have ha : AnalyticAt ℂ (discNormal N ζ hζ s f) z := by
      apply hn.meromorphicOrderAt_nonneg_iff_analyticAt.mp
      rw [discNormal_order N ζ hζ s f hz]
      exact (hmem f).mp hf
    let c := discNormal N ζ hζ s f z
    by_cases hc : f - algebraMap ℂ (modularFunctionFieldOver N ℂ) c = 0
    · have he : f = algebraMap ℂ (modularFunctionFieldOver N ℂ) c := sub_eq_zero.mp hc
      change originalPlaceEval N ℂ P f = c
      rw [he, originalPlaceEval_algebraMap]
    · apply originalPlaceEval_eq_of_ord_sub_pos
      have he : discRealize N ζ hζ s (f - algebraMap ℂ (modularFunctionFieldOver N ℂ) c) =ᶠ[𝓝[≠] z]
          (discNormal N ζ hζ s f - fun _ : ℂ => c) := by
        apply (discRealize_sub_const N ζ hζ s f c hz).trans
        exact ((discNormal_germ N ζ hζ s f hz).symm.sub Filter.EventuallyEq.rfl)
      have hsub : AnalyticAt ℂ (discNormal N ζ hζ s f - fun _ : ℂ => c) z := ha.sub analyticAt_const
      have hnonneg := hsub.meromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt.mpr hsub
      have hne : meromorphicOrderAt (discNormal N ζ hζ s f - fun _ : ℂ => c) z ≠ 0 := by
        intro he0
        have hvalue := hsub.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp he0
        exact hvalue (sub_self _)
      have hp : 0 < meromorphicOrderAt (discNormal N ζ hζ s f - fun _ : ℂ => c) z :=
        lt_of_le_of_ne hnonneg hne.symm
      rw [← meromorphicOrderAt_congr he] at hp
      change 0 < discOrder N ζ hζ s z (f - algebraMap ℂ (modularFunctionFieldOver N ℂ) c) at hp
      rw [horder _ hc] at hp
      exact WithTop.coe_pos.mp hp
  · have hzero : discNormal N ζ hζ s f z = 0 := by
      by_contra hv
      apply hf
      apply (hmem f).mpr
      rw [← discNormal_order N ζ hζ s f hz, hn.meromorphicOrderAt_eq_zero_iff.mpr hv]
    rw [originalPlaceEval, dif_neg hf, hzero]

end
end Dubon2026.SourceFunctionField.CuspLabels
