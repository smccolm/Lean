import Dubon2026.SourceCurveConvergentDiscPlaces
import Dubon2026.SourceCurveRationalResidueValues

/-! DUB-17/18 -> auxiliary cover analytic charts -> literal residue values.
Reuse the existing rational residue evaluation. Positive order of the
difference from an analytic normal-form value identifies the residue;
the existing conventions agree at poles as well. -/
namespace Dubon2026.SourceCurve.AnalyticDisc
noncomputable section
open SourceFunctionField.CuspTaylor Filter Metric
open scoped Topology
variable {E : Type*} [Field E] [Algebra ℂ E]

theorem rationalEval_eq_normal (e : E →ₐ[ℂ] realizedField) {R : ℝ}
    (hR : 0 < R) (G : E → ℂ → ℂ)
    (hm : ∀ a, MeromorphicOn (G a) (ball 0 R))
    (hr : ∀ a, Represents (e a).val (G a))
    {z : ℂ} (hz : z ∈ ball 0 R) (P : Place ℂ E)
    (hP : Function.Bijective (algebraMap ℂ P.ResidueField))
    (hmem : ∀ a, a ∈ P.toValuationSubring ↔ 0 ≤ meromorphicOrderAt (G a) z)
    (horder : ∀ a, a ≠ 0 → meromorphicOrderAt (G a) z = (P.ord a : WithTop ℤ))
    (a : E) : P.rationalEval hP a = normal R G a z := by
  have hn := normal_form G a hz
  by_cases ha : a ∈ P.toValuationSubring
  · have han : AnalyticAt ℂ (normal R G a) z := by
      apply hn.meromorphicOrderAt_nonneg_iff_analyticAt.mp
      rw [meromorphicOrderAt_congr (normal_germ hm a hz)]
      exact (hmem a).mp ha
    let c := normal R G a z
    by_cases hc : a - algebraMap ℂ E c = 0
    · have he : a = algebraMap ℂ E c := sub_eq_zero.mp hc
      change P.rationalEval hP a = c
      rw [he, Place.rationalEval_algebraMap]
    · apply P.rationalEval_eq_of_ord_sub_pos
      have he : G (a - algebraMap ℂ E c) =ᶠ[𝓝[≠] z]
          (normal R G a - fun _ : ℂ => c) :=
        (realize_sub_const e hR G hm hr a c hz).trans
          ((normal_germ hm a hz).symm.sub Filter.EventuallyEq.rfl)
      have hsub : AnalyticAt ℂ (normal R G a - fun _ : ℂ => c) z := han.sub analyticAt_const
      have hnonneg := hsub.meromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt.mpr hsub
      have hne : meromorphicOrderAt (normal R G a - fun _ : ℂ => c) z ≠ 0 := by
        intro he0
        have hvalue := hsub.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp he0
        exact hvalue (sub_self _)
      have hp : 0 < meromorphicOrderAt (normal R G a - fun _ : ℂ => c) z :=
        lt_of_le_of_ne hnonneg hne.symm
      rw [← meromorphicOrderAt_congr he, horder _ hc] at hp
      exact WithTop.coe_pos.mp hp
  · have hzero : normal R G a z = 0 := by
      by_contra hv
      apply ha
      apply (hmem a).mpr
      rw [← meromorphicOrderAt_congr (normal_germ hm a hz),
        hn.meromorphicOrderAt_eq_zero_iff.mpr hv]
    rw [Place.rationalEval, dif_neg ha, hzero]

end
end Dubon2026.SourceCurve.AnalyticDisc
