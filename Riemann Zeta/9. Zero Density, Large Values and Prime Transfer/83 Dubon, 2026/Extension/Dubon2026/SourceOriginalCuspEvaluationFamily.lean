import Dubon2026.SourceOriginalCuspResidueValues

/-! DUB-17/18 -> original torsion cardinality -> actual cusp place chart.
The constructed original place family has literal residue-value functions
equal locally to the proved meromorphic normal forms. Thus every original
function has the exact normalized place order at every family point, and
regular functions are analytic. The uniformizer value supplies the local
coordinate that will be inverted in the cusp-chart consumer.
-/
namespace Dubon2026.SourceFunctionField.CuspLabels
noncomputable section
open Filter Metric SourceCurve
open scoped Topology
variable (N : ℕ) [NeZero N] (ζ : ℂˣ) (hζ : IsPrimitiveRoot (ζ : ℂ) N)
variable (s : {s // s ∈ labels N})

theorem exists_cusp_disc_evaluation_family :
    ∃ (δ : ℝ) (γ : ℂ → Place ℂ (modularFunctionFieldOver N ℂ)),
      0 < δ ∧ γ 0 = place N ℂ ζ hζ s ∧
      (∀ z ∈ ball 0 δ, originalPlaceEval N ℂ (γ z) (place N ℂ ζ hζ s).uniformizer =
        discNormal N ζ hζ s (place N ℂ ζ hζ s).uniformizer z) ∧
      ∀ z ∈ ball 0 δ, ∀ f : modularFunctionFieldOver N ℂ, f ≠ 0 →
        MeromorphicAt (fun t => originalPlaceEval N ℂ (γ t) f) z ∧
        meromorphicOrderAt (fun t => originalPlaceEval N ℂ (γ t) f) z = ((γ z).ord f : WithTop ℤ) ∧
        (f ∈ (γ z).toValuationSubring → AnalyticAt ℂ (fun t => originalPlaceEval N ℂ (γ t) f) z) := by
  obtain ⟨δ, γ, hδ, hγ0, hγ⟩ := exists_cusp_disc_place_family N ζ hζ s
  have heq (f : modularFunctionFieldOver N ℂ) (z : ℂ) (hz : z ∈ ball 0 δ) :
      originalPlaceEval N ℂ (γ z) f = discNormal N ζ hζ s f z :=
    eval_eq_discNormal N ζ hζ s (hγ z hz).1 (γ z) (hγ z hz).2.1 (hγ z hz).2.2.1 f
  have hgerm (f : modularFunctionFieldOver N ℂ) (z : ℂ) (hz : z ∈ ball 0 δ) :
      (fun t => originalPlaceEval N ℂ (γ t) f) =ᶠ[𝓝 z] discNormal N ζ hζ s f := by
    filter_upwards [isOpen_ball.mem_nhds hz] with u hu
    exact heq f u hu
  refine ⟨δ, γ, hδ, hγ0, fun z hz => heq _ z hz, fun z hz f hf => ?_⟩
  have hn : MeromorphicNFAt (fun t => originalPlaceEval N ℂ (γ t) f) z :=
    (meromorphicNFAt_congr (hgerm f z hz)).mpr
      (discNormal_normalForm N ζ hζ s f (hγ z hz).1)
  have hord : meromorphicOrderAt (fun t => originalPlaceEval N ℂ (γ t) f) z =
      ((γ z).ord f : WithTop ℤ) := by
    rw [meromorphicOrderAt_congr ((hgerm f z hz).filter_mono nhdsWithin_le_nhds),
      discNormal_order N ζ hζ s f (hγ z hz).1]
    exact (hγ z hz).2.2.1 f hf
  refine ⟨hn.meromorphicAt, hord, fun hmem => ?_⟩
  apply hn.meromorphicOrderAt_nonneg_iff_analyticAt.mp
  rw [meromorphicOrderAt_congr ((hgerm f z hz).filter_mono nhdsWithin_le_nhds),
    discNormal_order N ζ hζ s f (hγ z hz).1]
  exact ((hγ z hz).2.1 f).mp hmem

end
end Dubon2026.SourceFunctionField.CuspLabels
