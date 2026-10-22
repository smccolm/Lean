import Dubon2026.SourceOriginalCuspNormalValues
import Dubon2026.SourceCurveOrderOnePlaces

/-! DUB-17/18 -> original torsion cardinality -> actual cusp place chart.
The original uniformizer gives order-one differences at nearby points.
The existing order-map place construction therefore has normalization
one, producing a family of actual original places centered at the given
cusp. All nontriviality and valuation hypotheses are derived here.
-/
namespace Dubon2026.SourceFunctionField.CuspLabels
noncomputable section
open Filter Metric SourceCurve
open scoped Topology
variable (N : ℕ) [NeZero N] (ζ : ℂˣ) (hζ : IsPrimitiveRoot (ζ : ℂ) N)
variable (s : {s // s ∈ labels N})

theorem exists_normalized_disc_place {z : ℂ} (hz : z ∈ ball 0 (discRadius N ζ hζ s))
    (ha : AnalyticAt ℂ (discNormal N ζ hζ s (place N ℂ ζ hζ s).uniformizer) z)
    (hd : deriv (discNormal N ζ hζ s (place N ℂ ζ hζ s).uniformizer) z ≠ 0) :
    ∃ P : Place ℂ (modularFunctionFieldOver N ℂ),
      (∀ f, f ∈ P.toValuationSubring ↔ 0 ≤ discOrder N ζ hζ s z f) ∧
      ∀ f, f ≠ 0 → discOrder N ζ hζ s z f = (P.ord f : WithTop ℤ) :=
  Place.exists_place_of_orderMap_of_order_one (discOrder N ζ hζ s z)
    (discOrder_eq_top_iff N ζ hζ s hz) (discOrder_mul N ζ hζ s hz)
    (discOrder_add N ζ hζ s hz) (discOrder_const N ζ hζ s hz)
    ((place N ℂ ζ hζ s).uniformizer - algebraMap ℂ (modularFunctionFieldOver N ℂ)
      (discNormal N ζ hζ s (place N ℂ ζ hζ s).uniformizer z))
    (discOrder_sub_uniformizer_one N ζ hζ s hz ha hd)

theorem exists_cusp_disc_place_family :
    ∃ (δ : ℝ) (γ : ℂ → Place ℂ (modularFunctionFieldOver N ℂ)),
      0 < δ ∧ γ 0 = place N ℂ ζ hζ s ∧
      ∀ z ∈ ball 0 δ, z ∈ ball 0 (discRadius N ζ hζ s) ∧
        (∀ f, f ∈ (γ z).toValuationSubring ↔ 0 ≤ discOrder N ζ hζ s z f) ∧
        (∀ f, f ≠ 0 → discOrder N ζ hζ s z f = ((γ z).ord f : WithTop ℤ)) ∧
        AnalyticAt ℂ (discNormal N ζ hζ s (place N ℂ ζ hζ s).uniformizer) z ∧
        deriv (discNormal N ζ hζ s (place N ℂ ζ hζ s).uniformizer) z ≠ 0 := by
  classical
  have ha := discNormal_uniformizer_analytic N ζ hζ s
  have hball : ∀ᶠ z in 𝓝 (0 : ℂ), z ∈ ball 0 (discRadius N ζ hζ s) :=
    ball_mem_nhds 0 (discRadius_pos N ζ hζ s)
  have he : ∀ᶠ z in 𝓝 (0 : ℂ), z ∈ ball 0 (discRadius N ζ hζ s) ∧
      AnalyticAt ℂ (discNormal N ζ hζ s (place N ℂ ζ hζ s).uniformizer) z ∧
      deriv (discNormal N ζ hζ s (place N ℂ ζ hζ s).uniformizer) z ≠ 0 :=
    hball.and
      (ha.eventually_analyticAt.and (ha.deriv.continuousAt.eventually_ne
        (discNormal_uniformizer_deriv_ne_zero N ζ hζ s)))
  obtain ⟨δ, hδ, hgood⟩ := Metric.eventually_nhds_iff_ball.mp he
  have hex (z : ℂ) (hz : z ∈ ball 0 δ) :=
    exists_normalized_disc_place N ζ hζ s (hgood z hz).1 (hgood z hz).2.1 (hgood z hz).2.2
  let γ : ℂ → Place ℂ (modularFunctionFieldOver N ℂ) :=
    fun z => if hz : z ∈ ball 0 δ then (hex z hz).choose else place N ℂ ζ hζ s
  have hγ (z : ℂ) (hz : z ∈ ball 0 δ) :
      (∀ f, f ∈ (γ z).toValuationSubring ↔ 0 ≤ discOrder N ζ hζ s z f) ∧
      (∀ f, f ≠ 0 → discOrder N ζ hζ s z f = ((γ z).ord f : WithTop ℤ)) := by
    dsimp only [γ]
    rw [dif_pos hz]
    exact (hex z hz).choose_spec
  refine ⟨δ, γ, hδ, ?_, fun z hz =>
    ⟨(hgood z hz).1, (hγ z hz).1, (hγ z hz).2, (hgood z hz).2.1, (hgood z hz).2.2⟩⟩
  apply Place.ext
  apply SetLike.ext
  intro f
  by_cases hf : f = 0
  · subst f
    exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩
  · rw [(hγ 0 (mem_ball_self hδ)).1, (place N ℂ ζ hζ s).mem_iff_ord_nonneg]
    change 0 ≤ meromorphicOrderAt (discRealize N ζ hζ s f) 0 ↔ _
    rw [discRealize_order_zero N ζ hζ s f hf]
    exact WithTop.coe_nonneg

end
end Dubon2026.SourceFunctionField.CuspLabels
