import Dubon2026.SourceOriginalCuspEvaluationFamily

/-! DUB-17/18 -> original torsion cardinality -> actual cusp charts.
Invert the analytic normal form of the original cusp uniformizer. This
gives an injective family of actual original places with uniformizer
value equal to the parameter and exact normalized orders at every point.
The order-one derivative and all analytic/residue inputs are derived.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Filter SourceCurve CuspLabels
open scoped Topology

theorem original_cusp_place_chart_parameter (N : ℕ) [NeZero N]
    (ζ : ℂˣ) (hζ : IsPrimitiveRoot (ζ : ℂ) N) (s : {s // s ∈ labels N}) :
    ∃ (ρ : ℝ) (γ : ℂ → Place ℂ (modularFunctionFieldOver N ℂ)),
      0 < ρ ∧ γ 0 = place N ℂ ζ hζ s ∧ Set.InjOn γ (Metric.ball 0 ρ) ∧
      (∀ z ∈ Metric.ball 0 ρ, originalPlaceEval N ℂ (γ z) (place N ℂ ζ hζ s).uniformizer = z) ∧
      ∀ z ∈ Metric.ball 0 ρ, ∀ f : modularFunctionFieldOver N ℂ, f ≠ 0 →
        MeromorphicAt (fun t => originalPlaceEval N ℂ (γ t) f) z ∧
        meromorphicOrderAt (fun t => originalPlaceEval N ℂ (γ t) f) z = (γ z).ord f ∧
        (f ∈ (γ z).toValuationSubring → AnalyticAt ℂ (fun t => originalPlaceEval N ℂ (γ t) f) z) := by
  let v := place N ℂ ζ hζ s
  let T := discNormal N ζ hζ s v.uniformizer
  have hT : AnalyticAt ℂ T 0 := discNormal_uniformizer_analytic N ζ hζ s
  have hT0 : T 0 = 0 := discNormal_uniformizer_zero N ζ hζ s
  have hd : deriv T 0 ≠ 0 := discNormal_uniformizer_deriv_ne_zero N ζ hζ s
  let r := hT.hasStrictDerivAt.localInverse T (deriv T 0) 0 hd
  have ha : AnalyticAt ℂ r 0 := by simpa only [hT0] using hT.analyticAt_localInverse hd
  have hr0 : r 0 = 0 := by
    simpa only [hT0] using
      (HasStrictDerivAt.eventually_left_inverse hT.hasStrictDerivAt hd).self_of_nhds
  have hdr : HasStrictDerivAt r (deriv T 0)⁻¹ 0 := by
    simpa only [hT0] using hT.hasStrictDerivAt.to_localInverse hd
  have hdr0 : deriv r 0 ≠ 0 := by rw [hdr.hasDerivAt.deriv]; exact inv_ne_zero hd
  have he : ∀ᶠ z in 𝓝 (0 : ℂ), T (r z) = z := by
    simpa only [hT0] using HasStrictDerivAt.eventually_right_inverse hT.hasStrictDerivAt hd
  obtain ⟨δ, γ₀, hδ, hγ₀, hcoord, hδorders⟩ := exists_cusp_disc_evaluation_family N ζ hζ s
  have hrange : ∀ᶠ z in 𝓝 (0 : ℂ), r z ∈ Metric.ball 0 δ := by
    apply ha.continuousAt.eventually
    rw [hr0]
    exact Metric.ball_mem_nhds 0 hδ
  have hderiv : ∀ᶠ z in 𝓝 (0 : ℂ), deriv r z ≠ 0 :=
    ha.deriv.continuousAt.eventually (isOpen_ne.mem_nhds hdr0)
  obtain ⟨ρ, hρ, hρall⟩ := Metric.eventually_nhds_iff_ball.mp
    (he.and (hrange.and (ha.eventually_analyticAt.and hderiv)))
  let γ : ℂ → Place ℂ (modularFunctionFieldOver N ℂ) := fun z => γ₀ (r z)
  have heval (z : ℂ) (hz : z ∈ Metric.ball 0 ρ) : originalPlaceEval N ℂ (γ z) v.uniformizer = z :=
    (hcoord (r z) (hρall z hz).2.1).trans (hρall z hz).1
  refine ⟨ρ, γ, hρ, ?_, ?_, heval, ?_⟩
  · change γ₀ (r 0) = _
    rw [hr0, hγ₀]
  · intro z hz w hw heq
    calc z = originalPlaceEval N ℂ (γ z) v.uniformizer := (heval z hz).symm
         _ = originalPlaceEval N ℂ (γ w) v.uniformizer := congrArg (fun P => originalPlaceEval N ℂ P v.uniformizer) heq
         _ = w := heval w hw
  · intro z hz f hf
    obtain ⟨_, hrangez, haz, hdrz⟩ := hρall z hz
    obtain ⟨hm, ho, han⟩ := hδorders (r z) hrangez f hf
    refine ⟨hm.comp_analyticAt haz, ?_, fun h => (han h).comp haz⟩
    change meromorphicOrderAt ((fun t => originalPlaceEval N ℂ (γ₀ t) f) ∘ r) z = _
    rw [meromorphicOrderAt_comp_of_deriv_ne_zero haz hdrz]
    exact ho

end
end Dubon2026.SourceFunctionField
