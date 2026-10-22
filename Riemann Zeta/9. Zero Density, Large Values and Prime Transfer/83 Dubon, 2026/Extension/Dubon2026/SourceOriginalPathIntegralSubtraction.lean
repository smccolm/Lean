import Dubon2026.SourceOriginalRegularPathPrimitives
import Dubon2026.SourceOriginalDifferentialResidues
import Dubon2026.SourceOriginalChartReadFieldLaws

/-! DUB-17/18 -> original torsion cardinality -> Abel converse -> all-loop
period correction. Subtraction of actual path integrals is derived under
regularity on the traversed path. Original coefficient linearity and analytic
continuation of the punctured reading identity give the local primitive law.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N]
attribute [local instance] placeTopology
local notation "F" => modularFunctionFieldOver N ℂ

theorem original_differentialCoeff_sub (v : Place ℂ F) (η ζ : Ω[F⁄ℂ]) :
    v.differentialCoeff (η - ζ) = v.differentialCoeff η - v.differentialCoeff ζ :=
  (originalDifferentialCoeff N v).map_sub η ζ

theorem readDifferential_sub_of_coeff_mem (v : Place ℂ F) (η ζ : Ω[F⁄ℂ])
    (hη : v.differentialCoeff η ∈ v.toValuationSubring)
    (hζ : v.differentialCoeff ζ ∈ v.toValuationSubring) :
    readDifferential N v (η - ζ) =ᶠ[𝓝 (0 : ℂ)]
      fun z => readDifferential N v η z - readDifferential N v ζ z := by
  have hs : v.differentialCoeff (η - ζ) ∈ v.toValuationSubring := by
    rw [original_differentialCoeff_sub]
    exact sub_mem hη hζ
  apply (ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    (analyticAt_readDifferential_of_coeff_mem N v (η - ζ) hs).continuousAt
    ((analyticAt_readDifferential_of_coeff_mem N v η hη).continuousAt.sub
      (analyticAt_readDifferential_of_coeff_mem N v ζ hζ).continuousAt)).mp
  have hball : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ ball 0 (placeRadius N v) :=
    nhdsWithin_le_nhds (ball_mem_nhds (0 : ℂ) (place_spec N v).1)
  filter_upwards [chartRead_add N v (v.differentialCoeff η) (-v.differentialCoeff ζ),
    chartRead_neg N v (v.differentialCoeff ζ), hball]
    with z ha hn hz
  rw [readDifferential_eq_coefficient N v (η - ζ) hz,
    readDifferential_eq_coefficient N v η hz, readDifferential_eq_coefficient N v ζ hz]
  rw [original_differentialCoeff_sub, sub_eq_add_neg, ha, Pi.add_apply, hn]
  rfl

theorem isPrimitiveAlong_sub_of_coeff_mem (η ζ : Ω[F⁄ℂ])
    {P Q : Place ℂ F} (γ : Path P Q)
    (hη : ∀ t, (γ t).differentialCoeff η ∈ (γ t).toValuationSubring)
    (hζ : ∀ t, (γ t).differentialCoeff ζ ∈ (γ t).toValuationSubring)
    (g h : unitInterval → ℂ) (hg : IsPrimitiveAlong N η γ g)
    (hh : IsPrimitiveAlong N ζ γ h) :
    IsPrimitiveAlong N (η - ζ) γ (fun t => g t - h t) := by
  intro t₀
  obtain ⟨Φ, hΦ, hgf⟩ := hg t₀
  obtain ⟨Ψ, hΨ, hhf⟩ := hh t₀
  refine ⟨fun z => Φ z - Ψ z, ?_, ?_⟩
  · rw [placeChart_self] at hΦ hΨ ⊢
    filter_upwards [hΦ, hΨ, readDifferential_sub_of_coeff_mem N (γ t₀) η ζ
      (hη t₀) (hζ t₀)] with z hz1 hz2 he
    rw [he]
    exact hz1.sub hz2
  · filter_upwards [hgf, hhf] with t ht1 ht2
    rw [ht1, ht2]

theorem pathIntegral_sub_of_coeff_mem (η ζ : Ω[F⁄ℂ])
    {P Q : Place ℂ F} (γ : Path P Q)
    (hη : ∀ t, (γ t).differentialCoeff η ∈ (γ t).toValuationSubring)
    (hζ : ∀ t, (γ t).differentialCoeff ζ ∈ (γ t).toValuationSubring) :
    pathIntegral N (η - ζ) γ = pathIntegral N η γ - pathIntegral N ζ γ := by
  obtain ⟨g, hg⟩ := exists_isPrimitiveAlong_of_coeff_mem N η γ hη
  obtain ⟨h, hh⟩ := exists_isPrimitiveAlong_of_coeff_mem N ζ γ hζ
  rw [pathIntegral_eq_of_isPrimitiveAlong N
    (isPrimitiveAlong_sub_of_coeff_mem N η ζ γ hη hζ g h hg hh),
    pathIntegral_eq_of_isPrimitiveAlong N hg, pathIntegral_eq_of_isPrimitiveAlong N hh]
  ring

end
end Dubon2026.SourceFunctionField.OriginalChart
