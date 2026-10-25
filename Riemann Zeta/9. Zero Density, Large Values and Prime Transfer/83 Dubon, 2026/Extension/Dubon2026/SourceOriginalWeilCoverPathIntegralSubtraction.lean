import Dubon2026.SourceOriginalWeilCoverRegularPathPrimitives
import Dubon2026.SourceOriginalWeilCoverDifferentialResidues
import Dubon2026.SourceOriginalWeilCoverReadFieldLaws

/-! DUB-17/18 -> auxiliary point division -> cover Abel converse -> integral-period exponential and principality. Adapt the native original-curve deduction to the literal cover, using proved chart, residue and meromorphic comparison inputs. No global regularity or completed Abel converse is assumed. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential OriginalPrimitiveGlue
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n] (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (A : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * A v)
include A hRadicand hOrders
local notation "CoverPath" => @Path (Place ℂ EE) (placeTopology N n radicand A hRadicand hOrders)

omit A hRadicand hOrders [NeZero n] in
theorem cover_differentialCoeff_sub (v : Place ℂ EE) (η ζ : Ω[EE⁄ℂ]) :
    v.differentialCoeff (η - ζ) = v.differentialCoeff η - v.differentialCoeff ζ :=
  (coverDifferentialCoeff N n radicand v).map_sub η ζ

theorem readDifferential_sub_of_coeff_mem (v : Place ℂ EE) (η ζ : Ω[EE⁄ℂ])
    (hη : v.differentialCoeff η ∈ v.toValuationSubring)
    (hζ : v.differentialCoeff ζ ∈ v.toValuationSubring) :
    readDifferential N n radicand A hRadicand hOrders v (η - ζ) =ᶠ[𝓝 (0 : ℂ)]
      fun z => readDifferential N n radicand A hRadicand hOrders v η z - readDifferential N n radicand A hRadicand hOrders v ζ z := by
  letI := placeTopology N n radicand A hRadicand hOrders
  have hs : v.differentialCoeff (η - ζ) ∈ v.toValuationSubring := by
    rw [cover_differentialCoeff_sub]
    exact sub_mem hη hζ
  apply (ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    (analyticAt_readDifferential_of_coeff_mem N n radicand A hRadicand hOrders v (η - ζ) hs).continuousAt
    ((analyticAt_readDifferential_of_coeff_mem N n radicand A hRadicand hOrders v η hη).continuousAt.sub
      (analyticAt_readDifferential_of_coeff_mem N n radicand A hRadicand hOrders v ζ hζ).continuousAt)).mp
  have hball : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ ball 0 (placeRadius N n radicand A hRadicand hOrders v) :=
    nhdsWithin_le_nhds (ball_mem_nhds (0 : ℂ) (place_spec N n radicand A hRadicand hOrders v).1)
  filter_upwards [chartRead_add N n radicand A hRadicand hOrders v (v.differentialCoeff η) (-v.differentialCoeff ζ),
    chartRead_neg N n radicand A hRadicand hOrders v (v.differentialCoeff ζ), hball]
    with z ha hn hz
  rw [readDifferential_eq_coefficient N n radicand A hRadicand hOrders v (η - ζ) hz,
    readDifferential_eq_coefficient N n radicand A hRadicand hOrders v η hz, readDifferential_eq_coefficient N n radicand A hRadicand hOrders v ζ hz]
  rw [cover_differentialCoeff_sub, sub_eq_add_neg (v.differentialCoeff η) (v.differentialCoeff ζ), ha, Pi.add_apply, hn]
  rfl

theorem isPrimitiveAlong_sub_of_coeff_mem (η ζ : Ω[EE⁄ℂ])
    {P Q : Place ℂ EE} (γ : CoverPath P Q)
    (hη : ∀ t, (γ t).differentialCoeff η ∈ (γ t).toValuationSubring)
    (hζ : ∀ t, (γ t).differentialCoeff ζ ∈ (γ t).toValuationSubring)
    (g h : unitInterval → ℂ) (hg : IsPrimitiveAlong N n radicand A hRadicand hOrders η γ g)
    (hh : IsPrimitiveAlong N n radicand A hRadicand hOrders ζ γ h) :
    IsPrimitiveAlong N n radicand A hRadicand hOrders (η - ζ) γ (fun t => g t - h t) := by
  letI := placeTopology N n radicand A hRadicand hOrders
  intro t₀
  obtain ⟨Φ, hΦ, hgf⟩ := hg t₀
  obtain ⟨Ψ, hΨ, hhf⟩ := hh t₀
  refine ⟨fun z => Φ z - Ψ z, ?_, ?_⟩
  · rw [placeChart_self] at hΦ hΨ ⊢
    filter_upwards [hΦ, hΨ, readDifferential_sub_of_coeff_mem N n radicand A hRadicand hOrders (γ t₀) η ζ
      (hη t₀) (hζ t₀)] with z hz1 hz2 he
    rw [he]
    exact hz1.sub hz2
  · filter_upwards [hgf, hhf] with t ht1 ht2
    rw [ht1, ht2]

theorem pathIntegral_sub_of_coeff_mem (η ζ : Ω[EE⁄ℂ])
    {P Q : Place ℂ EE} (γ : CoverPath P Q)
    (hη : ∀ t, (γ t).differentialCoeff η ∈ (γ t).toValuationSubring)
    (hζ : ∀ t, (γ t).differentialCoeff ζ ∈ (γ t).toValuationSubring) :
    pathIntegral N n radicand A hRadicand hOrders (η - ζ) γ = pathIntegral N n radicand A hRadicand hOrders η γ - pathIntegral N n radicand A hRadicand hOrders ζ γ := by
  letI := placeTopology N n radicand A hRadicand hOrders
  obtain ⟨g, hg⟩ := exists_isPrimitiveAlong_of_coeff_mem N n radicand A hRadicand hOrders η γ hη
  obtain ⟨h, hh⟩ := exists_isPrimitiveAlong_of_coeff_mem N n radicand A hRadicand hOrders ζ γ hζ
  rw [pathIntegral_eq_of_isPrimitiveAlong N n radicand A hRadicand hOrders
    (isPrimitiveAlong_sub_of_coeff_mem N n radicand A hRadicand hOrders η ζ γ hη hζ g h hg hh),
    pathIntegral_eq_of_isPrimitiveAlong N n radicand A hRadicand hOrders hg, pathIntegral_eq_of_isPrimitiveAlong N n radicand A hRadicand hOrders hh]
  ring


end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
