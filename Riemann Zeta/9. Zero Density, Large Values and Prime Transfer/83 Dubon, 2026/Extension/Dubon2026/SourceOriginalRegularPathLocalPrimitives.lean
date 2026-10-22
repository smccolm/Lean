import Dubon2026.SourceOriginalLocalRegularPrimitives
import Dubon2026.SourceOriginalPathLocalPrimitives

/-! DUB-17/18 -> Abel-Jacobi converse -> period correction and meromorphic
exponential. Along a continuous path regularity at each traversed original
place supplies small primitives. Actual coordinate changes transport them
to the charts used by the existing path-integral definition. The primitive
disk is shrunk locally; global regularity is not required or inferred.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential OriginalPrimitiveGlue
open scoped Topology
variable (N : ℕ) [NeZero N]

theorem exists_original_path_local_primitive_of_coeff_mem
    (ω : Ω[modularFunctionFieldOver N ℂ⁄ℂ])
    (c : ℝ → Place ℂ (modularFunctionFieldOver N ℂ))
    (hc : letI := placeTopology N; Continuous c)
    (hω : ∀ t, (c t).differentialCoeff ω ∈ (c t).toValuationSubring) (s : ℝ) :
    ∃ G : ℝ → ℂ, ∀ᶠ t₀ in 𝓝 s,
      IsPrimNear (fun t z => readDifferential N (c t) ω z)
        (fun t₀ t => placeChart N (c t₀) (c t)) G t₀ := by
  letI := placeTopology N
  obtain ⟨r, hr, _, Φ, hΦ⟩ := exists_readDifferential_local_primitive N (c s) ω (hω s)
  refine ⟨fun t => Φ (placeChart N (c s) (c t)), ?_⟩
  have hs : ∀ᶠ t₀ in 𝓝 s, c t₀ ∈ (placeChart N (c s)).source :=
    hc.continuousAt.eventually (placeChart_source_mem_nhds N (c s))
  have hk : ContinuousAt (fun t => placeChart N (c s) (c t)) s :=
    (continuousAt_placeChart N (c s) (c s) (mem_placeChart_source N (c s))).comp hc.continuousAt
  have hsmall : ∀ᶠ t₀ in 𝓝 s, placeChart N (c s) (c t₀) ∈ ball (0 : ℂ) r :=
    hk.eventually (by dsimp only; rw [placeChart_self]; exact ball_mem_nhds 0 hr)
  filter_upwards [hs, hsmall] with t₀ ht₀ hsmall₀
  let T := chartRead N (c t₀) (c s).uniformizer
  have hT : AnalyticAt ℂ T 0 := analyticAt_place_reading N (c t₀)
    (uniformizer_regular_on_chart N (c s) (c t₀) ht₀)
  have hT0 : T 0 ∈ ball 0 r := by
    change originalPlaceEval N ℂ (placeFamily N (c t₀) 0) (c s).uniformizer ∈ _
    rw [(place_spec N (c t₀)).2.1]
    exact hsmall₀
  have hb : ∀ᶠ z in 𝓝 (0 : ℂ), T z ∈ ball 0 r :=
    hT.continuousAt.eventually (isOpen_ball.mem_nhds hT0)
  refine ⟨Φ ∘ T, ?_, ?_⟩
  · dsimp only
    rw [placeChart_self]
    filter_upwards [readDifferential_change_of_coeff_mem N (c s) (c t₀) ω (hω t₀) ht₀,
      hT.eventually_analyticAt, hb] with z hchange hz hzb
    rw [hchange]
    exact (hΦ (T z) hzb).comp z hz.differentiableAt.hasDerivAt
  · have hm : ∀ᶠ t in 𝓝 t₀, c t ∈ (placeChart N (c t₀)).source :=
      hc.continuousAt.eventually (placeChart_source_mem_nhds N (c t₀))
    filter_upwards [hm] with t ht
    change Φ (placeChart N (c s) (c t)) =
      Φ (placeChart N (c s) (placeFamily N (c t₀) (placeChart N (c t₀) (c t))))
    rw [show placeFamily N (c t₀) (placeChart N (c t₀) (c t)) = c t from
      (placeChart N (c t₀)).left_inv ht]


end
end Dubon2026.SourceFunctionField.OriginalChart
