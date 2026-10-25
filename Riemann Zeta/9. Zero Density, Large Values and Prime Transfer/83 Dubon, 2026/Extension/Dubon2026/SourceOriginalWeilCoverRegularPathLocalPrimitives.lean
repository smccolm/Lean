import Dubon2026.SourceOriginalWeilCoverLocalRegularPrimitives
import Dubon2026.SourceOriginalWeilCoverPathLocalPrimitives

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

theorem exists_cover_path_local_primitive_of_coeff_mem
    (ω : Ω[EE⁄ℂ])
    (c : ℝ → Place ℂ (EE))
    (hc : letI := placeTopology N n radicand A hRadicand hOrders; Continuous c)
    (hω : ∀ t, (c t).differentialCoeff ω ∈ (c t).toValuationSubring) (s : ℝ) :
    ∃ G : ℝ → ℂ, ∀ᶠ t₀ in 𝓝 s,
      IsPrimNear (fun t z => readDifferential N n radicand A hRadicand hOrders (c t) ω z)
        (fun t₀ t => placeChart N n radicand A hRadicand hOrders (c t₀) (c t)) G t₀ := by
  letI := placeTopology N n radicand A hRadicand hOrders
  obtain ⟨r, hr, _, Φ, hΦ⟩ := exists_readDifferential_local_primitive N n radicand A hRadicand hOrders (c s) ω (hω s)
  refine ⟨fun t => Φ (placeChart N n radicand A hRadicand hOrders (c s) (c t)), ?_⟩
  have hs : ∀ᶠ t₀ in 𝓝 s, c t₀ ∈ (placeChart N n radicand A hRadicand hOrders (c s)).source :=
    hc.continuousAt.eventually (placeChart_source_mem_nhds N n radicand A hRadicand hOrders (c s))
  have hk : ContinuousAt (fun t => placeChart N n radicand A hRadicand hOrders (c s) (c t)) s :=
    (continuousAt_placeChart N n radicand A hRadicand hOrders (c s) (c s) (mem_placeChart_source N n radicand A hRadicand hOrders (c s))).comp hc.continuousAt
  have hsmall : ∀ᶠ t₀ in 𝓝 s, placeChart N n radicand A hRadicand hOrders (c s) (c t₀) ∈ ball (0 : ℂ) r :=
    hk.eventually (by dsimp only; rw [placeChart_self]; exact ball_mem_nhds 0 hr)
  filter_upwards [hs, hsmall] with t₀ ht₀ hsmall₀
  let T := chartRead N n radicand A hRadicand hOrders (c t₀) (c s).uniformizer
  have hT : AnalyticAt ℂ T 0 := analyticAt_place_reading N n radicand A hRadicand hOrders (c t₀)
    (uniformizer_regular_on_chart N n radicand A hRadicand hOrders (c s) (c t₀) ht₀)
  have hT0 : T 0 ∈ ball 0 r := by
    change (placeFamily N n radicand A hRadicand hOrders (c t₀) 0).rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand _) (c s).uniformizer ∈ _
    rw [(place_spec N n radicand A hRadicand hOrders (c t₀)).2.1]
    exact hsmall₀
  have hb : ∀ᶠ z in 𝓝 (0 : ℂ), T z ∈ ball 0 r :=
    hT.continuousAt.eventually (isOpen_ball.mem_nhds hT0)
  refine ⟨Φ ∘ T, ?_, ?_⟩
  · dsimp only
    rw [placeChart_self]
    filter_upwards [readDifferential_change_of_coeff_mem N n radicand A hRadicand hOrders (c s) (c t₀) ω (hω t₀) ht₀,
      hT.eventually_analyticAt, hb] with z hchange hz hzb
    rw [hchange]
    exact (hΦ (T z) hzb).comp z hz.differentiableAt.hasDerivAt
  · have hm : ∀ᶠ t in 𝓝 t₀, c t ∈ (placeChart N n radicand A hRadicand hOrders (c t₀)).source :=
      hc.continuousAt.eventually (placeChart_source_mem_nhds N n radicand A hRadicand hOrders (c t₀))
    filter_upwards [hm] with t ht
    change Φ (placeChart N n radicand A hRadicand hOrders (c s) (c t)) =
      Φ (placeChart N n radicand A hRadicand hOrders (c s) (placeFamily N n radicand A hRadicand hOrders (c t₀) (placeChart N n radicand A hRadicand hOrders (c t₀) (c t))))
    rw [show placeFamily N n radicand A hRadicand hOrders (c t₀) (placeChart N n radicand A hRadicand hOrders (c t₀) (c t)) = c t from
      (placeChart N n radicand A hRadicand hOrders (c t₀)).left_inv ht]



end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
