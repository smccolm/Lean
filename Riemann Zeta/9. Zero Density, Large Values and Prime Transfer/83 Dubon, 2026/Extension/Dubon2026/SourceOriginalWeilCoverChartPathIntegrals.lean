import Dubon2026.SourceOriginalWeilCoverAbelJacobiPeriods
import Mathlib.Analysis.Convex.PathConnected

/-! DUB-17/18 -> auxiliary point division -> cover Abel comparison.
The native original-curve path and local Abel arguments are adapted to the
literal Kummer splitting field and its constructed complex manifold.
All path and primitive inputs are proved; Abel inversion and its principal
kernel remain required. Adapted from anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
Def_AlgebraicCurve_ComplexLineIntegral and
S_AlgebraicCurve_exists_ball_abelJacobiVec_sub_sub_mem_pathPeriodLattice.
-/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (r : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C r : Polynomial FF)
variable (A : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hr : r ≠ 0)
variable (hrA : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord r = (n : ℤ) * A v)
include A hr hrA
local notation "CoverPath" => @Path (Place ℂ EE) (placeTopology N n r A hr hrA)

theorem isPrimitiveAlong_of_chart_primitive
    (ω : Ω[EE⁄ℂ])
    (hω : ω ∈ regularDifferentials ℂ (EE))
    (v : Place ℂ (EE)) (Φ : ℂ → ℂ)
    (hΦ : ∀ z ∈ ball (0 : ℂ) (placeRadius N n r A hr hrA v), HasDerivAt Φ (readDifferential N n r A hr hrA v ω z) z)
    {P Q : Place ℂ (EE)} (γ : CoverPath P Q)
    (hγ : ∀ t, γ t ∈ (placeChart N n r A hr hrA v).source) :
    IsPrimitiveAlong N n r A hr hrA ω γ (fun t => Φ (placeChart N n r A hr hrA v (γ t))) := by
  letI := placeTopology N n r A hr hrA
  intro t₀
  let T := chartRead N n r A hr hrA (γ t₀) v.uniformizer
  have hT : AnalyticAt ℂ T 0 := analyticAt_place_reading N n r A hr hrA (γ t₀)
    (uniformizer_regular_on_chart N n r A hr hrA v (γ t₀) (hγ t₀))
  have hT0 : T 0 ∈ ball 0 (placeRadius N n r A hr hrA v) := by
    change (placeFamily N n r A hr hrA (γ t₀) 0).rationalEval (originalWeilKummerCover_residue_bijective N ℂ n r _) v.uniformizer ∈ _
    rw [(place_spec N n r A hr hrA (γ t₀)).2.1]
    exact (placeChart N n r A hr hrA v).map_source (hγ t₀)
  have hb : ∀ᶠ z in 𝓝 (0 : ℂ), T z ∈ ball 0 (placeRadius N n r A hr hrA v) :=
    hT.continuousAt.eventually (isOpen_ball.mem_nhds hT0)
  refine ⟨Φ ∘ T, ?_, ?_⟩
  · rw [placeChart_self]
    filter_upwards [readDifferential_change N n r A hr hrA v (γ t₀) ω hω (hγ t₀),
      hT.eventually_analyticAt, hb] with z hchange hz hzb
    rw [hchange]
    exact (hΦ (T z) hzb).comp z hz.differentiableAt.hasDerivAt
  · have hm : ∀ᶠ t in 𝓝 t₀, γ t ∈ (placeChart N n r A hr hrA (γ t₀)).source :=
      γ.continuous.continuousAt.eventually (placeChart_source_mem_nhds N n r A hr hrA (γ t₀))
    filter_upwards [hm] with t ht
    change Φ (placeChart N n r A hr hrA v (γ t)) =
      Φ (placeChart N n r A hr hrA v (placeFamily N n r A hr hrA (γ t₀) (placeChart N n r A hr hrA (γ t₀) (γ t))))
    rw [show placeFamily N n r A hr hrA (γ t₀) (placeChart N n r A hr hrA (γ t₀) (γ t)) = γ t from
      (placeChart N n r A hr hrA (γ t₀)).left_inv ht]

theorem exists_cover_chart_path (v : Place ℂ (EE))
    {z : ℂ} (hz : z ∈ ball 0 (placeRadius N n r A hr hrA v)) :
    ∃ γ : CoverPath v (placeFamily N n r A hr hrA v z), ∀ t, γ t ∈ (placeChart N n r A hr hrA v).source := by
  letI := placeTopology N n r A hr hrA
  have h0 : (0 : ℂ) ∈ ball 0 (placeRadius N n r A hr hrA v) := mem_ball_self (place_spec N n r A hr hrA v).1
  obtain ⟨δ, hδ⟩ := ((convex_ball (0 : ℂ) (placeRadius N n r A hr hrA v)).isPathConnected ⟨0, h0⟩).joinedIn
    0 h0 z hz
  have hc : ContinuousOn (placeFamily N n r A hr hrA v) (range δ) :=
    (continuousOn_placeFamily N n r A hr hrA v).mono (by rintro _ ⟨t, rfl⟩; exact hδ t)
  refine ⟨(δ.map' hc).cast (place_spec N n r A hr hrA v).2.1.symm rfl, ?_⟩
  intro t
  exact ⟨δ t, hδ t, rfl⟩

theorem exists_cover_chart_path_integrals {k : ℕ}
    (b : Fin k → Ω[EE⁄ℂ])
    (hb : ∀ i, b i ∈ regularDifferentials ℂ (EE))
    (v : Place ℂ (EE)) (Φ : Fin k → ℂ → ℂ)
    (hΦ : ∀ i, ∀ z ∈ ball (0 : ℂ) (placeRadius N n r A hr hrA v),
      HasDerivAt (Φ i) (readDifferential N n r A hr hrA v (b i) z) z)
    {z : ℂ} (hz : z ∈ ball 0 (placeRadius N n r A hr hrA v)) :
    ∃ γ : CoverPath v (placeFamily N n r A hr hrA v z), ∀ i, pathIntegral N n r A hr hrA (b i) γ = Φ i z - Φ i 0 := by
  letI := placeTopology N n r A hr hrA
  obtain ⟨γ, hγ⟩ := exists_cover_chart_path N n r A hr hrA v hz
  refine ⟨γ, fun i => ?_⟩
  rw [pathIntegral_eq_of_isPrimitiveAlong N n r A hr hrA
    (isPrimitiveAlong_of_chart_primitive N n r A hr hrA (b i) (hb i) v (Φ i) (hΦ i) γ hγ)]
  rw [γ.target, γ.source, placeChart_self]
  have he : placeChart N n r A hr hrA v (placeFamily N n r A hr hrA v z) = z := place_eval_uniformizer N n r A hr hrA v hz
  rw [he]

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
