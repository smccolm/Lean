import Dubon2026.SourceOriginalWeilCoverMeromorphicBasisExtensionV2
import Dubon2026.SourceOriginalWeilCoverMeromorphicJumpData

/-! DUB-17/18 -> cover Abel converse -> meromorphic loop generation.
Consume the actual normalized jump data and the very same skeleton loops
used by reciprocity. Their proved edge-integral identity converts jump
containment to cycle periods; the actual finite basis then discharges the
common-coefficient formula for every allowed differential. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Set Filter KaehlerDifferential CellGeometry
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (baseDivisor : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * baseDivisor v)
include baseDivisor hRadicand hOrders
local notation "PC" => placeChart N n radicand baseDivisor hRadicand hOrders
local notation "PF" => placeFamily N n radicand baseDivisor hRadicand hOrders
local notation "RD" => readDifferential N n radicand baseDivisor hRadicand hOrders
local notation "CF" => coverCoeffIn N n radicand baseDivisor hRadicand hOrders



open RadialMeromorphicPeriods RadialDissectionPeriods



theorem cover_meromorphic_cycle_generation_of_jump_data :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE)),
      (∀ C P, P ∈ (D.cell C).ζ.source →
        AnalyticAt ℂ ((D.cell C).ζ ∘ PF P) 0 ∧ deriv ((D.cell C).ζ ∘ PF P) 0 ≠ 0) →
      ∀ (S : Finset (Place ℂ EE)) (T Ts : Finset D.ιE) (Z : D.ιE → D.ιE → ℤ)
        (γ : (j : D.ιE) → Path (D.vert (D.ends j).1) (D.vert (D.ends j).1)),
      (∀ j t, γ j t ∈ D.skeleton) →
      (∀ j (θ : Ω[EE⁄ℂ]), (∀ v ∈ D.skeleton, 0 ≤ v.ordDifferential θ) →
        (∃ g, IsPrimitiveAlong N n radicand baseDivisor hRadicand hOrders θ (γ j) g) ∧
        pathIntegral N n radicand baseDivisor hRadicand hOrders θ (γ j) =
          ∑ e, (Z j e : ℂ) * coverEdgeIntegral N n radicand baseDivisor hRadicand hOrders D θ e) →
      CoverMeromorphicJumpData N n radicand baseDivisor hRadicand hOrders D S T Ts Z →
      CoverMeromorphicCycleGeneration N n radicand baseDivisor hRadicand hOrders D S T Ts γ := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D hD S T Ts Z γ hγs hγi hjump
  obtain ⟨d, bθ, V, Ψ, J, _, hS, hP, hJ, _, hmem⟩ := hjump
  let θ : Fin d → Ω[EE⁄ℂ] := fun i => bθ i
  have hθ : ∀ i v, -1 ≤ v.ordDifferential (θ i) ∧ (v ∉ S → 0 ≤ v.ordDifferential (θ i)) :=
    fun i v => (bθ i).property v
  have hsk : ∀ i, ∀ v ∈ D.skeleton, 0 ≤ v.ordDifferential (θ i) := fun i =>
    cover_regular_on_skeleton N n radicand baseDivisor hRadicand hOrders D S
      (fun v hv => ⟨_, (hS.hd5 v hv).choose_spec.1⟩) (θ i) (fun v hv => (hθ i v).2 hv)
  have he : (fun l i => pathIntegral N n radicand baseDivisor hRadicand hOrders (θ i) (γ l)) =
      zv Z (fun e i => coverEdgeIntegral N n radicand baseDivisor hRadicand hOrders D (θ i) e) := by
    funext l i
    rw [(hγi l (θ i) (hsk i)).2]
    simp only [zv, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply cover_meromorphic_cycle_generation_of_basis N n radicand baseDivisor hRadicand hOrders
    D S hS bθ T Ts γ hγs
  apply cover_meromorphic_family_generation_of_jumps N n radicand baseDivisor hRadicand hOrders
    D hD S θ hθ hS hP hJ T Ts γ
  intro e
  rw [he]
  exact hmem e

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
