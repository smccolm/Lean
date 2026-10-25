import Dubon2026.SourceFiniteCycleResidueLinearity
import Dubon2026.SourceOriginalWeilCoverMeromorphicLoopPeriodsV2
import Dubon2026.SourceOriginalWeilCoverPathIntegralFiniteRegularity
import Dubon2026.SourceOriginalWeilCoverSimplePoleBasis
import Dubon2026.SourceOriginalWeilCoverWeightedResidueJumpSum

/-! DUB-17/18 -> cover Abel converse -> meromorphic loop generation.
The actual finite simple-pole basis extends the common integer formula to
every allowed differential, using pathwise linearity and actual linear residues.
Adapted from the existing original-curve proof and anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Set Filter Complex KaehlerDifferential CellGeometry
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


local notation "res" => fun (v : Place ℂ EE) (θ : Ω[EE⁄ℂ]) => Place.rationalEval v
  (originalWeilKummerCover_residue_bijective N ℂ n radicand v)
    (Place.uniformizer v * Place.differentialCoeff v θ)

/-- One integer cycle/residue formula per loop, shared by every allowed differential. -/
def CoverMeromorphicCycleGeneration :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    (D : RadialCellDissection (Place ℂ EE)) → Finset (Place ℂ EE) →
      Finset D.ιE → Finset D.ιE →
      ((j : D.ιE) → Path (D.vert (D.ends j).1) (D.vert (D.ends j).1)) → Prop := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  exact fun D S T Ts γ =>
    ∀ (P : Place ℂ EE) (δ : Path P P), (∀ t, δ t ∉ S) →
      ∃ (a : D.ιE → ℤ) (w : Place ℂ EE → ℤ), ∀ ϑ : Ω[EE⁄ℂ],
        (∀ v : Place ℂ EE, -1 ≤ v.ordDifferential ϑ) →
        (∀ v : Place ℂ EE, v ∉ S → 0 ≤ v.ordDifferential ϑ) →
        pathIntegral N n radicand baseDivisor hRadicand hOrders ϑ δ =
          ∑ l ∈ (T ∪ Ts)ᶜ, (a l : ℂ) * pathIntegral N n radicand baseDivisor hRadicand hOrders ϑ (γ l) +
          2 * Real.pi * Complex.I * ∑ v ∈ S, (w v : ℂ) * res v ϑ

theorem cover_meromorphic_cycle_generation_of_basis :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (𝒟 : RadialCellDissection (Place ℂ EE))
      (S : Finset (Place ℂ EE)), PolePos 𝒟 S → ∀ {d : ℕ}
      (bT : Module.Basis (Fin d) ℂ (coverSimplePoleSpace N n radicand S))
      (T Ts : Finset 𝒟.ιE)
      (γ : (j : 𝒟.ιE) → Path (𝒟.vert (𝒟.ends j).1) (𝒟.vert (𝒟.ends j).1)),
      (∀ j t, γ j t ∈ 𝒟.skeleton) →
      CoverMeromorphicFamilyGeneration N n radicand baseDivisor hRadicand hOrders
        𝒟 S (fun r => (bT r : Ω[EE⁄ℂ])) T Ts γ →
      CoverMeromorphicCycleGeneration N n radicand baseDivisor hRadicand hOrders 𝒟 S T Ts γ := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro 𝒟 S hS d bT T Ts γ hγs hfamily
  classical
  unfold CoverMeromorphicCycleGeneration
  intro Pt δ hδ
  let θ : Fin d → Ω[EE⁄ℂ] := fun r => (bT r : Ω[EE⁄ℂ])
  have hθ : ∀ r v, -1 ≤ v.ordDifferential (θ r) ∧ (v ∉ S → 0 ≤ v.ordDifferential (θ r)) :=
    fun r v => (bT r).2 v
  have hsk : ∀ r, ∀ v ∈ 𝒟.skeleton, 0 ≤ v.ordDifferential (θ r) := fun r =>
    cover_regular_on_skeleton N n radicand baseDivisor hRadicand hOrders 𝒟 S
      (fun v hv => ⟨_, (hS.hd5 v hv).choose_spec.1⟩) (θ r)
      (fun v hv => (hθ r v).2 hv)
  change CoverMeromorphicFamilyGeneration N n radicand baseDivisor hRadicand hOrders
    𝒟 S θ T Ts γ at hfamily
  obtain ⟨c, m, hcm⟩ := hfamily Pt δ hδ
  refine ⟨c, fun v => ∑ D, if v ∈ (𝒟.cell D).interior' then m D else 0, fun ϑ h1 h2 => ?_⟩
  have hϑ : ϑ ∈ coverSimplePoleSpace N n radicand S := fun v => ⟨h1 v, h2 v⟩
  let a : Fin d → ℂ := fun r => bT.repr ⟨ϑ, hϑ⟩ r
  have hexp : ϑ = ∑ r, a r • θ r := by
    have h := congrArg Subtype.val (bT.sum_repr ⟨ϑ, hϑ⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    exact h.symm
  have hδsum : pathIntegral N n radicand baseDivisor hRadicand hOrders ϑ δ = ∑ r, a r * pathIntegral N n radicand baseDivisor hRadicand hOrders (θ r) δ := by
    conv_lhs => rw [hexp]
    exact pathIntegral_sum_smul_of_coeff_mem N n radicand baseDivisor hRadicand hOrders a θ δ
      (fun r t => (δ t).mem_of_ord_nonneg ((hθ r (δ t)).2 (hδ t)))
  have hγsum : ∀ l, pathIntegral N n radicand baseDivisor hRadicand hOrders ϑ (γ l) = ∑ r, a r * pathIntegral N n radicand baseDivisor hRadicand hOrders (θ r) (γ l) := by
    intro l
    conv_lhs => rw [hexp]
    exact pathIntegral_sum_smul_of_coeff_mem N n radicand baseDivisor hRadicand hOrders a θ (γ l)
      (fun r t => (γ l t).mem_of_ord_nonneg (hsk r _ (hγs l t)))
  have hres : ∀ v, res v ϑ = ∑ r, a r * res v (θ r) := by
    intro v
    calc res v ϑ = coverDifferentialResidue N n radicand v ϑ :=
          (coverDifferentialResidue_simplePole N n radicand v ϑ (h1 v)).symm
      _ = ∑ r, a r * coverDifferentialResidue N n radicand v (θ r) := by
          rw [hexp, map_sum]
          simp only [map_smul, smul_eq_mul]
      _ = ∑ r, a r * res v (θ r) := by
          apply Finset.sum_congr rfl
          intro r _
          rw [coverDifferentialResidue_simplePole N n radicand v (θ r) (hθ r v).1]
  rw [hδsum]
  simp_rw [hcm]
  simp only [ρ, Finset.sum_apply]
  rw [sum_linear_combination_cycle_residue]
  simp_rw [← hγsum, ← hres]

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
