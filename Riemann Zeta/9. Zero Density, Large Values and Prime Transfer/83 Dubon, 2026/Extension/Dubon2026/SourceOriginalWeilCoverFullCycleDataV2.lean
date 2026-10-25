import Dubon2026.SourceOriginalWeilCoverMeromorphicGenerationV2
import Dubon2026.SourceOriginalWeilCoverMeromorphicJumpCycleData

/-! DUB-17/18 -> actual cover Abel converse. The constructed 2g complementary
cycles now carry regular and meromorphic generation, unimodularity, and both
reciprocity identities together. Only final prescribed indexing remains
before applying the existing raw-reciprocity Abel converse. -/
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



theorem exists_cover_full_cycle_data {kDim : ℕ}
    (b : Module.Basis (Fin kDim) ℂ (regularDifferentials ℂ EE))
    (P₀ : Place ℂ EE) (S : Finset (Place ℂ EE)) :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∃ (D : RadialCellDissection (Place ℂ EE)) (T Ts : Finset D.ιE)
      (Ψ : Fin kDim → D.ιC → ℂ → ℂ) (J : D.ιE → Fin kDim → ℂ)
      (γ : (j : D.ιE) → Path (D.vert (D.ends j).1) (D.vert (D.ends j).1)),
      (T ∪ Ts)ᶜ.card = 2 * Module.finrank ℂ (regularDifferentials ℂ EE) ∧
      (∀ j t, γ j t ∉ S) ∧
      CoverThirdKindCyclePeriodPolygonConclusion N n radicand baseDivisor hRadicand hOrders
        D (fun i : Fin kDim => (b i : Ω[EE⁄ℂ])) T Ts J γ P₀ S Ψ ∧
      CoverRegularCycleGeneration N n radicand baseDivisor hRadicand hOrders
        D (fun i : Fin kDim => (b i : Ω[EE⁄ℂ])) T Ts γ ∧
      CoverMeromorphicCycleGeneration N n radicand baseDivisor hRadicand hOrders D S T Ts γ := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  have h :=
    exists_cover_meromorphic_jump_cycle_data.{0} N n radicand baseDivisor hRadicand hOrders b P₀ S
  obtain ⟨D, hinj, hD, T, Ts, Z, hc, hword, hZ, hthird, hjump⟩ := h
  obtain ⟨C₀, V, Ψ, J, _, _, _, _, _, _, _, _, _, _, γ, hγs, hγi, hrec, hreg⟩ := hthird
  have hmer := cover_meromorphic_cycle_generation_of_jump_data N n radicand baseDivisor hRadicand hOrders
    D hD S T Ts Z γ hγs hγi hjump
  obtain ⟨d, bθ, Vθ, Ψθ, Jθ, _, hS, _, _, _, _⟩ := hjump
  refine ⟨D, T, Ts, Ψ, J, γ, hc, ?_, hrec, hreg, hmer⟩
  intro j t hv
  exact D.pole_not_mem_skeleton S (fun v h => ⟨_, (hS.hd5 v h).choose_spec.1⟩) hv (hγs j t)

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
