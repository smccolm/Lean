import Dubon2026.SourceOriginalWeilCoverFullCycleDataV2
import Dubon2026.SourceOriginalWeilCoverReciprocityReindex

/-! DUB-17/18 -> actual cover Abel converse. The same constructed cycles and
reciprocity matrix provide every raw geometric input on the prescribed 2g
index. No geometric generation, matrix or reciprocity hypothesis is supplied. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n] (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (baseDivisor : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * baseDivisor v)
include baseDivisor hRadicand hOrders
local notation "CoverPath" => @Path (Place ℂ EE) (placeTopology N n radicand baseDivisor hRadicand hOrders)


theorem exists_cover_reindexed_reciprocity {kDim : ℕ}
    (b : Module.Basis (Fin kDim) ℂ (regularDifferentials ℂ EE))
    (P₀ : Place ℂ EE) (S : Finset (Place ℂ EE)) :
    CoverRawReciprocityData N n radicand baseDivisor hRadicand hOrders
      (fun i : Fin kDim => (b i : Ω[EE⁄ℂ])) P₀ S := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  obtain ⟨D, T, Ts, Ψ, J, γ, hc, haway, hrec, hR, hG⟩ :=
    exists_cover_full_cycle_data N n radicand baseDivisor hRadicand hOrders b P₀ S
  have hn : Module.finrank ℂ (regularDifferentials ℂ EE) = kDim := by
    simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis b
  exact reindex_cover_reciprocity N n radicand baseDivisor hRadicand hOrders D
    (fun i : Fin kDim => (b i : Ω[EE⁄ℂ])) P₀ S T Ts Ψ J γ
    (hc.trans (congrArg (fun z => 2 * z) hn)) haway hR hG hrec

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
