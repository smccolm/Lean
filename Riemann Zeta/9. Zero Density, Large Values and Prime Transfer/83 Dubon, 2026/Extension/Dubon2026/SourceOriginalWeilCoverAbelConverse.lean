import Dubon2026.SourceOriginalWeilCoverReindexedReciprocity
import Dubon2026.SourceOriginalWeilCoverAbelConverseFromRawReciprocity

/-! DUB-17/18 -> auxiliary point division -> actual cover Abel converse.
The existing prescribed-residue, integer-period correction and meromorphic
exponential proof consumes every geometric clause from the constructed cover
cycles. The degree-zero Abel converse has no remaining generation, reciprocity
or period-discreteness hypothesis. Auxiliary division and arithmetic consumers
remain separate obligations. -/
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

theorem cover_isPrincipal_of_abelJacobi_mem {kDim : ℕ}
    (b : Module.Basis (Fin kDim) ℂ (regularDifferentials ℂ EE))
    (P₀ : Place ℂ EE) (D : Divisor ℂ EE) (hD0 : Divisor.degree D = 0)
    (hD : abelJacobiDiv N n radicand baseDivisor hRadicand hOrders (fun i => (b i : Ω[EE⁄ℂ])) P₀ D ∈
      pathPeriodLattice N n radicand baseDivisor hRadicand hOrders (fun i => (b i : Ω[EE⁄ℂ]))) :
    Divisor.IsPrincipal D := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  obtain ⟨Pz, Z, Q, haway, _, hunit, hgen, hgenRes, hRR, hrec⟩ :=
    exists_cover_reindexed_reciprocity N n radicand baseDivisor hRadicand hOrders b P₀ D.support
  apply cover_isPrincipal_of_raw_reciprocity N n radicand baseDivisor hRadicand hOrders b P₀ D hD0 hD Pz Z Q
    (fun k t => Finsupp.notMem_support_iff.mp (haway k t)) hunit hgen ?_ hRR ?_
  · intro P γ hγ
    obtain ⟨κ, w, hκ⟩ := hgenRes P γ (fun t => Finsupp.notMem_support_iff.mpr (hγ t))
    refine ⟨κ, w, fun η hη hreg => ?_⟩
    exact hκ η hη (fun v hv => hreg v (Finsupp.notMem_support_iff.mp hv))
  · intro η hη hres
    exact hrec D η hη hres (Finset.Subset.refl _)


end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
