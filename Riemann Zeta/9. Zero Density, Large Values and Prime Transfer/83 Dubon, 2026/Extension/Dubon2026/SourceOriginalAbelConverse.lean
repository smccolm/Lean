import Dubon2026.SourceOriginalReindexedReciprocity
import Dubon2026.SourceOriginalAbelConverseFromRawReciprocity
import Dubon2026.SourceOriginalAbelPrincipalDivisors

/-! DUB-17/18 -> original torsion cardinality -> complex Abel-Jacobi comparison.
The original degree-zero Abel converse now has no geometric reciprocity,
period-generation or discreteness hypothesis. Every raw geometric clause is
constructed above; the existing prescribed-residue, period-correction and
meromorphic exponential argument then proves principality in the original
function field. Torsion cardinality and arithmetic comparison remain separate.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N]
attribute [local instance] placeTopology
local notation "F" => modularFunctionFieldOver N ℂ

theorem original_isPrincipal_of_abelJacobi_mem {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ F))
    (P₀ : Place ℂ F) (D : Divisor ℂ F) (hD0 : Divisor.degree D = 0)
    (hD : abelJacobiDiv N (fun i => (b i : Ω[F⁄ℂ])) P₀ D ∈
      pathPeriodLattice N (fun i => (b i : Ω[F⁄ℂ]))) :
    Divisor.IsPrincipal D := by
  obtain ⟨Pz, Z, Q, haway, _, hunit, hgen, hgenRes, hRR, hrec⟩ :=
    CellGeometry.exists_original_reindexed_reciprocity b P₀ D.support
  apply original_isPrincipal_of_raw_reciprocity N b P₀ D hD0 hD Pz Z Q
    (fun k t => Finsupp.notMem_support_iff.mp (haway k t).1) hunit hgen ?_ hRR ?_
  · intro P γ hγ
    obtain ⟨κ, w, hκ⟩ := hgenRes P γ (fun t => Finsupp.notMem_support_iff.mpr (hγ t))
    refine ⟨κ, w, fun η hη hreg => ?_⟩
    exact hκ η hη (fun v hv => hreg v (Finsupp.notMem_support_iff.mp hv))
  · intro η hη hres
    exact hrec D η hη hres (Finset.Subset.refl _)

theorem original_isPrincipal_iff_abelJacobi_mem {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ F))
    (P₀ : Place ℂ F) (D : Divisor ℂ F) (hD0 : Divisor.degree D = 0) :
    Divisor.IsPrincipal D ↔ abelJacobiDiv N (fun i => (b i : Ω[F⁄ℂ])) P₀ D ∈
      pathPeriodLattice N (fun i => (b i : Ω[F⁄ℂ])) :=
  ⟨original_abelJacobiDiv_mem_of_isPrincipal N (fun i => b i) P₀ D,
    original_isPrincipal_of_abelJacobi_mem N b P₀ D hD0⟩

end
end Dubon2026.SourceFunctionField.OriginalChart
