import Dubon2026.SourceRadialPoleAvoidingNeighborhoods
import Dubon2026.SourceMeromorphicLocalLog

/-! DUB-17/18 -> cover Abel converse -> meromorphic path-to-jump comparison.
Use the existing local logarithm and principal cell readings to define the
corrected local atlas. Its value at the center is exactly the chosen reading. -/
namespace Dubon2026.SourceFunctionField.CellGeometry.RadialMeromorphicPeriods
noncomputable section
open Set RadialDissectionPeriods
open MeromorphicPeriods (Lg Lg_self)
variable {X R : Type*} [TopologicalSpace X]

/-- The cell primitive with a logarithmic branch centered at the chosen place. -/
noncomputable def Φloc {𝒟 : RadialCellDissection X} (S : Finset (X)) (residue : X → R → ℂ) (Ψ : R → 𝒟.ιC → ℂ → ℂ) (D : 𝒟.ιC) (x z : X) : R → ℂ :=
  fun r => Ψ r D ((𝒟.cell D).ζ z) + ρ 𝒟 S residue D r * Lg (𝒟.cell D).R.q ((𝒟.cell D).ζ x) ((𝒟.cell D).ζ z)

theorem Φloc_self {𝒟 : RadialCellDissection X} (S : Finset (X)) (residue : X → R → ℂ) (Ψ : R → 𝒟.ιC → ℂ → ℂ) (D : 𝒟.ιC) (x : X) :
    Φloc S residue Ψ D x x = pval S residue Ψ D x := by
  funext r
  simp only [Φloc, pval, Lg_self]

/-- A local primitive chart corrected by the fixed cell readings at its center. -/
noncomputable def Gθ {𝒟 : RadialCellDissection X} (S : Finset (X)) (residue : X → R → ℂ) (Ψ : R → 𝒟.ιC → ℂ → ℂ) (x y : X) : R → ℂ :=
  Φloc S residue Ψ (cellOf 𝒟 y) x y - pval S residue Ψ (cellOf 𝒟 y) x + pval S residue Ψ (cellOf 𝒟 x) x

theorem Gθ_self {𝒟 : RadialCellDissection X} (S : Finset (X)) (residue : X → R → ℂ) (Ψ : R → 𝒟.ιC → ℂ → ℂ) (x : X) :
    Gθ S residue Ψ x x = pval S residue Ψ (cellOf 𝒟 x) x := by
  rw [Gθ, Φloc_self]; abel


end
end Dubon2026.SourceFunctionField.CellGeometry.RadialMeromorphicPeriods
