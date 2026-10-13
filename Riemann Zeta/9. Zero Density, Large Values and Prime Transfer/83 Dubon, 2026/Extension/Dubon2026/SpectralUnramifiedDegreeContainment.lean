import Dubon2026.CyclicGaloisDegreeContainment
import Dubon2026.SpectralUnramifiedInvariantCompatibility
import Dubon2026.UnramifiedLocalFieldResidueGalois
import Mathlib.FieldTheory.Finite.GaloisField

/-! # Containment of actual unramified stages from their degrees

This supplies the actual tower needed by characteristic-degree H2 inflation,
then unramified vanishing and finite local support before DUB-17 global duality.
The existing spectral compositum and residue Galois theorems are reused.
-/

namespace Dubon2026
noncomputable section
open scoped ValuativeRel

variable {K Ω : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω]

/-- Degree divisibility gives literal containment of original spectral
unramified finite Galois stages in the same ambient field. -/
theorem spectralUnramifiedStage_le_of_finrank_dvd
    (E F : FiniteGaloisIntermediateField K Ω)
    (hE : SpectralStageUnramified K Ω E) (hF : SpectralStageUnramified K Ω F)
    (hdegree : Module.finrank K E ∣ Module.finrank K F) : E ≤ F := by
  let H := E ⊔ F
  let i := IntermediateField.inclusion
    (show E.toIntermediateField ≤ H.toIntermediateField from le_sup_left)
  letI : NontriviallyNormedField H := spectralNorm.nontriviallyNormedField K H
  letI : NormedAlgebra K H := spectralNorm.normedAlgebra K H
  letI : IsUltrametricDist H := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel H := ValuativeRel.ofValuation (NormedField.valuation (K := H))
  haveI : IsNonarchimedeanLocalField H := spectralFiniteExtension_isNonarchimedeanLocalField K H
  haveI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation H) :=
    spectralValuation_hasExtension K H
  haveI : Algebra.FormallyUnramified 𝒪[K] 𝒪[H] := spectralStageUnramified_sup K Ω E F hE hF
  haveI : IsCyclic Gal(H/K) :=
    (unramifiedLocalFieldResidueGaloisEquiv K H).isCyclic.mpr inferInstance
  let j := IntermediateField.inclusion
    (show F.toIntermediateField ≤ H.toIntermediateField from le_sup_right)
  have hd : Module.finrank K i.fieldRange ∣ Module.finrank K j.fieldRange := by
    change Module.finrank K i.range ∣ Module.finrank K j.range
    rw [← (AlgEquiv.ofInjectiveField i).toLinearEquiv.finrank_eq,
      ← (AlgEquiv.ofInjectiveField j).toLinearEquiv.finrank_eq]
    exact hdegree
  have hle := cyclicGaloisIntermediateField_le_of_finrank_dvd i.fieldRange j.fieldRange hd
  intro x hx
  have hi : i ⟨x, hx⟩ ∈ i.fieldRange := ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨y, hy⟩ := hle hi
  have heq : (y : Ω) = x := congrArg (fun z : H => (z : Ω)) hy
  exact heq ▸ y.property

end
end Dubon2026
