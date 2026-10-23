import Dubon2026.SourceModularResidueHom

/-! DUB-17/18 -> original Frobenius/inertia -> good/place reduction ->
degree-preserving reduction coordinate. The actual internal j coordinate is
integral in the constructed Gauss ring and reduces to the literal residue j.
The proved all-level degree theorem supplies equality and positivity of the
two coordinate degrees. Genus preservation and place comparison remain open. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open IntermediateField SourceLevelProjective
variable {L : Type*} [Field L] (A : ValuationSubring L) (N : ℕ)
local notation "FF" => modularFunctionFieldCoeff N L
local notation "kk" => IsLocalRing.ResidueField A
local notation "Fb" => modularFunctionFieldCoeff N kk

theorem jCoeff_mem_gaussRing : jCoeff N L ∈ gaussRing A N := by
  refine ⟨jqModC A, 1, by simp, ?_⟩
  change jqModC L * ι A 1 = ι A (jqModC A)
  simp only [map_one, mul_one]
  exact (map_jqModC A.subtype).symm

theorem resHom_jCoeff :
    resHom A N ⟨jCoeff N L, jCoeff_mem_gaussRing A N⟩ = jqModC kk := by
  rw [resHom_eq A N (x := jqModC A) (y := 1) (by simp) (by
    change jqModC L * ι A 1 = ι A (jqModC A)
    simp only [map_one, mul_one]
    exact (map_jqModC A.subtype).symm)]
  simp only [map_one, div_one]
  exact map_jqModC (IsLocalRing.residue A)

variable [NeZero N] [IsAlgClosed L]

theorem modularResidueHom_jCoeff (hNL : (N : L) ≠ 0) (hNk : (N : kk) ≠ 0) :
    modularResidueHom A N hNL hNk ⟨jCoeff N L, jCoeff_mem_gaussRing A N⟩ =
      jCoeff N kk := Subtype.ext (resHom_jCoeff A N)

theorem reduction_coordinate_degree (hNL : (N : L) ≠ 0) (hNk : (N : kk) ≠ 0) :
    Module.finrank (IntermediateField.adjoin L ({jCoeff N L} : Set FF)) FF =
        Module.finrank (IntermediateField.adjoin kk ({jCoeff N kk} : Set Fb)) Fb ∧
      0 < Module.finrank (IntermediateField.adjoin kk ({jCoeff N kk} : Set Fb)) Fb := by
  letI := valuation_residue_isAlgClosed A
  rw [finrank_coeff_over_j_eq_psi N hNL, finrank_coeff_over_j_eq_psi N hNk]
  exact ⟨rfl, dedekindPsi_pos (NeZero.ne N)⟩

theorem exists_reduction_coordinate (hNL : (N : L) ≠ 0) (hNk : (N : kk) ≠ 0) :
    ∃ x : gaussRing A N, Transcendental kk (modularResidueHom A N hNL hNk x) ∧
      0 < Module.finrank
        (IntermediateField.adjoin kk ({modularResidueHom A N hNL hNk x} : Set Fb)) Fb ∧
      Module.finrank (IntermediateField.adjoin L ({(x : FF)} : Set FF)) FF =
        Module.finrank
          (IntermediateField.adjoin kk ({modularResidueHom A N hNL hNk x} : Set Fb)) Fb := by
  refine ⟨⟨jCoeff N L, jCoeff_mem_gaussRing A N⟩, ?_⟩
  rw [modularResidueHom_jCoeff]
  exact ⟨transcendental_jCoeff N kk, (reduction_coordinate_degree A N hNL hNk).2,
    (reduction_coordinate_degree A N hNL hNk).1⟩

end
end Dubon2026.SourceFunctionField.GaussReduction
