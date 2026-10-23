import Dubon2026.SourceModularGaussResidueImage

/-! DUB-17/18 -> original Frobenius/inertia -> good/place reduction ->
surjectivity onto the actual residue modular field. The constructed residue
range is a field because its kernel is the Gauss maximal ideal. Lifts of
constants and divisor-j elements contain every required generator. No abstract
residue-surjectivity hypothesis is supplied. Adapted from the archived FLT
construction of reduction on constants and the existing actual coefficient maps. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open IntermediateField
variable {L : Type*} [Field L] (A : ValuationSubring L) (N : ℕ)
local notation "FF" => modularFunctionFieldCoeff N L
local notation "kk" => IsLocalRing.ResidueField A

theorem exists_resHom_eq {z : LaurentSeries kk} (hz : z ∈ modularFunctionFieldCoeff N kk) :
    ∃ f : gaussRing A N, resHom A N f = z := by
  let S : Subfield (LaurentSeries kk) :=
    { carrier := Set.range (resHom A N)
      mul_mem' := by rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩; exact ⟨f * g, map_mul _ _ _⟩
      one_mem' := ⟨1, map_one _⟩
      add_mem' := by rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩; exact ⟨f + g, map_add _ _ _⟩
      zero_mem' := ⟨0, map_zero _⟩
      neg_mem' := by rintro _ ⟨f, rfl⟩; exact ⟨-f, map_neg _ _⟩
      inv_mem' := by
        rintro _ ⟨f, rfl⟩
        by_cases h0 : resHom A N f = 0
        · exact ⟨0, by rw [h0, inv_zero, map_zero]⟩
        · have hu : IsUnit f := by
            by_contra hu
            exact h0 ((resHom_eq_zero_iff A N f).mpr
              ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hu)))
          obtain ⟨u, rfl⟩ := hu
          refine ⟨↑u⁻¹, ?_⟩
          exact (inv_eq_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])).symm }
  have hle : Subfield.closure (Set.range (algebraMap kk (LaurentSeries kk)) ∪ divisorExpansionsCoeff N kk)
      ≤ S := by
    rw [Subfield.closure_le]
    rintro z (⟨t, rfl⟩ | ⟨d, hd, hdN, rfl⟩)
    · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective t
      exact ⟨⟨_, (algebraMap_mem_gaussRing_iff A N (a : L)).mpr a.2⟩, resHom_algebraMap A N a _⟩
    · have hmem : ι A (qExpand A d (jqModC A)) ∈ FF := by
        rw [show ι A (qExpand A d (jqModC A)) = qExpand L d (jqModC L) from
          coefficientMap_j_expansion A.subtype d]
        exact jqd_mem_coeff_field N L hdN
      exact ⟨_, (resHom_ι A N hmem).trans (coefficientMap_j_expansion (IsLocalRing.residue A) d)⟩
  obtain ⟨f, hf⟩ := hle (show z ∈ Subfield.closure _ from hz)
  exact ⟨f, hf⟩

end
end Dubon2026.SourceFunctionField.GaussReduction
