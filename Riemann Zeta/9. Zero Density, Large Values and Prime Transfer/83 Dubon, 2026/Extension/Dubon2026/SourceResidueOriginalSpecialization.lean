import Dubon2026.SourceResidueIntegralSpecialization

/-! DUB-17/18 -> original Frobenius/inertia -> actual good/place reduction
-> specialization of the original arithmetic modular field. The original
rational-field scalar extension equals the actual coefficient-field divisor
construction, by their literal generators. Consequently every integral Laurent
member of that original arithmetic field reduces into the residue modular field.
The level is only required to be nonzero in the residue constants; no genus or
good-reduction assertion is made at this step. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open IntermediateField

theorem original_field_eq_coefficient_field (N : ℕ) (L : Type*) [Field L] [Algebra ℚ L] :
    modularFunctionFieldOver N L = modularFunctionFieldCoeff N L := by
  rw [modularFunctionFieldOver, laurentBaseChange_full_eq_adjoin, modularFunctionFieldCoeff]
  apply congrArg (IntermediateField.adjoin L)
  ext x
  constructor
  · rintro ⟨y, ⟨d, hd, hdN, rfl⟩, rfl⟩
    refine ⟨d, hd, hdN, ?_⟩
    exact coefficientMap_j_expansion (algebraMap ℚ L) d
  · rintro ⟨d, hd, hdN, rfl⟩
    refine ⟨qExpand ℚ d jq, ⟨d, hd, hdN, rfl⟩, ?_⟩
    exact coefficientMap_j_expansion (algebraMap ℚ L) d

theorem original_integral_laurent_specializes (N : ℕ) [NeZero N]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hNk : (N : IsLocalRing.ResidueField A) ≠ 0)
    (y : LaurentSeries A)
    (hy : coeffMap A.subtype y ∈ modularFunctionFieldOver N (AlgebraicClosure ℚ)) :
    coeffMap (IsLocalRing.residue A) y ∈ modularFunctionFieldCoeff N (IsLocalRing.ResidueField A) := by
  rw [original_field_eq_coefficient_field] at hy
  exact integral_modular_coefficient_specializes A N
    (Nat.cast_ne_zero.mpr (NeZero.ne N)) hNk y hy

end
end Dubon2026.SourceFunctionField
