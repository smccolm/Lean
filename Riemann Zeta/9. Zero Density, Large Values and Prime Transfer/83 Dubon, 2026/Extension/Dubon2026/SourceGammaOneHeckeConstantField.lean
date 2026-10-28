import Dubon2026.SourceGammaOneComplexFieldExtension
import Dubon2026.SourceGammaOneHeckeFieldNaturality

/-! DUB17/18 -> original all-weight arithmetic realization -> actual
Gamma1 Tate/Hecke comparison -> conorm naturality for the actual
intersection correspondence. Reuse the native coefficient map on
Gamma1 M intersect Gamma0(d*M), with the same fixed Qbar embedding.
Only the field inputs needed for extending the correspondence's places
are added; no separate Picard descent for this field is required. -/
namespace Dubon2026.SourceFunctionField.GammaOne.HeckeConstantField
noncomputable section
open CongruenceSubgroup
local notation "Qbar" => AlgebraicClosure ℚ
variable (M d : ℕ)
local notation "H" => Gamma1 M ⊓ Gamma0 (d * M)
local notation "FQ" => functionFieldOver H Qbar
local notation "FC" => functionFieldOver H ℂ

/-- The existing coefficient map on the actual Hecke intersection field. -/
def fieldMap : FQ →+* FC :=
  fieldCoefficientMap H OriginalConstantField.sigma

theorem fieldMap_constants (a : Qbar) :
    fieldMap M d (algebraMap Qbar FQ a) =
      algebraMap ℂ FC (OriginalConstantField.sigma a) :=
  fieldCoefficientMap_constants H OriginalConstantField.sigma a

theorem fieldMap_rational (x : qExpFunctionFieldC ℚ H) :
    fieldMap M d ⟨coeffEmb Qbar x.val, coeffEmb_mem_laurentBaseChange Qbar x.property⟩ =
      ⟨coeffEmb ℂ x.val, coeffEmb_mem_laurentBaseChange ℂ x.property⟩ :=
  Subtype.ext (OriginalConstantField.coeffMap_sigma_rational x.val)

theorem fieldMap_j : fieldMap M d (jCoordinateOver H Qbar) = jCoordinateOver H ℂ :=
  fieldCoefficientMap_j H OriginalConstantField.sigma

/-- The fixed original algebraic-closure scalar action. -/
abbrev complexAlgebra : Algebra Qbar ℂ := ConstantField.complexAlgebra

/-- The actual correspondence field acts by coefficient transport. -/
abbrev fieldAlgebra : Algebra FQ FC := (fieldMap M d).toAlgebra

/-- The same fixed arithmetic constants inside the complex correspondence field. -/
abbrev complexFieldAlgebra : Algebra Qbar FC :=
  ((algebraMap ℂ FC).comp OriginalConstantField.sigma.toRingHom).toAlgebra

attribute [local instance] complexAlgebra fieldAlgebra complexFieldAlgebra

theorem complexScalarTower : IsScalarTower Qbar ℂ FC :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem arithmeticFieldScalarTower : IsScalarTower Qbar FQ FC :=
  IsScalarTower.of_algebraMap_eq fun a => (fieldMap_constants M d a).symm

theorem adjoin_range_fieldMap :
    IntermediateField.adjoin ℂ (Set.range (fieldMap M d)) = ⊤ := by
  apply IntermediateField.lift_injective (functionFieldOver H ℂ)
  refine Eq.trans ?_ (IntermediateField.lift_top ℂ
    (functionFieldOver H ℂ)).symm
  apply le_antisymm (IntermediateField.lift_le _)
  change IntermediateField.adjoin ℂ
    (coeffEmb ℂ '' (qExpFunctionFieldC ℚ H : Set (LaurentSeries ℚ))) ≤ _
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨⟨coeffEmb ℂ x, coeffEmb_mem_laurentBaseChange ℂ hx⟩, ?_, rfl⟩
  exact IntermediateField.subset_adjoin ℂ _
    ⟨⟨coeffEmb Qbar x, coeffEmb_mem_laurentBaseChange Qbar hx⟩,
      fieldMap_rational M d ⟨x, hx⟩⟩


/-- Inclusion into Laurent series with their coefficientwise scalar action. -/
def laurentLinearMap (L : Type*) [Field L] [Algebra ℚ L] :
    functionFieldOver H L →ₗ[L] LaurentSeries L where
  toFun := Subtype.val
  map_add' _ _ := rfl
  map_smul' a x := by
    change algebraMap L (LaurentSeries L) a * (x : LaurentSeries L) = a • (x : LaurentSeries L)
    rw [SourceDifferential.algebraMap_laurentSeries_apply_alt,
      HahnSeries.single_zero_mul_eq_smul]

end
end Dubon2026.SourceFunctionField.GammaOne.HeckeConstantField
