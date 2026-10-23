import Dubon2026.SourcePadicCoefficientLocalStructure
import Mathlib.NumberTheory.Padics.PadicIntegers

/-! DUB-17/18 -> residual primitive representation -> span the image
of the actual integral Tate module over the coefficient integer ring.
The original p-adic integers map into that ring because the constructed
coefficient valuation extends the original p-adic norm valuation. -/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel
variable (p : ℕ) [Fact p.Prime]

private local instance : ValuativeRel ℚ_[p] :=
  ValuativeRel.ofValuation (NormedField.valuation (K := ℚ_[p]))

theorem padicInteger_normValuation_le_one (z : ℤ_[p]) :
    ValuativeRel.valuation ℚ_[p] (z : ℚ_[p]) ≤ 1 := by
  letI : (NormedField.valuation (K := ℚ_[p])).Compatible :=
    Valuation.Compatible.ofValuation _
  have h := (ValuativeRel.isEquiv (ValuativeRel.valuation ℚ_[p])
    (NormedField.valuation (K := ℚ_[p])) (z : ℚ_[p]) 1).mpr
      (show ‖(z : ℚ_[p])‖₊ ≤ ‖(1 : ℚ_[p])‖₊ from by
        simpa only [nnnorm_one, NNReal.coe_le_one] using z.property)
  simpa only [map_one] using h

variable (E : Type) [Field E] [Algebra ℚ_[p] E] [ValuativeRel E]
variable [(ValuativeRel.valuation ℚ_[p]).HasExtension (ValuativeRel.valuation E)]

theorem padicInteger_coefficient_valuation_le_one (z : ℤ_[p]) :
    ValuativeRel.valuation E (algebraMap ℚ_[p] E (z : ℚ_[p])) ≤ 1 :=
  (Valuation.HasExtension.val_map_le_one_iff
    (ValuativeRel.valuation ℚ_[p]) (ValuativeRel.valuation E) (z : ℚ_[p])).mpr
      (padicInteger_normValuation_le_one p z)

/-- The original p-adic integer scalar inclusion into the actual coefficient integer ring. -/
def padicIntegerCoefficientMap : ℤ_[p] →+* 𝒪[E] :=
  ((algebraMap ℚ_[p] E).comp PadicInt.Coe.ringHom).codRestrict
    (ValuativeRel.valuation E).integer (padicInteger_coefficient_valuation_le_one p E)

theorem padicIntegerCoefficientMap_coe (z : ℤ_[p]) :
    (padicIntegerCoefficientMap p E z : E) = algebraMap ℚ_[p] E (z : ℚ_[p]) := rfl

/-- The coefficient integers as an algebra over the original p-adic integers. -/
@[reducible]
def padicIntegerCoefficientAlgebra : Algebra ℤ_[p] 𝒪[E] :=
  (padicIntegerCoefficientMap p E).toAlgebra

theorem padicIntegerCoefficient_scalarTower
    [Algebra ℤ_[p] E] [IsScalarTower ℤ_[p] ℚ_[p] E] :
    letI := padicIntegerCoefficientAlgebra p E
    IsScalarTower ℤ_[p] 𝒪[E] E := by
  letI := padicIntegerCoefficientAlgebra p E
  apply IsScalarTower.of_algebraMap_eq
  intro z
  exact IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] E z

end
end Dubon2026
