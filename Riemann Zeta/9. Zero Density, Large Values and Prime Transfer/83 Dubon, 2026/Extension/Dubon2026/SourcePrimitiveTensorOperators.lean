import Dubon2026.SourceIntegerCoefficientExtensionLaws
import Dubon2026.SourceOriginalHeckeCoefficientFaithfulness
import Dubon2026.SourcePrimitiveGoodProjectionHecke

/-! DUB-17/18 -> original Tate primitive component. The actual finite
good Hecke annihilator and its arithmetic projector are elements of the
literal coefficient-field tensor of the integral Hecke algebra. Their
complex evaluation recovers exactly the already constructed operators. -/
namespace Dubon2026
noncomputable section
open Matrix.SpecialLinearGroup CongruenceSubgroup Polynomial TensorProduct
open scoped MatrixGroups
variable (N : ℕ) [NeZero N]
local notation "S" => CuspForm (Subgroup.map (mapGL ℝ) (Gamma0 N)) 2
local notation "TZ" => sourceOriginalIntegralHeckeAlgebra N 2

/-- The actual positive-index Hecke operator in the original integral algebra. -/
def primitiveIntegralHeckeIndex (n : ℕ+) : TZ :=
  ⟨cuspHeckeLinear N 2 n, Algebra.subset_adjoin ⟨n, rfl⟩⟩

/-- Complex evaluation of the literal coefficient extension of the original integral algebra. -/
def primitiveCoefficientCuspEvaluation (f : PrimitiveCuspForm N 2) :
    sourcePrimitiveCoefficientField f ⊗[ℤ] TZ →+* Module.End ℂ S :=
  integerCoefficientExtension (algebraMap (sourcePrimitiveCoefficientField f) ℂ)
    (sourceOriginalIntegralHeckeAlgebra N 2).val.toRingHom

/-- The actual squared good-prime annihilator in the arithmetic Hecke algebra. -/
def primitiveGoodTensorAnnihilator (f : PrimitiveCuspForm N 2)
    (s : Finset {q : Nat.Primes // q.val.Coprime N}) : sourcePrimitiveCoefficientField f ⊗[ℤ] TZ :=
  ∑ q ∈ s, ((1 : sourcePrimitiveCoefficientField f) ⊗ₜ[ℤ]
    primitiveIntegralHeckeIndex N ⟨q.val.val, q.val.property.pos⟩ -
    sourcePrimitiveFieldCoefficient f q.val.val • 1) ^ 2

/-- The same arithmetic projector polynomial evaluated in the original tensor Hecke algebra. -/
def primitiveGoodTensorProjector (f : PrimitiveCuspForm N 2)
    (s : Finset {q : Nat.Primes // q.val.Coprime N})
    (P : Polynomial (sourcePrimitiveCoefficientField f)) : sourcePrimitiveCoefficientField f ⊗[ℤ] TZ :=
  aeval (primitiveGoodTensorAnnihilator N f s) P

theorem primitiveCoefficientCuspEvaluation_injective (f : PrimitiveCuspForm N 2) :
    Function.Injective (primitiveCoefficientCuspEvaluation N f) :=
  originalHecke_coefficient_extension_injective N (algebraMap (sourcePrimitiveCoefficientField f) ℂ)

theorem primitiveCoefficientCuspEvaluation_hecke (f : PrimitiveCuspForm N 2) (n : ℕ+) :
    primitiveCoefficientCuspEvaluation N f
      ((1 : sourcePrimitiveCoefficientField f) ⊗ₜ[ℤ] primitiveIntegralHeckeIndex N n) =
        cuspHeckeLinear N 2 n := by
  rw [primitiveCoefficientCuspEvaluation, integerCoefficientExtension_tmul, map_one, one_smul]
  rfl

theorem primitiveCoefficientCuspEvaluation_annihilator (f : PrimitiveCuspForm N 2)
    (s : Finset {q : Nat.Primes // q.val.Coprime N}) :
    primitiveCoefficientCuspEvaluation N f (primitiveGoodTensorAnnihilator N f s) =
      primitiveGoodAnnihilator N f s :=
  integerCoefficientExtension_shifted_squares (algebraMap (sourcePrimitiveCoefficientField f) ℂ)
    (sourceOriginalIntegralHeckeAlgebra N 2).val.toRingHom s
    (fun q => primitiveIntegralHeckeIndex N ⟨q.val.val, q.val.property.pos⟩)
    (fun q => sourcePrimitiveFieldCoefficient f q.val.val)

theorem primitiveCoefficientCuspEvaluation_projector (f : PrimitiveCuspForm N 2)
    (s : Finset {q : Nat.Primes // q.val.Coprime N})
    (P : Polynomial (sourcePrimitiveCoefficientField f)) :
    primitiveCoefficientCuspEvaluation N f (primitiveGoodTensorProjector N f s P) =
      primitiveGoodCoefficientProjector N f s P := by
  calc
    _ = aeval (primitiveCoefficientCuspEvaluation N f (primitiveGoodTensorAnnihilator N f s))
        (P.map (algebraMap (sourcePrimitiveCoefficientField f) ℂ)) :=
      integerCoefficientExtension_aeval (algebraMap (sourcePrimitiveCoefficientField f) ℂ)
        (sourceOriginalIntegralHeckeAlgebra N 2).val.toRingHom
        (primitiveGoodTensorAnnihilator N f s) P
    _ = _ := by rw [primitiveCoefficientCuspEvaluation_annihilator]; rfl

end
end Dubon2026
