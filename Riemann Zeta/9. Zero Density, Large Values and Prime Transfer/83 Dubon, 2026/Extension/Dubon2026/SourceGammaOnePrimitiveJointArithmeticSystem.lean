import Dubon2026.SourceGammaOneGeometricPrimitiveJointCharacter
import Dubon2026.SourceGammaOnePrimitiveJointCharacterValues
import Dubon2026.SourceGammaOnePrimitiveJointArithmeticData

/-! DUB-17/18 -> original all-weight association -> original finite arithmetic
systems. This consumer unpacks the proved original character, derives its
literal Fourier and diamond values, and combines the same joint action with
its proved arithmetic descent and actual local Frobenius witnesses. It does
not assert a rank-two or characteristic-zero Galois realization. -/
namespace Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
noncomputable section
open SourceCurve CongruenceSubgroup IntermediateField
open scoped ValuativeRel NumberField
attribute [local instance] rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric
attribute [local instance 1100] rationalPrimeOriginalNormedField
local notation "Qbar" => AlgebraicClosure ℚ
variable (Q p n : ℕ) [NeZero Q] [Fact p.Prime] {k : ℤ}
local notation "w" => Int.toNat (k - 2)
local notation "d" => 2 * n + 1
local notation "N" => p ^ (d + 1)
local notation "M" => Q * N ^ 2
local notation "Γ" => Gamma1 M
local notation "V" => sourceBinaryCoefficientRep (ZMod N) Q w
local notation "T" => TateModule p (Pic0 Qbar (functionFieldOver Γ Qbar))
private local instance : Algebra ℤ_[p] (ZMod N) := (PadicInt.toZModPow (d + 1)).toAlgebra
private local instance : Module ℤ_[p] V := Module.restrictScalars ℤ_[p] (ZMod N) V
private local instance : IsScalarTower ℤ_[p] (ZMod N) V :=
  IsScalarTower.restrictScalars ℤ_[p] (ZMod N) V
private local instance : AddCommGroup (T →ₗ[ℤ_[p]] V) := inferInstance
private local instance : Module (ZMod N) (T →ₗ[ℤ_[p]] V) := inferInstance
local notation "J" => (T →ₗ[ℤ_[p]] V) ⧸ binaryTateDiamondRelations Q p d w
local notation "R" => binaryPrimitiveJointOperatorRing Q p d w
local notation "S" => sourceBinaryHeckePrime (Q * N) ⊕ Gamma0 M
private local instance : IsGalois ℚ Qbar := sourceRationalAlgebraicClosure_isGalois

/-- The original all-weight Fourier character and one actual finite arithmetic
Galois system share the same operator ring, exact diamond values and local
Frobenius quadratic, with all geometric and inertia premises discharged. -/
theorem exists_gammaOne_primitive_joint_arithmetic_system
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (hlarge : 3 < p)
    {E : Type} [Field E] [CharZero E] [ValuativeRel E] [CharP 𝓀[E] p]
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E) :
    Finite R ∧
    ∃ Hq : sourceBinaryHeckePrime (Q * N) → Module.End (ZMod N) J,
      (∀ ell, (Hq ell).comp (binaryTateDiamondRelations Q p d w).mkQ =
        (binaryTateDiamondRelations Q p d w).mkQ.comp (binaryTatePrimeOperators Q p d w ell)) ∧
      ∃ χ : (binaryPrimitiveJointHeckeDiamondWord Q p d w Hq).range →+*
          𝒪[E] ⧸ (IsLocalRing.maximalIdeal 𝒪[E]) ^ (n + 1),
        χ.comp (binaryPrimitiveJointHeckeDiamondWord Q p d w Hq).rangeRestrict =
          (sourcePrimitiveH1AdicQuotientCharacter f hk τ n).comp
            (sourceGammaOneOriginalHeckeDiamondWord Q N w).toRingHom ∧
        (∀ g : Gamma0 M, χ ((binaryPrimitiveJointHeckeDiamondWord Q p d w Hq).rangeRestrict
          (FreeAlgebra.ι ℤ (Sum.inr g))) = 1) ∧
        (∀ ell : sourceBinaryHeckePrime (Q * N),
          χ ((binaryPrimitiveJointHeckeDiamondWord Q p d w Hq).rangeRestrict
            (FreeAlgebra.ι ℤ (Sum.inl ell))) =
            Ideal.Quotient.mk ((IsLocalRing.maximalIdeal 𝒪[E]) ^ (n + 1))
              ⟨τ (sourcePrimitiveFieldCoefficient f ell.val),
                sourcePrimitiveCoefficient_valuation_le_one f hk τ ell.val⟩) ∧
        binaryPrimitiveJointArithmeticData Q p d w Hq := by
  have hs := exists_gammaOne_primitive_joint_original_character Q p n f hk hlarge τ
  let Hq := hs.2.choose
  have hH := hs.2.choose_spec.1
  have hchar := hs.2.choose_spec.2
  let χ := hchar.choose
  have hχ := hchar.choose_spec
  have harith := binaryPrimitiveJoint_arithmetic_data Q p d w Hq hH
  refine ⟨hs.1, Hq, hH, χ, hχ, ?_, ?_, harith⟩
  · exact fun g => binaryPrimitiveJoint_character_diamond Q p n f hk τ Hq χ hχ g
  · exact fun ell => binaryPrimitiveJoint_character_hecke Q p n f hk τ Hq χ hχ ell

end
end Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
