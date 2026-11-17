import Dubon2026.SourceGammaOneGeometricHeckeFamily
import Dubon2026.SourceGammaOnePrimitiveJointCharacter

/-! DUB-17/18 -> original all-weight association -> original finite
joint arithmetic character. Proved original geometry supplies the quotient
Hecke family, and the explicit primitive boundary supplies its faithful
prime/diamond comparison. The resulting finite operator image carries
the entire original character at every requested precision. Its diamond
values are one by the original word map. Arithmetic specialization and
the characteristic-zero source endpoint remain separate obligations. -/
namespace Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
noncomputable section
open SourceCurve CongruenceSubgroup IntermediateField
open scoped ValuativeRel
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
/-- The actual geometric quotient and explicit primitive boundary together
carry the original character at every target precision, using twice the
source precision and no supplied lifting or separator hypothesis. -/
theorem exists_gammaOne_primitive_joint_original_character
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (hlarge : 3 < p)
    {E : Type} [Field E] [CharZero E] [ValuativeRel E] [CharP 𝓀[E] p]
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E) :
    Finite (binaryPrimitiveJointOperatorRing Q p d w) ∧
    ∃ Hq : sourceBinaryHeckePrime (Q * N) → Module.End (ZMod N)
        ((T →ₗ[ℤ_[p]] V) ⧸ binaryTateDiamondRelations Q p d w),
      (∀ ell, (Hq ell).comp (binaryTateDiamondRelations Q p d w).mkQ =
        (binaryTateDiamondRelations Q p d w).mkQ.comp (binaryTatePrimeOperators Q p d w ell)) ∧
      sourceOperatorRangeCharacterData (binaryPrimitiveJointHeckeDiamondWord Q p d w Hq)
        ((sourcePrimitiveH1AdicQuotientCharacter f hk τ n).comp
          (sourceGammaOneOriginalHeckeDiamondWord Q N w).toRingHom) := by
  refine ⟨binaryPrimitiveJointOperatorRing_finite Q p d w, ?_⟩
  have hs := exists_gammaOne_diamond_quotient_hecke_family Q p d w
  rcases hs with ⟨Hq, hH⟩
  exact ⟨Hq, hH, binaryPrimitiveJoint_original_character Q p n f hk hlarge τ Hq hH⟩

end
end Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
