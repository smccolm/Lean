import Dubon2026.SourceGammaOnePrimitiveJointHeckeTrace
import Dubon2026.SourceGammaOnePrimitiveJointTraceFrobenius

/-! DUB-17/18 -> original all-weight association -> original adic traces.
A character of the proved original joint Hecke image specializes the actual
trace and determinant without assuming a rank-two eigenspace. The next
original-object consumer supplies that character from the modular form. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open SourceCurve CongruenceSubgroup SourceCuspBoundary CoefficientReduction
attribute [local instance] rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric algebraicLocalIntegerAction
attribute [local instance 1100] rationalPrimeOriginalNormedField
local notation "Qbar" => AlgebraicClosure ℚ
private local instance : IsGalois ℚ Qbar := sourceRationalAlgebraicClosure_isGalois
private theorem map_product_identity {A B : Type} [Ring A] [Ring B]
    (χ : A →+* B) (a b c d e : A) (h : a * b = c + d * e) :
    χ a * χ b = χ c + χ d * χ e := by
  simpa only [map_mul, map_add] using congrArg χ h

variable (Q p n w : ℕ) [NeZero Q] [Fact p.Prime]
local notation "N" => p ^ (n + 1)
local notation "M" => Q * N ^ 2
local notation "V" => sourceBinaryCoefficientRep (ZMod N) Q w
local notation "T" => TateModule p (Pic0 Qbar (functionFieldOver (Gamma1 M) Qbar))
private local instance : Algebra ℤ_[p] (ZMod N) := (PadicInt.toZModPow (n + 1)).toAlgebra
private local instance : Module ℤ_[p] V := Module.restrictScalars ℤ_[p] (ZMod N) V
private local instance : IsScalarTower ℤ_[p] (ZMod N) V :=
  IsScalarTower.restrictScalars ℤ_[p] (ZMod N) V
private local instance : AddCommGroup (T →ₗ[ℤ_[p]] V) := inferInstance
private local instance : Module (ZMod N) (T →ₗ[ℤ_[p]] V) := inferInstance
local notation "J" => (T →ₗ[ℤ_[p]] V) ⧸ binaryTateDiamondRelations Q p n w
local notation "S" => sourceBinaryHeckePrime (Q * N) ⊕ Gamma0 M

/-- Specialize the actual Hecke-valued trace by a character of its exact image. -/
def binaryPrimitiveJointSpecializedTrace
    (Hq : sourceBinaryHeckePrime (Q * N) → Module.End (ZMod N) J)
    (hH : ∀ ell, (Hq ell).comp (binaryTateDiamondRelations Q p n w).mkQ =
      (binaryTateDiamondRelations Q p n w).mkQ.comp (binaryTatePrimeOperators Q p n w ell))
    {C : Type} [Ring C] (χ : (binaryPrimitiveJointHeckeDiamondWord Q p n w Hq).range →+* C) :
    (Qbar ≃ₐ[ℚ] Qbar) → C := χ ∘ binaryPrimitiveJointHeckeTrace Q p n w Hq hH

/-- The same character specializes the actual multiplicative determinant. -/
def binaryPrimitiveJointSpecializedDeterminant
    (Hq : sourceBinaryHeckePrime (Q * N) → Module.End (ZMod N) J)
    {C : Type} [Ring C] (χ : (binaryPrimitiveJointHeckeDiamondWord Q p n w Hq).range →+* C) :
    (Qbar ≃ₐ[ℚ] Qbar) →* C :=
  χ.toMonoidHom.comp (binaryPrimitiveJointHeckeDeterminant Q p n w Hq)

/-- Specializing the original finite trace preserves discrete continuity. -/
theorem binaryPrimitiveJointSpecializedTrace_continuous
    (Hq : sourceBinaryHeckePrime (Q * N) → Module.End (ZMod N) J)
    (hH : ∀ ell, (Hq ell).comp (binaryTateDiamondRelations Q p n w).mkQ =
      (binaryTateDiamondRelations Q p n w).mkQ.comp (binaryTatePrimeOperators Q p n w ell))
    {C : Type} [Ring C] (χ : (binaryPrimitiveJointHeckeDiamondWord Q p n w Hq).range →+* C) :
    @Continuous _ _ _ ⊥ (binaryPrimitiveJointSpecializedTrace Q p n w Hq hH χ) := by
  letI : TopologicalSpace (binaryPrimitiveJointHeckeDiamondWord Q p n w Hq).range := ⊥
  letI : DiscreteTopology (binaryPrimitiveJointHeckeDiamondWord Q p n w Hq).range := ⟨rfl⟩
  letI : TopologicalSpace C := ⊥
  exact (continuous_of_discreteTopology (f := χ)).comp
    (binaryPrimitiveJointHeckeTrace_continuous Q p n w Hq hH)

/-- The specialized determinant remains continuous. -/
theorem binaryPrimitiveJointSpecializedDeterminant_continuous
    (Hq : sourceBinaryHeckePrime (Q * N) → Module.End (ZMod N) J)
    {C : Type} [Ring C] (χ : (binaryPrimitiveJointHeckeDiamondWord Q p n w Hq).range →+* C) :
    @Continuous _ _ _ ⊥ (binaryPrimitiveJointSpecializedDeterminant Q p n w Hq χ) := by
  letI : TopologicalSpace (binaryPrimitiveJointHeckeDiamondWord Q p n w Hq).range := ⊥
  letI : DiscreteTopology (binaryPrimitiveJointHeckeDiamondWord Q p n w Hq).range := ⟨rfl⟩
  letI : TopologicalSpace C := ⊥
  exact (continuous_of_discreteTopology (f := χ)).comp
    (binaryPrimitiveJointHeckeDeterminant_continuous Q p n w Hq)

/-- The character preserves the dimension-two trace identity at one. -/
theorem binaryPrimitiveJointSpecializedTrace_one
    (Hq : sourceBinaryHeckePrime (Q * N) → Module.End (ZMod N) J)
    (hH : ∀ ell, (Hq ell).comp (binaryTateDiamondRelations Q p n w).mkQ =
      (binaryTateDiamondRelations Q p n w).mkQ.comp (binaryTatePrimeOperators Q p n w ell))
    {C : Type} [Ring C] (χ : (binaryPrimitiveJointHeckeDiamondWord Q p n w Hq).range →+* C) :
    binaryPrimitiveJointSpecializedTrace Q p n w Hq hH χ 1 = 2 := by
  have he : binaryPrimitiveJointHeckeTrace Q p n w Hq hH 1 = 2 :=
    Subtype.ext (binaryPrimitiveJointTrace_one Q p n w)
  change χ (binaryPrimitiveJointHeckeTrace Q p n w Hq hH 1) = _
  rw [he, map_ofNat]

/-- The exact dimension-two product identity survives specialization. -/
theorem binaryPrimitiveJointSpecializedTrace_product
    (Hq : sourceBinaryHeckePrime (Q * N) → Module.End (ZMod N) J)
    (hH : ∀ ell, (Hq ell).comp (binaryTateDiamondRelations Q p n w).mkQ =
      (binaryTateDiamondRelations Q p n w).mkQ.comp (binaryTatePrimeOperators Q p n w ell))
    {C : Type} [Ring C] (χ : (binaryPrimitiveJointHeckeDiamondWord Q p n w Hq).range →+* C)
    (g h : Qbar ≃ₐ[ℚ] Qbar) :
    binaryPrimitiveJointSpecializedTrace Q p n w Hq hH χ g *
        binaryPrimitiveJointSpecializedTrace Q p n w Hq hH χ h =
      binaryPrimitiveJointSpecializedTrace Q p n w Hq hH χ (g * h) +
        binaryPrimitiveJointSpecializedTrace Q p n w Hq hH χ (g * h⁻¹) *
          binaryPrimitiveJointSpecializedDeterminant Q p n w Hq χ h := by
  exact map_product_identity χ _ _ _ _ _
    (binaryPrimitiveJointHeckeTrace_product Q p n w Hq hH g h)

/-- The specialized trace retains cyclicity. -/
theorem binaryPrimitiveJointSpecializedTrace_mul_comm
    (Hq : sourceBinaryHeckePrime (Q * N) → Module.End (ZMod N) J)
    (hH : ∀ ell, (Hq ell).comp (binaryTateDiamondRelations Q p n w).mkQ =
      (binaryTateDiamondRelations Q p n w).mkQ.comp (binaryTatePrimeOperators Q p n w ell))
    {C : Type} [Ring C] (χ : (binaryPrimitiveJointHeckeDiamondWord Q p n w Hq).range →+* C)
    (g h : Qbar ≃ₐ[ℚ] Qbar) :
    binaryPrimitiveJointSpecializedTrace Q p n w Hq hH χ (g * h) =
      binaryPrimitiveJointSpecializedTrace Q p n w Hq hH χ (h * g) :=
  congrArg χ (Subtype.ext (binaryPrimitiveJointTrace_mul_comm Q p n w Hq hH g h))

end
end Dubon2026.SourceFunctionField.GammaOne
