import Dubon2026.SourceGammaOnePrimitiveJointTrace
import Dubon2026.SourceUnitTraceConjugation

/-! DUB-17/18 -> all-weight association -> trace specialization.
A known Hecke-word trace value is invariant under actual global conjugation:
the original determinant is cyclotomic, and original Galois operators
commute with the full Hecke image. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open SourceCurve CongruenceSubgroup SourceCuspBoundary CoefficientReduction
attribute [local instance] rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric
attribute [local instance 1100] rationalPrimeOriginalNormedField
local notation "Qbar" => AlgebraicClosure ℚ
private local instance : IsGalois ℚ Qbar := sourceRationalAlgebraicClosure_isGalois
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

/-- The actual multiplicative determinant term is invariant under conjugation. -/
theorem binaryPrimitiveJointDeterminant_conjugate (g τ : Qbar ≃ₐ[ℚ] Qbar) :
    binaryPrimitiveJointDeterminant Q p n w (τ * g * τ⁻¹) =
      binaryPrimitiveJointDeterminant Q p n w g := by
  change binaryPrimitiveJointWeightedDiamond Q p n w
      (sourceAbsoluteCyclotomicCharacter M (τ * g * τ⁻¹)) = _
  have he : sourceAbsoluteCyclotomicCharacter M (τ * g * τ⁻¹) =
      sourceAbsoluteCyclotomicCharacter M g := by
    simp [mul_comm]
  rw [he]
  rfl

/-- A trace equal to an original word stays equal to that same word under
actual Galois conjugation; neither trace centrality nor density is assumed. -/
theorem binaryPrimitiveJointTrace_conjugate_eq_word
    (Hq : sourceBinaryHeckePrime (Q * N) → Module.End (ZMod N) J)
    (hH : ∀ ell, (Hq ell).comp (binaryTateDiamondRelations Q p n w).mkQ =
      (binaryTateDiamondRelations Q p n w).mkQ.comp (binaryTatePrimeOperators Q p n w ell))
    (g τ : Qbar ≃ₐ[ℚ] Qbar) (a : FreeAlgebra ℤ S)
    (hT : binaryPrimitiveJointTrace Q p n w g =
      binaryPrimitiveJointHeckeDiamondWord Q p n w Hq a) :
    binaryPrimitiveJointTrace Q p n w (τ * g * τ⁻¹) =
      binaryPrimitiveJointHeckeDiamondWord Q p n w Hq a := by
  have hD : Commute (binaryPrimitiveJointGaloisRep Q p n w τ⁻¹)
      (binaryPrimitiveJointDeterminant Q p n w g) := by
    obtain ⟨b, hb⟩ := binaryPrimitiveJointDeterminant_mem_range Q p n w Hq g
    rw [← hb]
    exact binaryPrimitiveJointGaloisRep_word Q p n w Hq hH τ⁻¹ b
  exact sourceUnitTrace_conjugate_eq (binaryPrimitiveJointGaloisRep Q p n w)
    (binaryPrimitiveJointDeterminant Q p n w) g τ _
    (binaryPrimitiveJointDeterminant_conjugate Q p n w g τ) hD
    (binaryPrimitiveJointGaloisRep_word Q p n w Hq hH τ a) hT

end
end Dubon2026.SourceFunctionField.GammaOne
