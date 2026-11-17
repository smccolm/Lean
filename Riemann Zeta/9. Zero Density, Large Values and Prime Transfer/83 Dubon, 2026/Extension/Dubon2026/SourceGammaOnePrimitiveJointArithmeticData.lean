import Dubon2026.SourceGammaOnePrimitiveJointDescent
import Dubon2026.SourceGammaOnePrimitiveJointFrobeniusWitness

/-! DUB-17/18 -> original all-weight association -> one actual finite
arithmetic system. This explicit proposition records the original action's
arithmetic descent, whole-word commutation and actual local Frobenius
witnesses. The following theorem derives every field from native proofs. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open SourceCurve CongruenceSubgroup SourceCuspBoundary CoefficientReduction
open scoped NumberField
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

local notation "R" => binaryPrimitiveJointOperatorRing Q p n w

/-- The literal arithmetic properties required of the already fixed joint
operator action. This is a specification, proved by the consumer below. -/
def binaryPrimitiveJointArithmeticData
    (Hq : sourceBinaryHeckePrime (Q * N) → Module.End (ZMod N) J) : Prop :=
  letI : TopologicalSpace R := ⊥
  ∃ η : rationalArithmeticGaloisGroup ((Q * p : ℕ) : 𝓞 ℚ) →ₜ* Rˣ,
    (∀ σ, (η (sourceAbsoluteArithmeticRestriction ((Q * p : ℕ) : 𝓞 ℚ) σ)).val =
      binaryPrimitiveJointGaloisRep Q p n w σ) ∧
    (∀ σ a, Commute
      (η (sourceAbsoluteArithmeticRestriction ((Q * p : ℕ) : 𝓞 ℚ) σ)).val
      (binaryPrimitiveJointHeckeDiamondWord Q p n w Hq a)) ∧
    (∀ (ell : sourceBinaryHeckePrime (Q * N))
        (e : Qbar →ₐ[ℚ] rationalPrimeLocalClosure ell.val ell.property.1),
      let A := sourceRationalLocalValuation ell.val ell.property.1 e
      ∃ g : Gamma0 M, (g.val 1 1 : ZMod M) = ell.val ∧
        ∃ σ : A.decompositionSubgroup ℚ,
          (∀ a : IsLocalRing.ResidueField A, σ • a = a ^ ell.val) ∧
          let F := (η (sourceAbsoluteArithmeticRestriction ((Q * p : ℕ) : 𝓞 ℚ) σ.val)).val
          F * binaryPrimitiveJointHeckeDiamondWord Q p n w Hq (FreeAlgebra.ι ℤ (Sum.inl ell)) =
            F * F + (ell.val ^ (w + 1)) •
              binaryPrimitiveJointHeckeDiamondWord Q p n w Hq (FreeAlgebra.ι ℤ (Sum.inr g)))

/-- The proved original geometry and norm-inertia identities supply the
specified arithmetic action, its commutation and its local Frobenius data. -/
theorem binaryPrimitiveJoint_arithmetic_data
    (Hq : sourceBinaryHeckePrime (Q * N) → Module.End (ZMod N) J)
    (hH : ∀ ell, (Hq ell).comp (binaryTateDiamondRelations Q p n w).mkQ =
      (binaryTateDiamondRelations Q p n w).mkQ.comp (binaryTatePrimeOperators Q p n w ell)) :
    binaryPrimitiveJointArithmeticData Q p n w Hq := by
  letI : TopologicalSpace R := ⊥
  obtain ⟨η, hη⟩ := binaryPrimitiveJointGaloisRep_arithmetic_descent Q p n w
  refine ⟨η, hη, ?_, ?_⟩
  · intro σ a
    rw [hη]
    exact binaryPrimitiveJointGaloisRep_word Q p n w Hq hH σ a
  · intro ell e
    obtain ⟨g, hg, σ, hσ, hpoly⟩ :=
      binaryPrimitiveJointGaloisRep_exists_local_frobenius Q p n w Hq hH ell e
    refine ⟨g, hg, σ, hσ, ?_⟩
    dsimp only
    rw [hη]
    exact hpoly

end
end Dubon2026.SourceFunctionField.GammaOne
