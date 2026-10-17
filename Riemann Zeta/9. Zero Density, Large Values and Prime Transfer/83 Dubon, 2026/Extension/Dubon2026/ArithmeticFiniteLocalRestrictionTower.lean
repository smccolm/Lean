import Dubon2026.ArithmeticFiniteLocalStageMonotone
import Dubon2026.ArithmeticFiniteLocalRestrictionSquare

/-! # Restriction along the original arithmetic local tower

Both local stages use the same original arithmetic embedding. Restricting
an actual local automorphism and then returning to the global subfield is
therefore identical to the reverse route. DUB-17 uses this square to carry
the proved away-prime reciprocity factors to the original cyclic subfield.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField

attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois arithmeticFiniteLocalStageRationalAlgebra

variable (a : 𝓞 ℚ)
    (E F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    (hEF : E.toIntermediateField ≤ F.toIntermediateField) (p : ℕ) (hp : p.Prime)

/-- The original finite local restriction commutes in the ambient closure. -/
theorem rationalArithmeticFiniteLocalRestriction_commutes_coe
    (σ : Gal(rationalArithmeticFiniteLocalStage a F p hp / rationalPrimeLocalField p hp))
    (x : F) :
    rationalArithmeticFiniteLocalEmbedding a F p hp
      (rationalArithmeticFiniteLocalRestriction a F p hp σ x) =
      (σ (rationalArithmeticFiniteLocalStageInclusion a F p hp x) :
        rationalPrimeLocalClosure p hp) := by
  exact congrArg (fun z : rationalArithmeticFiniteLocalStage a F p hp =>
    (z : rationalPrimeLocalClosure p hp))
    (embeddedNormalGaloisRestriction_commutes
      (rationalArithmeticFiniteLocalStageInclusion a F p hp) σ x)

attribute [-instance] UniformSpace.Completion.instSMul
  AlgebraicClosure.instSMulOfIsScalarTower

/-- Use the original rational module when elaborating the explicit local tower. -/
local instance arithmeticLocalRestrictionPrimeModule :
    Module ℚ (rationalPrimeLocalField p hp) := Algebra.toModule

/-- The original global and local subfield restrictions commute on the
actual field automorphisms, with the local containment derived. -/
theorem rationalArithmeticFiniteLocalRestriction_tower
    (σ : Gal(rationalArithmeticFiniteLocalStage a F p hp / rationalPrimeLocalField p hp)) :
    let K := rationalPrimeLocalField p hp
    let M := rationalArithmeticFiniteLocalStage a E p hp
    let N := rationalArithmeticFiniteLocalStage a F p hp
    let hMN := rationalArithmeticFiniteLocalStage_mono a E F hEF p hp
    letI : Algebra M N := (IntermediateField.inclusion hMN).toAlgebra
    letI : Module M N := Algebra.toModule
    letI : SMul M N := (IntermediateField.inclusion hMN).toAlgebra.toSMul
    letI : IsScalarTower K M N := IsScalarTower.of_algHom (IntermediateField.inclusion hMN)
    embeddedNormalGaloisRestriction (F := ℚ) (IntermediateField.inclusion hEF)
      (rationalArithmeticFiniteLocalRestriction a F p hp σ) =
      rationalArithmeticFiniteLocalRestriction a E p hp
        ((AlgEquiv.restrictNormalHom M : Gal(N/K) →* Gal(M/K)) σ) := by
  let K := rationalPrimeLocalField p hp
  let Ω := rationalPrimeLocalClosure p hp
  let M := rationalArithmeticFiniteLocalStage a E p hp
  let N := rationalArithmeticFiniteLocalStage a F p hp
  let hMN := rationalArithmeticFiniteLocalStage_mono a E F hEF p hp
  letI : Algebra M N := (IntermediateField.inclusion hMN).toAlgebra
  letI : Module M N := Algebra.toModule
  letI : SMul M N := (IntermediateField.inclusion hMN).toAlgebra.toSMul
  haveI : IsScalarTower K M N := IsScalarTower.of_algHom (IntermediateField.inclusion hMN)
  let i : E →ₐ[ℚ] F := IntermediateField.inclusion hEF
  apply AlgEquiv.ext
  intro x
  apply (rationalArithmeticFiniteLocalEmbedding a E p hp).injective
  have hleft := congrArg (rationalArithmeticFiniteLocalEmbedding a F p hp)
    (embeddedNormalGaloisRestriction_commutes i
      (rationalArithmeticFiniteLocalRestriction a F p hp σ) x)
  have houter := rationalArithmeticFiniteLocalRestriction_commutes_coe a F p hp σ (i x)
  have hright := rationalArithmeticFiniteLocalRestriction_commutes_coe a E p hp
    ((AlgEquiv.restrictNormalHom M : Gal(N/K) →* Gal(M/K)) σ) x
  have hlocal := congrArg (fun z : N => (z : Ω))
    (σ.restrictNormal_commutes M (rationalArithmeticFiniteLocalStageInclusion a E p hp x))
  exact (hleft.trans houter).trans (hright.trans hlocal).symm

end
end Dubon2026
