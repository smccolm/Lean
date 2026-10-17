import Dubon2026.OriginalArithmeticClassInvariant
import Dubon2026.OriginalRelationPrimeInvariantPairing

/-! # The scalar relation pairing at an actual arithmetic stage

Construct the invariant and its prime-field readout for the same original
outside-unit class coefficient. No invariant or detection premise remains.
This is the finite scalar input to DUB-17's source class duality argument.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory IsDedekindDomain
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.module
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul

/-- Retain the original stage's rational algebra in the scalar pairing. -/
local instance relationPrimePairingRationalAlgebra {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    (F : FiniteGaloisIntermediateField ℚ Ω) : Algebra ℚ F := F.algebra'

/-- Every actual arithmetic stage has a constructed injective class
invariant and additive residue-ring pairing detecting exactly the original obstruction. -/
theorem originalUnramifiedStage_exists_prime_relation_pairing
    {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    (a : 𝓞 ℚ) (ha : a ≠ 0) (N : OriginalUnramifiedGaloisStage (Ω := Ω) a)
    (p : ℕ) [NeZero p] (B : Rep.{0} ℤ Gal(N.val/ℚ)) (hB : ∀ b : B, p • b = 0) :
    let T := originalExceptionalIntegerSupport N.val (algebraMap (𝓞 ℚ) (𝓞 N.val) a)
      (originalIntegerMap_ne_zero (L := N.val) a ha)
    let hT := originalExceptionalIntegerSupport_galoisStable N.val ℚ a ha
    let C := originalIdeleClassesModOutsideRep ℚ N.val T hT
    ∃ inv : groupCohomology C 2 →+ AddCircle (1 : ℚ), Function.Injective inv ∧
      ∃ α : (originalRelationModule B ⟶ C) →+ (groupCohomology B 1 →+ ZMod p),
        (∀ φ y, rationalCyclicInvariant p (α φ y) =
          inv ((originalRelationExtensionObstruction B C φ).hom y)) ∧
        ∀ φ y, α φ y = 0 ↔ (originalRelationExtensionObstruction B C φ).hom y = 0 := by
  exact originalRelation_exists_prime_pairing_from_invariant B _ p hB
    (originalUnramifiedStageClass_exists_injective_invariant a ha N)

/-- The same actual arithmetic invariant constructs the concrete pairing
data used by the enlarged-stage scalar separation theorem. -/
theorem originalUnramifiedStage_prime_relation_pairing_data
    {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    (a : 𝓞 ℚ) (ha : a ≠ 0) (N : OriginalUnramifiedGaloisStage (Ω := Ω) a)
    (p : ℕ) [NeZero p] (B : Rep.{0} ℤ Gal(N.val/ℚ)) (hB : ∀ b : B, p • b = 0) :
    let T := originalExceptionalIntegerSupport N.val (algebraMap (𝓞 ℚ) (𝓞 N.val) a)
      (originalIntegerMap_ne_zero (L := N.val) a ha)
    let hT := originalExceptionalIntegerSupport_galoisStable N.val ℚ a ha
    Nonempty (OriginalRelationPrimePairingData B
      (originalIdeleClassesModOutsideRep ℚ N.val T hT) p) := by
  exact originalRelationPrimePairingData_nonempty B _ p hB
    (originalUnramifiedStageClass_exists_injective_invariant a ha N)

end
end Dubon2026
