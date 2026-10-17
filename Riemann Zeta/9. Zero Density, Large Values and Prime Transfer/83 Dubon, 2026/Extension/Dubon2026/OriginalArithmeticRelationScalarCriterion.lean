import Dubon2026.OriginalArithmeticConstructedRelationExtension
import Dubon2026.OriginalArithmeticRelationPrimePairing

/-! # The exact scalar relation criterion at a constructed arithmetic stage

The actual class invariant and scalar readout are constructed on the same
enlarged stage as the original extension criterion. The scalar functional
vanishes precisely for relations extending through the original free cover.
This applies to every relation at that stage, including all canonical
transports from the original stage, and supplies DUB-17's finite separation
input. Continuous and source-local cup-pairing comparisons remain separate.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory IsDedekindDomain
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.module
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul

/-- Keep the actual stage's displayed rational algebra. -/
local instance scalarCriterionRationalAlgebra {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    (F : FiniteGaloisIntermediateField ℚ Ω) : Algebra ℚ F := F.algebra'

private theorem scalar_criterion_of_pairing {G : Type} [Group G]
    (B C : Rep ℤ G) (p : ℕ) [NeZero p]
    (hd : Nonempty (OriginalRelationPrimePairingData B C p))
    (hc : ∀ ψ : originalRelationModule B ⟶ C,
      originalRelationExtensionObstruction B C ψ = 0 ↔
        ∃ f : Rep.free ℤ G B ⟶ C, originalRelationInclusion B ≫ f = ψ) :
    ∃ d : OriginalRelationPrimePairingData B C p,
      ∀ ψ : originalRelationModule B ⟶ C,
        (∀ y, d.readout ψ y = 0) ↔
          ∃ f : Rep.free ℤ G B ⟶ C, originalRelationInclusion B ≫ f = ψ := by
  obtain ⟨d⟩ := hd
  refine ⟨d, fun ψ => ?_⟩
  constructor
  · intro h
    apply (hc ψ).mp
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    exact (d.zero_iff ψ y).mp (h y)
  · intro h y
    apply (d.zero_iff ψ y).mpr
    exact congrArg (fun f : groupCohomology B 1 ⟶ groupCohomology C 2 => f.hom y)
      ((hc ψ).mpr h)

/-- At a constructed stage above the original coefficient stage, the
constructed scalar pairing has exactly the original extension kernel. -/
theorem originalUnramifiedStage_exists_scalar_relation_criterion
    (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (a : 𝓞 ℚ) (ha : a ≠ 0)
    (P : OriginalUnramifiedGaloisStage (Ω := Ω) a)
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpa : (p : 𝓞 ℚ) ∣ a)
    (B : Rep.{0} ℤ Gal(P.val/ℚ)) [Finite B] (hB : ∀ b : B, p • b = 0) :
    ∃ N : OriginalUnramifiedGaloisStage (Ω := Ω) a,
      ∃ hPN : P.val.toIntermediateField ≤ N.val.toIntermediateField,
        letI : Algebra P.val N.val := (IntermediateField.inclusion hPN).toRingHom.toAlgebra
        letI : IsScalarTower ℚ P.val N.val := IsScalarTower.of_algHom (IntermediateField.inclusion hPN)
        let T := originalExceptionalIntegerSupport N.val (algebraMap (𝓞 ℚ) (𝓞 N.val) a)
          (originalIntegerMap_ne_zero (L := N.val) a ha)
        let hT := originalExceptionalIntegerSupport_galoisStable N.val ℚ a ha
        let C := originalIdeleClassesModOutsideRep ℚ N.val T hT
        let BN := Rep.res (AlgEquiv.restrictNormalHom P.val : Gal(N.val/ℚ) →* Gal(P.val/ℚ)) B
        ∃ d : OriginalRelationPrimePairingData BN C p,
          ∀ ψ : originalRelationModule BN ⟶ C,
            (∀ y, d.readout ψ y = 0) ↔
              ∃ f : Rep.free ℤ Gal(N.val/ℚ) BN ⟶ C, originalRelationInclusion BN ≫ f = ψ := by
  obtain ⟨N, hPN, hcriterion⟩ :=
    originalUnramifiedStage_exists_constructed_relation_criterion Ω a ha P p hp2 hpa B hB
  letI : Algebra P.val N.val := (IntermediateField.inclusion hPN).toRingHom.toAlgebra
  letI : IsScalarTower ℚ P.val N.val := IsScalarTower.of_algHom (IntermediateField.inclusion hPN)
  let T := originalExceptionalIntegerSupport N.val (algebraMap (𝓞 ℚ) (𝓞 N.val) a)
    (originalIntegerMap_ne_zero (L := N.val) a ha)
  let hT := originalExceptionalIntegerSupport_galoisStable N.val ℚ a ha
  let C := originalIdeleClassesModOutsideRep ℚ N.val T hT
  let BN := Rep.res (AlgEquiv.restrictNormalHom P.val : Gal(N.val/ℚ) →* Gal(P.val/ℚ)) B
  exact ⟨N, hPN, scalar_criterion_of_pairing BN C p
    (originalUnramifiedStage_prime_relation_pairing_data a ha N p BN hB) hcriterion⟩

end
end Dubon2026
