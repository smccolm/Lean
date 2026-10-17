import Dubon2026.ArithmeticOriginalRelationClassTransport

/-! # The constructed scalar criterion consumes the descended relation

The actual field embedding, canonical relation restriction and original
full-class transition carry the given relation morphism to the very stage
where scalar vanishing is equivalent to extension. This is the required
finite-stage connection for DUB-17; continuous/local pairing is separate.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
  (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Keep the original arithmetic union's rational inclusion. -/
local instance relationScalarPlacementUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

/-- Keep every original finite stage's displayed rational algebra. -/
local instance relationScalarPlacementStageAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

/-- The actual finite class relation is carried through the constructed
original field embedding to the scalar vanishing/extension equivalence. -/
theorem arithmeticClassRelation_exists_original_scalar_criterion
    (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpa : (p : 𝓞 ℚ) ∣ a)
    (B : Rep.{0} ℤ Gal(P/ℚ)) [Finite B] (hB : ∀ b : B, p • b = 0) :
    ∃ F : OriginalUnramifiedGaloisStage (Ω := Ω) a, ∃ i : P →ₐ[ℚ] F.val,
      (∀ x : P, (i x : Ω) = (x.val : Ω)) ∧
      let BF := arithmeticOriginalStageRestrictedCoefficient Ω a P F i B
      ∃ N : OriginalUnramifiedGaloisStage (Ω := Ω) a,
        ∃ hFN : F.val.toIntermediateField ≤ N.val.toIntermediateField,
          letI : Algebra F.val N.val := (IntermediateField.inclusion hFN).toRingHom.toAlgebra
          letI : IsScalarTower ℚ F.val N.val := IsScalarTower.of_algHom (IntermediateField.inclusion hFN)
          let T := originalExceptionalIntegerSupport N.val (algebraMap (𝓞 ℚ) (𝓞 N.val) a)
            (originalIntegerMap_ne_zero (L := N.val) a ha)
          let hT := originalExceptionalIntegerSupport_galoisStable N.val ℚ a ha
          let C := originalIdeleClassesModOutsideRep ℚ N.val T hT
          let BN := Rep.res (AlgEquiv.restrictNormalHom F.val : Gal(N.val/ℚ) →* Gal(F.val/ℚ)) BF
          ∃ d : OriginalRelationPrimePairingData BN C p,
            ∀ φ : originalRelationModule B ⟶ arithmeticClassesModOutsideStageRep ℚ Ω a ha P,
              let ψ := arithmeticOriginalEnlargedRelationClassTransport Ω a ha P F i B N hFN φ
              (∀ y, d.readout ψ y = 0) ↔
                ∃ f : Rep.free ℤ Gal(N.val/ℚ) BN ⟶ C, originalRelationInclusion BN ≫ f = ψ := by
  obtain ⟨F, i, hi, N, hFN, hN⟩ :=
    arithmeticClassStage_exists_original_scalar_relation_criterion Ω a ha P p hp2 hpa B hB
  letI : Algebra F.val N.val := (IntermediateField.inclusion hFN).toRingHom.toAlgebra
  letI : IsScalarTower ℚ F.val N.val := IsScalarTower.of_algHom (IntermediateField.inclusion hFN)
  obtain ⟨d, hd⟩ := hN
  refine ⟨F, i, hi, N, hFN, d, ?_⟩
  intro φ
  exact hd _

end
end Dubon2026
