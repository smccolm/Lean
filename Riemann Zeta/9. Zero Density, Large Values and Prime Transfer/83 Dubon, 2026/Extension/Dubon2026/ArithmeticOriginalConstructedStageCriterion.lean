import Dubon2026.ArithmeticOriginalRelationStagePlacement
import Dubon2026.OriginalArithmeticConstructedRelationExtension

/-! Choose the actual original extension-criterion field before assembling
the local Cartier family. The initial finite coefficient in the arithmetic
union is restricted directly along its retained ambient embedding. This
is DUB-17's shorter zero-obstruction route, without scalar-readout data. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] relationPlacementUnionAlgebra relationPlacementStageAlgebra

/-- The initial actual finite coefficient reaches a constructed original
field where zero relation obstruction is equivalent to extension. Its
embedding retains every ambient value, and no scalar readout is supplied. -/
theorem arithmeticClassStage_exists_original_constructed_relation_criterion
    (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (a : 𝓞 ℚ) (ha : a ≠ 0)
    (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpa : (p : 𝓞 ℚ) ∣ a)
    (B : Rep.{0} ℤ Gal(P/ℚ)) [Finite B] (hB : ∀ b : B, p • b = 0) :
    ∃ N : OriginalUnramifiedGaloisStage (Ω := Ω) a, ∃ i : P →ₐ[ℚ] N.val,
      (∀ x : P, (i x : Ω) = (x.val : Ω)) ∧
      let BN := arithmeticOriginalStageRestrictedCoefficient Ω a P N i B
      let T := originalExceptionalIntegerSupport N.val (algebraMap (𝓞 ℚ) (𝓞 N.val) a)
        (originalIntegerMap_ne_zero (L := N.val) a ha)
      let hT := originalExceptionalIntegerSupport_galoisStable N.val ℚ a ha
      let C := originalIdeleClassesModOutsideRep ℚ N.val T hT
      ∀ χ : originalRelationModule BN ⟶ C,
        originalRelationExtensionObstruction BN C χ = 0 ↔
          ∃ f : Rep.free ℤ Gal(N.val/ℚ) BN ⟶ C, originalRelationInclusion BN ≫ f = χ := by
  obtain ⟨F, i₀, hi₀⟩ :=
    originalUnramifiedUnion_finite_subextension_embeds_stage a ha P.toIntermediateField
  let BF := arithmeticOriginalStageRestrictedCoefficient Ω a P F i₀ B
  obtain ⟨N, hFN, hcriterion⟩ :=
    originalUnramifiedStage_exists_constructed_relation_criterion Ω a ha F p hp2 hpa BF hB
  letI : Algebra P F.val := i₀.toAlgebra
  letI : Module P F.val := i₀.toAlgebra.toModule
  letI : SMul P F.val := i₀.toAlgebra.toSMul
  letI : IsScalarTower ℚ P F.val := IsScalarTower.of_algHom i₀
  letI : Algebra F.val N.val := (IntermediateField.inclusion hFN).toRingHom.toAlgebra
  letI : Module F.val N.val := Algebra.toModule
  letI : SMul F.val N.val := Algebra.toSMul
  letI : IsScalarTower ℚ F.val N.val := IsScalarTower.of_algHom (IntermediateField.inclusion hFN)
  let i : P →ₐ[ℚ] N.val := (IntermediateField.inclusion hFN).comp i₀
  letI : Algebra P N.val := i.toAlgebra
  letI : Module P N.val := i.toAlgebra.toModule
  letI : SMul P N.val := i.toAlgebra.toSMul
  letI : IsScalarTower ℚ P N.val := IsScalarTower.of_algHom i
  letI : IsScalarTower P F.val N.val := IsScalarTower.of_algebraMap_eq' rfl
  have hBN : Rep.res (AlgEquiv.restrictNormalHom F.val : Gal(N.val/ℚ) →* Gal(F.val/ℚ)) BF =
      arithmeticOriginalStageRestrictedCoefficient Ω a P N i B := by
    apply congrArg (fun ρ : Representation ℤ Gal(N.val/ℚ) B => Rep.of ρ)
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro x
    exact congrArg (fun u => B.ρ u x)
      (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply P F.val g).symm
  refine ⟨N, i, fun x => hi₀ x, ?_⟩
  let criterion (V : Rep.{0} ℤ Gal(N.val/ℚ)) :=
    let T := originalExceptionalIntegerSupport N.val (algebraMap (𝓞 ℚ) (𝓞 N.val) a)
      (originalIntegerMap_ne_zero (L := N.val) a ha)
    let hT := originalExceptionalIntegerSupport_galoisStable N.val ℚ a ha
    let C := originalIdeleClassesModOutsideRep ℚ N.val T hT
    ∀ χ : originalRelationModule V ⟶ C,
      originalRelationExtensionObstruction V C χ = 0 ↔
        ∃ f : Rep.free ℤ Gal(N.val/ℚ) V ⟶ C, originalRelationInclusion V ≫ f = χ
  exact (congrArg criterion hBN).mp hcriterion

end
end Dubon2026
