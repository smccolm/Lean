import Dubon2026.ArithmeticRelativeStageIdeleTotalInvariant
import Dubon2026.OriginalCyclicClassH2Surjectivity
import Dubon2026.ContinuousFiniteH2CardAnnihilation

/-! # Original cyclic class invariants at a relative arithmetic stage

Apply the existing original-object argument to an actual finite extension
which is Galois over its specified base. No normality over the rationals
is required. This is the auxiliary-stage interface needed by DUB-17's
class-generator transfer, with all local maps and scalar towers retained.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance 1100] Submodule.Quotient.module
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageUpperTopology arithmeticRelativeStageUpperDiscrete arithmeticOrbitUpperGalois

private theorem finiteGaloisDegree_annihilates
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)] [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
    (n : ℕ) (hn : Module.finrank K L = n)
    (x : GaloisUnitContinuousH2 (K := K) (Ω := L)) : n • x = 0 := by
  letI : Fintype Gal(L/K) := Fintype.ofFinite _
  have hz := continuousFiniteH2_card_nsmul_eq_zero (Rep.ofAlgebraAutOnUnits K L)
    (discreteGaloisUnitAction_continuous (K := K) (Ω := L)) x
  have he : Fintype.card Gal(L/K) = n :=
    Nat.card_eq_fintype_card.symm.trans ((IsGalois.card_aut_eq_finrank K L).trans hn)
  exact he ▸ hz

variable (a : 𝓞 ℚ)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  (H : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ H]
  (hFH : F ≤ H)
  [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    IsGalois F H]

/-- The actual odd-primary cyclic-stage idele-class H2 admits an invariant whose composite with the literal full-idele class map is the proved original-prime total. -/
theorem rationalArithmeticRelativeStage_exists_class_invariant
    (q r : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hcyclic : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsCyclic Gal(H/F))
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ (r + 1)) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    ∃ invC : groupCohomology (originalIdeleClassRep F H) 2 →+ AddCircle (1 : ℚ),
      ∀ x : rationalArithmeticRelativeStageIdeleH2 a F H hFH,
        invC ((groupCohomology.functor ℤ Gal(H/F) 2).map (originalFullClassRepHom F H) x) =
          rationalArithmeticRelativeStageIdeleTotalInvariant a F H hFH x := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := hGal
  letI : IsCyclic Gal(H/F) := hcyclic
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits F H) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits F H) := ⟨rfl⟩
  let total : groupCohomology (originalFullIdeleRep F H) 2 →ₗ[ℤ] AddCircle (1 : ℚ) := {
    toFun := rationalArithmeticRelativeStageIdeleTotalInvariant a F H hFH
    map_add' := map_add (rationalArithmeticRelativeStageIdeleTotalInvariant a F H hFH)
    map_smul' := fun n x => by
      simpa only [← Int.cast_smul_eq_zsmul ℤ n x, Int.cast_id] using
        map_zsmul (rationalArithmeticRelativeStageIdeleTotalInvariant a F H hFH) n x }
  let principal := ((groupCohomology.functor ℤ Gal(H/F) 2).map (originalFullPrincipalRepHom F H)).hom
  have hkill : principal.range ≤ total.ker := by
    rintro x ⟨y, rfl⟩
    change total (principal y) = 0
    induction y using groupCohomology.H2_induction_on with
    | h c =>
      let z : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F H) :=
        ⟨c, continuous_of_discreteTopology⟩
      have hz := finiteGaloisDegree_annihilates F H (q ^ (r + 1)) hdegree (Submodule.Quotient.mk z)
      exact rationalArithmeticRelativeStageIdeleTotalInvariant_principal a F H hFH q r hq hq2 hqa z hz
  let lift := principal.range.liftQ total hkill
  let e := originalCyclicClassH2QuotientEquiv F H
  refine ⟨(lift.comp e.symm.toLinearMap).toAddMonoidHom, ?_⟩
  intro x
  change lift (e.symm ((groupCohomology.functor ℤ Gal(H/F) 2).map (originalFullClassRepHom F H) x)) = total x
  have hm : lift (e.symm (e (Submodule.Quotient.mk x))) = total x := by
    rw [e.symm_apply_apply]
    rfl
  exact (congrArg (fun c => lift (e.symm c)) (originalCyclicClassH2QuotientEquiv_mk F H x)).symm.trans hm

end
end Dubon2026
