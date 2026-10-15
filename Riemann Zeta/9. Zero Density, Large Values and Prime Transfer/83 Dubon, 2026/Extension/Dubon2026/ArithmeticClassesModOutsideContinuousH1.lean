import Dubon2026.ArithmeticClassOneCocycleFiniteDescent
import Dubon2026.ArithmeticClassesModOutsideH1

/-! # Original arithmetic class-quotient continuous H1 vanishes

Literal finite-stage descent and the proved finite class H1 theorem
construct an original continuous coboundary for every class cocycle.
This supplies the degree-one vanishing input at the rational arithmetic
group for DUB-17 class formation. Global invariant/Ext duality and the
original localization comparison remain separate obligations.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- The original field inclusion supplies the rational algebra structure used in this comparison. -/
local instance classContinuousH1UnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]

/-- The original coefficient structure used in this comparison. -/
local instance classContinuousH1SMul : @ContinuousSMul ℤ (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)
    (arithmeticClassesModOutsideColimitRep ℚ Ω a ha).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩

/-- Every original continuous arithmetic class cocycle has an actual class-coefficient coboundary witness. -/
theorem rationalArithmeticClassOneCocycle_exists_coboundary
    (c : continuousRepresentationCocyclesOne (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)) :
    ∃ v : arithmeticClassesModOutsideColimitRep ℚ Ω a ha,
      ∀ g : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ),
        (arithmeticClassesModOutsideColimitRep ℚ Ω a ha).ρ g v - v = c.val g := by
  obtain ⟨F, d, hd⟩ := arithmeticClassOneCocycle_exists_finite_descent ℚ Ω a ha c
  letI : Algebra ℚ F := F.algebra'
  letI : NumberField F := NumberField.of_module_finite ℚ F
  haveI := ModuleCat.isZero_iff_subsingleton.mp
    (rationalArithmeticClassesModOutsideStage_first_zero Ω a ha F)
  have hz : groupCohomology.H1π (arithmeticClassesModOutsideStageRep ℚ Ω a ha F) d = 0 :=
    Subsingleton.elim _ _
  obtain ⟨v, hv⟩ := (groupCohomology.H1π_eq_zero_iff d).mp hz
  let i := coefficientRepresentationColimitOf
    (arithmeticGlobalClassesModOutsideStageRep ℚ Ω a ha)
    (arithmeticGlobalClassesModOutsideStageTransition ℚ Ω a ha) F
  refine ⟨i.hom v, ?_⟩
  intro g
  have hv' := congrFun hv (AlgEquiv.restrictNormalHom F g)
  calc
    (arithmeticClassesModOutsideColimitRep ℚ Ω a ha).ρ g (i.hom v) - i.hom v =
        i.hom ((arithmeticGlobalClassesModOutsideStageRep ℚ Ω a ha F).ρ g v - v) := by
      rw [map_sub, Rep.hom_comm_apply]
    _ = i.hom (d (AlgEquiv.restrictNormalHom F g)) := congrArg i.hom hv'
    _ = c.val g := hd g

/-- The actual continuous H1 of the original arithmetic full-class quotient modulo outside units is zero. -/
theorem rationalArithmeticClassesModOutsideContinuousH1_eq_zero
    (x : ContinuousRepresentationH1 (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)
      (arithmeticClassesModOutsideColimitAction_continuous ℚ Ω a ha)) : x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    obtain ⟨v, hv⟩ := rationalArithmeticClassOneCocycle_exists_coboundary Ω a ha c
    refine ⟨v, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    funext g
    exact hv g

end
end Dubon2026
