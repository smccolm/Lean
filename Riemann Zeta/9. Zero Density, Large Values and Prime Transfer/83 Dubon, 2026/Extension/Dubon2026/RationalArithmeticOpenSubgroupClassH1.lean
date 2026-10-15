import Dubon2026.ArithmeticOpenSubgroupClassCocycleDescent
import Dubon2026.OriginalClassQuotientSubgroupCohomology
import Dubon2026.ArithmeticClassesModOutsideH1

/-! # Original class-quotient H1 vanishes on every open arithmetic subgroup

Each actual continuous cocycle descends to the actual image of the open
subgroup at a finite Galois stage. Proved fixed-field class H1 vanishing
gives a coboundary there, and the original colimit map returns its witness.
This discharges the open-subgroup H1 condition for the P-class formation needed
by DUB-17; degree-two invariant maps and Ext duality remain necessary.
-/

namespace Dubon2026
noncomputable section
open NumberField CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- The original arithmetic union carries its literal rational inclusion. -/
local instance openClassH1UnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]

/-- Scalar multiplication is continuous for the original discrete class coefficient. -/
local instance openClassH1ContinuousSMul : @ContinuousSMul ℤ (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)
    (arithmeticClassesModOutsideColimitRep ℚ Ω a ha).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩

/-- The actual open arithmetic subgroup carries its induced topological group structure. -/
local instance openClassH1TopologicalGroup (H : OpenSubgroup Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ)) :
    IsTopologicalGroup H := inferInstanceAs (IsTopologicalGroup H.toSubgroup)

/-- Every actual continuous class cocycle on every original open arithmetic subgroup has an original class-coefficient coboundary witness. -/
theorem rationalArithmeticOpenSubgroupClassOneCocycle_exists_coboundary
    (H : OpenSubgroup Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ))
    (c : continuousRepresentationCocyclesOne (restrictedCoefficientRep
      (arithmeticClassesModOutsideColimitRep ℚ Ω a ha) H.toSubgroup.subtype)) :
    ∃ v : arithmeticClassesModOutsideColimitRep ℚ Ω a ha,
      ∀ g : H, (arithmeticClassesModOutsideColimitRep ℚ Ω a ha).ρ g.val v - v = c.val g := by
  have hDescent := arithmeticOpenSubgroupClassOneCocycle_exists_finite_descent ℚ Ω a ha H
    (fun g => c.val g) c.property ((groupCohomology.mem_cocycles₁_iff _).mp c.val.property)
  obtain ⟨F, d, hd⟩ := hDescent
  letI : Algebra ℚ F := F.algebra'
  letI : NumberField F := NumberField.of_module_finite ℚ F
  let π : H →* Gal(F/ℚ) := (AlgEquiv.restrictNormalHom F).comp H.toSubgroup.subtype
  let B := Rep.res π.range.subtype (arithmeticClassesModOutsideStageRep ℚ Ω a ha F)
  haveI : Subsingleton (groupCohomology B 1) := ModuleCat.isZero_iff_subsingleton.mp
    (originalClassQuotientSubgroup_first_zero ℚ F
      (arithmeticSUnitFiniteStageSupport ℚ Ω a ha F)
      (originalExceptionalIntegerSupport_galoisStable F ℚ a ha) π.range
      (rationalArithmeticFiniteStage_outside_unramified Ω a ha F))
  have hz : groupCohomology.H1π B d = 0 := Subsingleton.elim _ _
  obtain ⟨v, hv⟩ := (groupCohomology.H1π_eq_zero_iff d).mp hz
  let i := coefficientRepresentationColimitOf
    (arithmeticGlobalClassesModOutsideStageRep ℚ Ω a ha)
    (arithmeticGlobalClassesModOutsideStageTransition ℚ Ω a ha) F
  refine ⟨i.hom v, ?_⟩
  intro g
  have hv' := congrFun hv (π.rangeRestrict g)
  calc
    (arithmeticClassesModOutsideColimitRep ℚ Ω a ha).ρ g.val (i.hom v) - i.hom v =
        i.hom ((arithmeticGlobalClassesModOutsideStageRep ℚ Ω a ha F).ρ g.val v - v) := by
      rw [map_sub, Rep.hom_comm_apply]
    _ = i.hom (d (π.rangeRestrict g)) := congrArg i.hom hv'
    _ = c.val g := hd g

/-- The original continuous class-quotient H1 vanishes for every actual open arithmetic subgroup. -/
theorem rationalArithmeticOpenSubgroupClassesModOutsideH1_eq_zero
    (H : OpenSubgroup Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ))
    (x : ContinuousRepresentationH1 (restrictedCoefficientRep
      (arithmeticClassesModOutsideColimitRep ℚ Ω a ha) H.toSubgroup.subtype)
      (restrictedCoefficientAction_continuous _ H.toSubgroup.subtype continuous_subtype_val
        (arithmeticClassesModOutsideColimitAction_continuous ℚ Ω a ha))) : x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    have hCoboundary := rationalArithmeticOpenSubgroupClassOneCocycle_exists_coboundary Ω a ha H c
    obtain ⟨v, hv⟩ := hCoboundary
    refine ⟨v, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    funext g
    exact hv g

end
end Dubon2026
