import Dubon2026.ArithmeticRealUnitH2Inflation
import Dubon2026.ContinuousCoefficientMackey
import Dubon2026.GaloisUnitCorestrictionCocycleComparison

/-! # Actual real restriction of original field corestriction

The native continuous coefficient Mackey theorem is applied to the same
original real field embedding. All orbit indices are finite by the
original finite subfield and the actual group Gal(C/R). This serves
DUB-17's remaining kernel obligation: vanishing of the original infinite
coordinates must force vanishing of the real restriction of corestriction.
The literal infinite-completion comparison remains a separate step.
-/
namespace Dubon2026
noncomputable section
open scoped BigOperators NumberField

attribute [-instance] UniformSpace.Completion.instSMul SubfieldClass.instSMulRat
  DivisionRing.toRatAlgebra AlgebraicClosure.instSMulOfIsScalarTower
attribute [local instance] arithmeticKummerStageAlgebra arithmeticKummerStageGalois
  arithmeticKummerStageTopology arithmeticKummerStageDiscrete arithmeticGlobalUnitContinuousSMul
  originalRealPeriodQuadratic arithmeticRealGlobalClosureAlgebra arithmeticRealGlobalClosureSMul
  arithmeticRealGlobalClosureTower

variable (a : 𝓞 ℚ)
  [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits ℝ ℂ)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits ℝ ℂ)]
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]

/-- The original arithmetic union remains Galois over the same finite subfield. -/
local instance arithmeticRealOrbitUpperGalois : IsGalois F (rationalUnramifiedExtension a) :=
  IsGalois.tower_top_of_isGalois ℚ F (rationalUnramifiedExtension a)

/-- The actual finite subfield gives finite global fixing-subgroup index. -/
local instance arithmeticRealOrbitGlobalFinite :
    Finite (Gal(rationalUnramifiedExtension a/ℚ) ⧸ F.fixingSubgroup) :=
  Subgroup.quotient_finite_of_isOpen F.fixingSubgroup F.fixingSubgroup_isOpen

/-- Enumerate the same finite fixing-subgroup cosets. -/
local instance arithmeticRealOrbitGlobalFintype :
    Fintype (Gal(rationalUnramifiedExtension a/ℚ) ⧸ F.fixingSubgroup) := Fintype.ofFinite _

/-- The actual real orbit quotient is finite as a quotient of the same global cosets. -/
local instance arithmeticRealOrbitIndexFinite :
    Finite (cosetOrbitIndex (galoisBaseChangeRestriction ℚ ℝ (rationalUnramifiedExtension a) ℂ)
      F.fixingSubgroup) :=
  Finite.of_surjective (fun c : Gal(rationalUnramifiedExtension a/ℚ) ⧸ F.fixingSubgroup =>
    (Quotient.mk'' c : cosetOrbitIndex
      (galoisBaseChangeRestriction ℚ ℝ (rationalUnramifiedExtension a) ℂ) F.fixingSubgroup))
    (fun ω => Quotient.inductionOn' ω (fun c => ⟨c, rfl⟩))

/-- Enumerate the exact original real orbit quotient. -/
local instance arithmeticRealOrbitIndexFintype :
    Fintype (cosetOrbitIndex (galoisBaseChangeRestriction ℚ ℝ (rationalUnramifiedExtension a) ℂ)
      F.fixingSubgroup) := Fintype.ofFinite _

/-- Every actual real orbit stabilizer has finite index in Gal(C/R). -/
local instance arithmeticRealOrbitStabilizerFintype
    (c : Gal(rationalUnramifiedExtension a/ℚ) ⧸ F.fixingSubgroup) :
    Fintype (Gal(ℂ/ℝ) ⧸ cosetOrbitStabilizer
      (galoisBaseChangeRestriction ℚ ℝ (rationalUnramifiedExtension a) ℂ) F.fixingSubgroup c) :=
  Fintype.ofFinite _

/-- The exact orbit-indexed family uses the same finite real stabilizer cosets. -/
local instance arithmeticRealOrbitStabilizerFamily :
    ∀ ω : cosetOrbitIndex (galoisBaseChangeRestriction ℚ ℝ (rationalUnramifiedExtension a) ℂ) F.fixingSubgroup,
      Fintype (Gal(ℂ/ℝ) ⧸ cosetOrbitStabilizer
        (galoisBaseChangeRestriction ℚ ℝ (rationalUnramifiedExtension a) ℂ) F.fixingSubgroup ω.out) :=
  fun ω => arithmeticRealOrbitStabilizerFintype a F ω.out

variable [TopologicalSpace (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))]

/-- The actual real orbit cocycle uses the original field cocycle, original
fixing-subgroup identification and literal real coefficient embedding. -/
def rationalArithmeticRealOrbitUnitCocycle
    (c : Gal(rationalUnramifiedExtension a/ℚ) ⧸ F.fixingSubgroup)
    (y : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))) :
    continuousRepresentationCocyclesTwo
      (restrictedCoefficientRep (Rep.ofAlgebraAutOnUnits ℝ ℂ)
        (cosetOrbitStabilizer (galoisBaseChangeRestriction ℚ ℝ (rationalUnramifiedExtension a) ℂ)
          F.fixingSubgroup c).subtype) :=
  continuousCoefficientCocycleTwoMap
    (restrictedCoefficientRep (restrictedCoefficientRep (Rep.ofAlgebraAutOnUnits ℚ (rationalUnramifiedExtension a))
      (galoisBaseChangeRestriction ℚ ℝ (rationalUnramifiedExtension a) ℂ))
      (cosetOrbitStabilizer (galoisBaseChangeRestriction ℚ ℝ (rationalUnramifiedExtension a) ℂ)
        F.fixingSubgroup c).subtype)
    (restrictedCoefficientRep (Rep.ofAlgebraAutOnUnits ℝ ℂ)
      (cosetOrbitStabilizer (galoisBaseChangeRestriction ℚ ℝ (rationalUnramifiedExtension a) ℂ)
        F.fixingSubgroup c).subtype)
    (galoisUnitBaseChangeInclusion ℚ ℝ (rationalUnramifiedExtension a) ℂ).hom.toLinearMap
    continuous_of_discreteTopology
    (fun d x => Rep.hom_comm_apply (galoisUnitBaseChangeInclusion ℚ ℝ (rationalUnramifiedExtension a) ℂ) d x)
    (continuousCosetOrbitCocycle (Rep.ofAlgebraAutOnUnits ℚ (rationalUnramifiedExtension a))
      (discreteGaloisUnitAction_continuous (K := ℚ) (Ω := rationalUnramifiedExtension a))
      (galoisBaseChangeRestriction ℚ ℝ (rationalUnramifiedExtension a) ℂ)
      (galoisBaseChangeRestriction_continuous ℚ ℝ (rationalUnramifiedExtension a) ℂ)
      F.fixingSubgroup c (galoisFixingUnitCocycle ℚ (rationalUnramifiedExtension a) F y))

/-- The original real orbit trace is the genuine subgroup corestriction
of the literal real orbit cocycle into the actual complex-unit H2. -/
def rationalArithmeticRealOrbitUnitTrace
    (c : Gal(rationalUnramifiedExtension a/ℚ) ⧸ F.fixingSubgroup)
    (y : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))) :
    GaloisUnitContinuousH2 (K := ℝ) (Ω := ℂ) :=
  continuousRepresentationH2Corestriction (Rep.ofAlgebraAutOnUnits ℝ ℂ)
    (discreteGaloisUnitAction_continuous (K := ℝ) (Ω := ℂ))
    (cosetOrbitStabilizer (galoisBaseChangeRestriction ℚ ℝ (rationalUnramifiedExtension a) ℂ) F.fixingSubgroup c)
    (cosetOrbitStabilizer_isOpen _
      (galoisBaseChangeRestriction_continuous ℚ ℝ (rationalUnramifiedExtension a) ℂ)
      F.fixingSubgroup F.fixingSubgroup_isOpen c)
    (Submodule.Quotient.mk (rationalArithmeticRealOrbitUnitCocycle a F c y))

/-- Real restriction of genuine original field corestriction is exactly
the sum of the actual real orbit traces, with finiteness derived internally. -/
theorem rationalArithmeticUnitCorestriction_realRestriction
    (y : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))) :
    rationalArithmeticRealUnitH2Restriction a
      (galoisUnitContinuousCorestriction ℚ (rationalUnramifiedExtension a) F (Submodule.Quotient.mk y)) =
      ∑ ω : cosetOrbitIndex (galoisBaseChangeRestriction ℚ ℝ (rationalUnramifiedExtension a) ℂ) F.fixingSubgroup,
        rationalArithmeticRealOrbitUnitTrace a F ω.out y := by
  have htrace := galoisUnitContinuousCorestriction_eq_subgroupTrace ℚ (rationalUnramifiedExtension a) F
    F.fixingSubgroup F.fixingSubgroup_isOpen rfl
    (galoisFixingUnitCocycle ℚ (rationalUnramifiedExtension a) F y) y (fun _ _ => rfl)
  have hm := continuousCoefficientH2Map_restriction_corestriction_orbits
    (Rep.ofAlgebraAutOnUnits ℚ (rationalUnramifiedExtension a))
    (discreteGaloisUnitAction_continuous (K := ℚ) (Ω := rationalUnramifiedExtension a))
    (galoisBaseChangeRestriction ℚ ℝ (rationalUnramifiedExtension a) ℂ)
    (galoisBaseChangeRestriction_continuous ℚ ℝ (rationalUnramifiedExtension a) ℂ)
    (Rep.ofAlgebraAutOnUnits ℝ ℂ)
    (discreteGaloisUnitAction_continuous (K := ℝ) (Ω := ℂ))
    (galoisUnitBaseChangeInclusion ℚ ℝ (rationalUnramifiedExtension a) ℂ).hom.toLinearMap
    continuous_of_discreteTopology
    (Rep.hom_comm_apply (galoisUnitBaseChangeInclusion ℚ ℝ (rationalUnramifiedExtension a) ℂ))
    F.fixingSubgroup F.fixingSubgroup_isOpen
    (galoisFixingUnitCocycle ℚ (rationalUnramifiedExtension a) F y)
  exact (congrArg (rationalArithmeticRealUnitH2Restriction a) htrace.symm).trans hm

end
end Dubon2026
