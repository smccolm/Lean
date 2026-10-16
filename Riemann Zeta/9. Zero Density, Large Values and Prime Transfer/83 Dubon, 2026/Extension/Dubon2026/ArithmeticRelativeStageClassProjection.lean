import Dubon2026.ArithmeticRelativeStageNormalizedClassInvariants

/-! # The literal relative-stage original class projection

Name the actual class cohomology and projection so the auxiliary transfer
can retain its original maps without repeatedly elaborating their large
representations. The zero-total theorem uses the already proved injective
class invariant, and serves DUB-17's auxiliary restriction-vanishing step.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup

variable (a : 𝓞 ℚ)
  (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ H] (hFH : F ≤ H)

/-- The original idele-class H2 over the literal relative arithmetic stage. -/
def rationalArithmeticRelativeStageClassH2 : Type := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  exact ↥(groupCohomology (originalIdeleClassRep F H) 2)

/-- The actual additive group on the original relative-stage class cohomology. -/
local instance arithmeticRelativeStageClassAddCommGroup :
    AddCommGroup (rationalArithmeticRelativeStageClassH2 a F H hFH) := by
  dsimp only [rationalArithmeticRelativeStageClassH2]
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  infer_instance

/-- The actual full-idele to idele-class H2 projection, as an additive map. -/
def rationalArithmeticRelativeStageClassProjection :
    rationalArithmeticRelativeStageIdeleH2 a F H hFH →+
      rationalArithmeticRelativeStageClassH2 a F H hFH := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  exact ((groupCohomology.functor ℤ Gal(H/F) 2).map
    (originalFullClassRepHom F H)).hom.toAddMonoidHom

/-- The named projection is the original class-coefficient map on exactly the same cohomology class. -/
theorem rationalArithmeticRelativeStageClassProjection_eq
    (x : rationalArithmeticRelativeStageIdeleH2 a F H hFH) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    rationalArithmeticRelativeStageClassProjection a F H hFH x =
      (groupCohomology.functor ℤ Gal(H/F) 2).map (originalFullClassRepHom F H) x := rfl

variable [FiniteDimensional ℚ F]
  [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    IsGalois F H]

/-- The proved injective original invariant sends a zero canonical total to the zero class, for the same full-idele witness. -/
theorem rationalArithmeticRelativeStageClassProjection_zero_of_total
    (q r : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hcyclic : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsCyclic Gal(H/F))
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ (r + 1))
    (x : rationalArithmeticRelativeStageIdeleH2 a F H hFH)
    (hx : rationalArithmeticRelativeStageIdeleTotalInvariant a F H hFH x = 0) :
    rationalArithmeticRelativeStageClassProjection a F H hFH x = 0 := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  obtain ⟨invG, hi, _, ht⟩ := rationalArithmeticRelativeStage_exists_normalized_class_invariants
    a F H hFH q r hq hq2 hqa hcyclic hdegree
  apply hi
  exact (ht x).trans (hx.trans (map_zero invG).symm)

end
end Dubon2026
