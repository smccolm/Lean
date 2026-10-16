import Dubon2026.ArithmeticRelativeStageNormalizedClassInvariants
import Dubon2026.OriginalGlobalH2IdeleInjection

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
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageUpperTopology arithmeticRelativeStageUpperDiscrete arithmeticOrbitUpperGalois

variable (a : 𝓞 ℚ)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  (H : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ H]
  (hFH : F ≤ H)
  [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    IsGalois F H]

/-- In an actual odd-primary cyclic stage, zero original-prime total is exactly the existence of an original global unit H2 class mapping to the given full-idele class. -/
theorem rationalArithmeticRelativeStage_total_zero_iff_principal
    (q r : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hcyclic : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsCyclic Gal(H/F))
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ (r + 1))
    (x : rationalArithmeticRelativeStageIdeleH2 a F H hFH) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    rationalArithmeticRelativeStageIdeleTotalInvariant a F H hFH x = 0 ↔
      ∃ y : groupCohomology (Rep.ofAlgebraAutOnUnits F H) 2,
        (groupCohomology.functor ℤ Gal(H/F) 2).map (originalFullPrincipalRepHom F H) y = x := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  obtain ⟨invG, hi, _, ht⟩ := rationalArithmeticRelativeStage_exists_normalized_class_invariants
    a F H hFH q r hq hq2 hqa hcyclic hdegree
  have hz : rationalArithmeticRelativeStageIdeleTotalInvariant a F H hFH x = 0 ↔
      (groupCohomology.functor ℤ Gal(H/F) 2).map (originalFullClassRepHom F H) x = 0 := by
    rw [← ht x]
    exact map_eq_zero_iff invG hi
  exact hz.trans (originalFullPrincipalH2_range_iff_class_zero F H x).symm

end
end Dubon2026
