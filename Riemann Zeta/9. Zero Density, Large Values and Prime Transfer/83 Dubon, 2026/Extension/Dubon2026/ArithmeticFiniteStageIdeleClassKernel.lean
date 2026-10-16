import Dubon2026.ArithmeticFiniteStageNormalizedClassInvariants
import Dubon2026.OriginalGlobalH2IdeleInjection

/-! # The actual principal image is the kernel of the normalized idele total

The constructed injective class invariant and the original exact sequence
identify the total's kernel with actual global unit H2. This discharges
the finite cyclic-stage H2 obstruction used by DUB-17's reciprocity route;
arbitrary-stage and reverse H1 localization remain separate obligations.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticFiniteStageIdeleAddCommGroup
  arithmeticFiniteStageUpperTopology arithmeticFiniteStageUpperDiscrete arithmeticOrbitUpperGalois

variable (a : 𝓞 ℚ)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  (H : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a)) (hFH : F ≤ H.toIntermediateField)

/-- In an actual odd-primary cyclic stage, zero original-prime total is exactly the existence of an original global unit H2 class mapping to the given full-idele class. -/
theorem rationalArithmeticFiniteStage_total_zero_iff_principal
    (q r : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hcyclic : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsCyclic Gal(H/F))
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ (r + 1))
    (x : rationalArithmeticFiniteStageIdeleH2 a F H hFH) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    rationalArithmeticFiniteStageIdeleTotalInvariant a F H hFH x = 0 ↔
      ∃ y : groupCohomology (Rep.ofAlgebraAutOnUnits F H) 2,
        (groupCohomology.functor ℤ Gal(H/F) 2).map (originalFullPrincipalRepHom F H) y = x := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  obtain ⟨invG, hi, _, ht⟩ := rationalArithmeticFiniteStage_exists_normalized_class_invariants
    a F H hFH q r hq hq2 hqa hcyclic hdegree
  have hz : rationalArithmeticFiniteStageIdeleTotalInvariant a F H hFH x = 0 ↔
      (groupCohomology.functor ℤ Gal(H/F) 2).map (originalFullClassRepHom F H) x = 0 := by
    rw [← ht x]
    exact map_eq_zero_iff invG hi
  exact hz.trans (originalFullPrincipalH2_range_iff_class_zero F H x).symm

end
end Dubon2026
