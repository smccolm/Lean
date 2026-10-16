import Dubon2026.ArithmeticRelativeStageNormalizedIdeleTotal
import Dubon2026.ArithmeticRelativeStageClassInvariantDescent
import Dubon2026.OriginalIdeleClassFiniteGaloisCohomology

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

/-- Actual odd-primary cyclic arithmetic stages have a constructed full-order original idele-class H2 element, normalized by the descended original-prime total. -/
theorem rationalArithmeticRelativeStage_exists_full_order_class
    (q r : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hcyclic : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsCyclic Gal(H/F))
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ (r + 1)) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    ∃ invC : groupCohomology (originalIdeleClassRep F H) 2 →+ AddCircle (1 : ℚ),
    ∃ u : groupCohomology (originalIdeleClassRep F H) 2,
      (∀ x : rationalArithmeticRelativeStageIdeleH2 a F H hFH,
        invC ((groupCohomology.functor ℤ Gal(H/F) 2).map (originalFullClassRepHom F H) x) =
          rationalArithmeticRelativeStageIdeleTotalInvariant a F H hFH x) ∧
      invC u = (↑((1 : ℚ) / (q ^ (r + 1) : ℕ)) : AddCircle (1 : ℚ)) ∧
      addOrderOf u = q ^ (r + 1) := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := hGal
  obtain ⟨invC, hInv⟩ := rationalArithmeticRelativeStage_exists_class_invariant
    a F H hFH q r hq hq2 hqa hcyclic hdegree
  obtain ⟨x, hx⟩ := rationalArithmeticRelativeStage_exists_normalized_idele_total
    a F H hFH q r hq hcyclic hdegree
  let u := (groupCohomology.functor ℤ Gal(H/F) 2).map (originalFullClassRepHom F H) x
  have hu : invC u = (↑((1 : ℚ) / (q ^ (r + 1) : ℕ)) : AddCircle (1 : ℚ)) := (hInv x).trans hx
  have hi : addOrderOf (invC u) = q ^ (r + 1) := by
    rw [hu]
    letI : Fact (0 < (1 : ℚ)) := ⟨by norm_num⟩
    exact AddCircle.addOrderOf_period_div (p := (1 : ℚ)) (pow_pos hq.pos (r + 1))
  have hd := (originalIdeleClass_finiteGalois_second_card_dvd F H).2
  have hupper : addOrderOf u ∣ q ^ (r + 1) :=
    (addOrderOf_dvd_natCard u).trans (hdegree ▸ hd)
  have hlower : q ^ (r + 1) ∣ addOrderOf u := hi ▸ addOrderOf_map_dvd invC u
  exact ⟨invC, u, hInv, hu, Nat.dvd_antisymm hupper hlower⟩

end
end Dubon2026
