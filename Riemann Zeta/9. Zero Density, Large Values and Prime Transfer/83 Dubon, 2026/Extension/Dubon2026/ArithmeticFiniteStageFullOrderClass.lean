import Dubon2026.ArithmeticFiniteStageNormalizedIdeleTotal
import Dubon2026.ArithmeticFiniteStageClassInvariantDescent
import Dubon2026.OriginalIdeleClassFiniteGaloisCohomology

/-! # A constructed full-order original class at each odd-primary cyclic stage

The actual normalized full-idele class maps to the original idele-class
H2. The descended total gives its positive reciprocal-degree value, while
the existing finite-Galois size bound gives the opposite order divisibility.
No generator is assumed. This removes the cyclic-stage generator input on
DUB-17's normalized finite class-invariant dependency chain.
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

/-- Actual odd-primary cyclic arithmetic stages have a constructed full-order original idele-class H2 element, normalized by the descended original-prime total. -/
theorem rationalArithmeticFiniteStage_exists_full_order_class
    (q r : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hcyclic : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsCyclic Gal(H/F))
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ (r + 1)) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    ∃ invC : groupCohomology (originalIdeleClassRep F H) 2 →+ AddCircle (1 : ℚ),
    ∃ u : groupCohomology (originalIdeleClassRep F H) 2,
      (∀ x : rationalArithmeticFiniteStageIdeleH2 a F H hFH,
        invC ((groupCohomology.functor ℤ Gal(H/F) 2).map (originalFullClassRepHom F H) x) =
          rationalArithmeticFiniteStageIdeleTotalInvariant a F H hFH x) ∧
      invC u = (↑((1 : ℚ) / (q ^ (r + 1) : ℕ)) : AddCircle (1 : ℚ)) ∧
      addOrderOf u = q ^ (r + 1) := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := IsGalois.tower_top_of_isGalois ℚ F H
  obtain ⟨invC, hInv⟩ := rationalArithmeticFiniteStage_exists_class_invariant
    a F H hFH q r hq hq2 hqa hcyclic hdegree
  obtain ⟨x, hx⟩ := rationalArithmeticFiniteStage_exists_normalized_idele_total
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
