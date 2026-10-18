import Dubon2026.ArithmeticOriginalBottomPrimeEquiv
import Dubon2026.OriginalAdicDecompositionDegree

/-! The original completion inclusion from the rationals to the arithmetic
bottom field has degree one. Native decomposition-degree comparison and
Lagrange's theorem discharge the local factor in DUB-17's canonical total
base-change formula; no local normalization factor is supplied. -/
namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField

/-- The actual bottom-field completion has degree one over its original
rational completion, as its decomposition group divides a group of order one. -/
theorem arithmeticOriginalBottomCompletion_finrank
    (a : 𝓞 ℚ) (v : HeightOneSpectrum (𝓞 ℚ))
    (u : HeightOneSpectrum (𝓞 (⊥ : IntermediateField ℚ (rationalUnramifiedExtension a))))
    [u.asIdeal.LiesOver v.asIdeal] :
    letI : Algebra (v.adicCompletion ℚ)
      (u.adicCompletion (⊥ : IntermediateField ℚ (rationalUnramifiedExtension a))) :=
      (originalAdicBaseChangeMap ℚ (⊥ : IntermediateField ℚ (rationalUnramifiedExtension a)) v u).toAlgebra
    Module.finrank (v.adicCompletion ℚ)
      (u.adicCompletion (⊥ : IntermediateField ℚ (rationalUnramifiedExtension a))) = 1 := by
  let K : IntermediateField ℚ (rationalUnramifiedExtension a) := ⊥
  letI : Algebra (v.adicCompletion ℚ) (u.adicCompletion K) :=
    (originalAdicBaseChangeMap ℚ K v u).toAlgebra
  rw [originalAdicBaseChange_finrank_eq_decomposition_card]
  have hd : Nat.card Gal(K/ℚ) = 1 :=
    (IsGalois.card_aut_eq_finrank ℚ K).trans IntermediateField.finrank_bot
  apply Nat.dvd_one.mp
  exact hd ▸ (OriginalFiniteDecompositionGroup ℚ K u).card_subgroup_dvd_card

end
end Dubon2026
