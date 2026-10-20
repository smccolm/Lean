import Dubon2026.FiniteBaseRealConjugation

/-! For an actual totally complex quadratic extension of the totally real
base, the original real-place involution lies in the nonidentity component.
This supplies the source CM component normalization for DUB-17. -/

namespace Dubon2026
open NumberField Algebra
open scoped NumberField
noncomputable section

/-- Retain the original rational algebra when comparing the real and CM fields. -/
local instance finiteBaseCMUnionAlgebra (a : 𝓞 ℚ) :
    Algebra ℚ (rationalUnramifiedExtension a) := (rationalUnramifiedExtension a).algebra'

variable (a : 𝓞 ℚ) (F : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ F] [IsTotallyReal F]
  (K : IntermediateField F (rationalUnramifiedExtension a))
  [IsQuadraticExtension F K] [IsTotallyComplex K]

/-- The original real-place involution acts nontrivially on the actual CM field. -/
theorem finiteBaseCMComponent_conjugation_ne_one :
    finiteBaseQuadraticComponent a F K (finiteBaseRealConjugation a F) ≠ 1 := by
  intro h
  have hfix := (finiteBaseQuadraticComponent_eq_one_iff a F K _).mp h
  let φ : K →+* ℂ := (rationalArithmeticLocalEmbedding (K := ℂ) a).toRingHom.comp K.val.toRingHom
  apply IsTotallyComplex.complexEmbedding_not_isReal φ
  apply ComplexEmbedding.isReal_iff.mpr
  apply RingHom.ext
  intro x
  exact (finiteBaseRealConjugation_commutes a F x).symm.trans
    (congrArg (rationalArithmeticLocalEmbedding (K := ℂ) a) (hfix x))

/-- The actual real-place involution has the unique nonidentity source component. -/
theorem finiteBaseCMComponent_conjugation :
    finiteBaseQuadraticComponent a F K (finiteBaseRealConjugation a F) =
      Multiplicative.ofAdd (1 : ZMod 2) := by
  have hn := finiteBaseCMComponent_conjugation_ne_one a F K
  have hz : (finiteBaseQuadraticComponent a F K (finiteBaseRealConjugation a F)).toAdd ≠ 0 := by
    intro h
    exact hn h
  change (finiteBaseQuadraticComponent a F K (finiteBaseRealConjugation a F)).toAdd = (1 : ZMod 2)
  generalize (finiteBaseQuadraticComponent a F K (finiteBaseRealConjugation a F)).toAdd = z at hz ⊢
  fin_cases z
  · exact (hz rfl).elim
  · rfl

include K in
/-- The same original CM arithmetic group contains the constructed nontrivial involution. -/
theorem finiteBaseCMConjugation_ne_one : finiteBaseRealConjugation a F ≠ 1 := by
  intro h
  have hn := finiteBaseCMComponent_conjugation_ne_one a F K
  rw [h, map_one] at hn
  exact hn rfl

end
end Dubon2026
