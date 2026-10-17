import Dubon2026.ArithmeticRealCyclotomicRestriction

/-! # Actual real restriction through the original containing field

The same original real arithmetic automorphism restricts through either
finite field in the tower. This identifies the restricted cyclotomic real
factor in DUB-17's principal product with the actual real arithmetic map,
without imposing a cyclotomic property on the cyclic subfield.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField

attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois

variable (a : 𝓞 ℚ)
    (E F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    (hEF : E.toIntermediateField ≤ F.toIntermediateField)

/-- The literal finite restrictions of the original real arithmetic map
commute through the actual global containing field. -/
theorem rationalRealArithmeticFiniteRestriction_tower (σ : Gal(ℂ/ℝ)) :
    embeddedNormalGaloisRestriction (F := ℚ) (IntermediateField.inclusion hEF)
      (rationalRealArithmeticFiniteRestriction a F σ) =
      rationalRealArithmeticFiniteRestriction a E σ := by
  let g : Gal(rationalUnramifiedExtension a / ℚ) := rationalRealArithmeticRestriction a σ
  let i : E →ₐ[ℚ] F := IntermediateField.inclusion hEF
  apply AlgEquiv.ext
  intro x
  apply E.toIntermediateField.val.injective
  have hleft := congrArg F.toIntermediateField.val
    (embeddedNormalGaloisRestriction_commutes i (rationalRealArithmeticFiniteRestriction a F σ) x)
  have houter := g.restrictNormal_commutes F (i x)
  have hright := g.restrictNormal_commutes E x
  exact (hleft.trans houter).trans hright.symm

variable (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} ℚ F]

/-- The restricted sign-selected cyclotomic factor is the actual real
arithmetic restriction on the original cyclic subfield. -/
theorem rationalCyclotomicRealSignAut_restrict_eq_real (q : ℚˣ) :
    embeddedNormalGaloisRestriction (F := ℚ) (IntermediateField.inclusion hEF)
      (rationalCyclotomicRealSignAut n F q) =
      rationalRealArithmeticFiniteRestriction a E (if 0 < q.val then 1 else Complex.conjAe) := by
  rw [← rationalRealArithmeticFiniteRestriction_sign a F n q]
  exact rationalRealArithmeticFiniteRestriction_tower a E F hEF _

end
end Dubon2026
