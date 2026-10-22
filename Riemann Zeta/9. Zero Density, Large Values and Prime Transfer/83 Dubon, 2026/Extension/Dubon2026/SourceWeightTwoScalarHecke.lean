import Dubon2026.SourceWeightTwoParabolicPeriods
import Dubon2026.SourcePeriodHeckeCohomology
import Dubon2026.SourceTrivialIntegralHecke

/-! DUB-17/18 -> original parabolic Hecke realization -> actual period-pair
Hecke equivariance. Evaluate the existing full polynomial period-cocycle
identity at the degree-zero constant. Its coboundary vanishes, and the
remaining sum is exactly the already constructed trivial-coefficient Hecke
operator under the native H1/additive-character identification.
-/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup Matrix.SpecialLinearGroup groupCohomology MvPolynomial
open SourceModularSymbols OnePoint
open scoped MatrixGroups BigOperators

private local instance primeNeZero {N : ℕ} (ell : sourceBinaryHeckePrime N) :
    NeZero ell.val := ⟨ell.property.1.ne_zero⟩

theorem sourceWeightTwoConstant_diagonal (p : ℕ)
    (L : Module.Dual ℂ (homogeneousSubmodule (Fin 2) ℂ 0)) :
    sourceHeckeDualDiagonal 0 p L sourceWeightTwoConstant = L sourceWeightTwoConstant := by
  change L (sourceModularBinaryFormAdjugateRep ℂ 0 (integralTriangularMatrix 1 p 0)
    sourceWeightTwoConstant) = L sourceWeightTwoConstant
  apply congrArg L
  apply Subtype.ext
  change matrixPolynomialAction _ (1 : MvPolynomial (Fin 2) ℂ) = 1
  exact map_one _

/-- The original trivial-coefficient Hecke operator on native additive characters. -/
def sourceWeightTwoHeckeHom (N : ℕ) (ell : sourceBinaryHeckePrime N) :
    Module.End ℂ (Additive (Gamma0 N) →+ ℂ) :=
  (H1IsoOfIsTrivial (Rep.trivial ℂ (Gamma0 N) ℂ)).hom.hom.comp
    ((sourceTrivialRingHeckeOperators ℂ N ell).comp
      (H1IsoOfIsTrivial (Rep.trivial ℂ (Gamma0 N) ℂ)).inv.hom)

theorem sourceWeightTwoHeckeHom_apply (N : ℕ) (ell : sourceBinaryHeckePrime N)
    (φ : Additive (Gamma0 N) →+ ℂ) (γ : Gamma0 N) :
    sourceWeightTwoHeckeHom N ell φ (Additive.ofMul γ) =
      letI : NeZero ell.val := ⟨ell.property.1.ne_zero⟩
      letI := sourceHeckeUpperFintype N ell.val
      ∑ q : Gamma0 N ⧸ heckeUpperSubgroup N ell.val,
        φ (Additive.ofMul (sourceHeckeConjugation ell.property.1
          (cosetTransition (heckeUpperSubgroup N ell.val) γ q))) := by
  letI : NeZero ell.val := ⟨ell.property.1.ne_zero⟩
  letI := sourceHeckeUpperFintype N ell.val
  change (H1IsoOfIsTrivial (Rep.trivial ℂ (Gamma0 N) ℂ)).hom
    (sourceTrivialRingHeckeOperators ℂ N ell
      ((H1IsoOfIsTrivial (Rep.trivial ℂ (Gamma0 N) ℂ)).inv φ)) (Additive.ofMul γ) = _
  rw [sourceTrivialRingHecke_hom_apply]
  simp only [CategoryTheory.Iso.inv_hom_id_apply]

theorem sourceWeightTwoPeriodValue_hecke (N : ℕ) [NeZero N]
    (ell : sourceBinaryHeckePrime N) (f : CuspForm (Gamma0 N) 2) (γ : Gamma0 N) :
    sourceWeightTwoPeriodValue (Gamma0 N) (cuspHeckePrime ell.property.1 f) γ =
      sourceWeightTwoHeckeHom N ell (sourceWeightTwoPeriodHom (Gamma0 N) f) (Additive.ofMul γ) := by
  letI : NeZero ell.val := ⟨ell.property.1.ne_zero⟩
  letI := sourceHeckeUpperFintype N ell.val
  have he := congrArg (fun L : Module.Dual ℂ (homogeneousSubmodule (Fin 2) ℂ 0) =>
    L sourceWeightTwoConstant)
    (sourcePeriodCocycle_hecke ell.property.1 ell.property.2 f (w := 0) (by norm_num) ∞ γ)
  simp only [LinearMap.add_apply, LinearMap.sub_apply] at he
  rw [sourcePeriodDualRep_apply, sourceWeightTwoConstant_fixed, add_sub_cancel_right] at he
  rw [sourceWeightTwoPeriodValue_cocycle, he, sourceHeckeCocycle_apply]
  rw [sourceWeightTwoHeckeHom_apply]
  simp only [LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro q _
  rw [sourcePeriodDualRep_apply, sourceWeightTwoConstant_fixed, sourceWeightTwoConstant_diagonal]
  rfl

theorem sourceWeightTwoPeriodHom_hecke (N : ℕ) [NeZero N]
    (ell : sourceBinaryHeckePrime N) (f : CuspForm (Gamma0 N) 2) :
    sourceWeightTwoPeriodHom (Gamma0 N) (cuspHeckePrime ell.property.1 f) =
      sourceWeightTwoHeckeHom N ell (sourceWeightTwoPeriodHom (Gamma0 N) f) := by
  ext γ
  exact sourceWeightTwoPeriodValue_hecke N ell f γ

end
end Dubon2026
