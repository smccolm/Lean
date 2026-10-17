import Dubon2026.ArithmeticRealH2Restriction
import Dubon2026.ArithmeticFiniteLocalStage
import Dubon2026.ArithmeticCyclotomicRealSignAction
import Dubon2026.CyclotomicConjugationPower

/-! # Actual real restriction agrees with original cyclotomic conjugation

The existing real arithmetic restriction uses the original embedding into
the complex numbers. Its finite restriction therefore acts by actual
complex conjugation under that same embedding. The proved cyclotomic
character identifies it with the real factor of DUB-17's principal product.
The subsequent real-place cohomology comparison remains separate.
-/
namespace Dubon2026
noncomputable section
open NumberField
open scoped NumberField

attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois

variable (a : 𝓞 ℚ) (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))

/-- The original real arithmetic restriction, followed by literal finite
restriction to the same original global field. -/
def rationalRealArithmeticFiniteRestriction : Gal(ℂ/ℝ) →* Gal(F/ℚ) :=
  (AlgEquiv.restrictNormalHom F).comp (rationalRealArithmeticRestriction a).toMonoidHom

/-- The finite real restriction acts through the exact original arithmetic
embedding into the complex numbers. -/
theorem rationalRealArithmeticFiniteRestriction_commutes (σ : Gal(ℂ/ℝ)) (x : F) :
    rationalArithmeticLocalEmbedding (K := ℂ) a
      ((rationalRealArithmeticFiniteRestriction a F σ x : F) : rationalUnramifiedExtension a) =
      σ (rationalArithmeticLocalEmbedding (K := ℂ) a (x : rationalUnramifiedExtension a)) := by
  let g : Gal(rationalUnramifiedExtension a / ℚ) := rationalRealArithmeticRestriction a σ
  have hF := g.restrictNormal_commutes F x
  have hC := rationalArithmeticLocalRestrictionContinuous_commutes
    (F := ℝ) (K := ℂ) a σ (x : rationalUnramifiedExtension a)
  exact (congrArg (rationalArithmeticLocalEmbedding (K := ℂ) a) hF).trans hC

variable (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} ℚ F]

/-- Actual complex conjugation restricts to the existing cyclotomic
conjugation on the original containing field. -/
theorem rationalRealArithmeticFiniteRestriction_conjugation :
    rationalRealArithmeticFiniteRestriction a F Complex.conjAe =
      rationalCyclotomicConjugation n F := by
  let φ : F →+* ℂ :=
    ((rationalArithmeticLocalEmbedding (K := ℂ) a).comp F.toIntermediateField.val).toRingHom
  let c : Gal(F/ℚ) := rationalRealArithmeticFiniteRestriction a F Complex.conjAe
  have hc : ComplexEmbedding.IsConj φ c := by
    apply RingHom.ext
    intro x
    exact (rationalRealArithmeticFiniteRestriction_commutes a F Complex.conjAe x).symm
  let hζ := IsCyclotomicExtension.zeta_spec n ℚ F
  apply IsPrimitiveRoot.autToPow_injective ℚ hζ
  exact (originalCyclotomicConjugation_power hζ φ c hc).trans
    (rationalCyclotomicConjugation_autToPow n F hζ).symm

/-- The sign-selected original real automorphism gives exactly the
cyclotomic real factor used in the proved principal product. -/
theorem rationalRealArithmeticFiniteRestriction_sign (q : ℚˣ) :
    rationalRealArithmeticFiniteRestriction a F
      (if 0 < q.val then 1 else Complex.conjAe) =
      rationalCyclotomicRealSignAut n F q := by
  by_cases hq : 0 < q.val
  · simp only [hq, if_true, map_one, rationalCyclotomicRealSignAut]
  · simp only [hq, if_false, rationalCyclotomicRealSignAut]
    exact rationalRealArithmeticFiniteRestriction_conjugation a F n

end
end Dubon2026
