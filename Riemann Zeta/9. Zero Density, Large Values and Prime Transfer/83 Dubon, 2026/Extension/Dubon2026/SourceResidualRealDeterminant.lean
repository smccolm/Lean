import Dubon2026.SourceArithmeticWeightTwist
import Dubon2026.ArithmeticRealH2Restriction
import Dubon2026.CyclotomicConjugationPower

/-! DUB-17/18 -> arithmetic automorphy -> oddness of the actual residual
representation. Reuse the original real arithmetic restriction and the
proved cyclotomic exponent of genuine complex conjugation. -/
namespace Dubon2026
noncomputable section
open scoped NumberField

theorem sourceArithmeticCyclotomic_conjugation
    (a : 𝓞 ℚ) (n : ℕ) [NeZero n] (hna : (n : 𝓞 ℚ) ∣ a) :
    rationalArithmeticCyclotomicCharacter a n hna
      (rationalRealArithmeticRestriction a Complex.conjAe) = -1 := by
  let U := rationalUnramifiedExtension a
  letI : Algebra ℚ U := U.algebra'
  letI : IsGalois ℚ U := originalUnramifiedGaloisUnion_isGalois a
  have hx : ∃ μ : U, IsPrimitiveRoot μ n :=
    originalQUnramifiedUnion_exists_primitiveRoot (Ω := AlgebraicClosure ℚ) a n hna
  let e : U →+* ℂ := (rationalArithmeticLocalEmbedding (K := ℂ) a).toRingHom
  have hc : NumberField.ComplexEmbedding.IsConj e
      (rationalRealArithmeticRestriction a Complex.conjAe) := by
    apply RingHom.ext
    intro x
    exact (rationalArithmeticLocalRestrictionContinuous_commutes
      (F := ℝ) (K := ℂ) a Complex.conjAe x).symm
  exact originalCyclotomicConjugation_power (Classical.choose_spec hx) e
    (rationalRealArithmeticRestriction a Complex.conjAe) hc

theorem sourceArithmeticCyclotomicUnitCharacter_conjugation
    {K : Type} [Field K] [TopologicalSpace K]
    (p : ℕ) [NeZero p] [CharP K p]
    (a : 𝓞 ℚ) (hpa : (p : 𝓞 ℚ) ∣ a) :
    (sourceArithmeticCyclotomicUnitCharacter (F := K) p a hpa
      (rationalRealArithmeticRestriction a Complex.conjAe) : K) = -1 := by
  change ZMod.castHom (dvd_refl p) K
    (rationalArithmeticCyclotomicCharacter a p hpa
      (rationalRealArithmeticRestriction a Complex.conjAe) : ZMod p) = _
  rw [sourceArithmeticCyclotomic_conjugation]
  simp

theorem sourceArithmetic_real_det_of_cyclotomic
    {K : Type} [Field K] [TopologicalSpace K]
    (p : ℕ) [NeZero p] [CharP K p]
    (a : 𝓞 ℚ) (hpa : (p : 𝓞 ℚ) ∣ a)
    (j : ℕ) (hj : Odd j)
    (ρ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup (Fin 2) K)
    (hdet : Matrix.GeneralLinearGroup.det.comp ρ =
      (sourceArithmeticCyclotomicUnitCharacter (F := K) p a hpa).toMonoidHom ^ j) :
    (ρ (rationalRealArithmeticRestriction a Complex.conjAe)).val.det = -1 := by
  have he := congrArg (fun χ => (χ
    (rationalRealArithmeticRestriction a Complex.conjAe) : K)) hdet
  change (ρ (rationalRealArithmeticRestriction a Complex.conjAe)).val.det =
    (((sourceArithmeticCyclotomicUnitCharacter (F := K) p a hpa).toMonoidHom ^ j)
      (rationalRealArithmeticRestriction a Complex.conjAe) : K) at he
  rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val] at he
  change (ρ (rationalRealArithmeticRestriction a Complex.conjAe)).val.det =
    ((sourceArithmeticCyclotomicUnitCharacter (F := K) p a hpa)
      (rationalRealArithmeticRestriction a Complex.conjAe) : K) ^ j at he
  rw [sourceArithmeticCyclotomicUnitCharacter_conjugation, hj.neg_one_pow] at he
  exact he

end
end Dubon2026
