import Dubon2026.SourceArithmeticCharacterFrobeniusEquality
import Dubon2026.SourceArithmeticWeightTwist

/-! DUB-17/18 -> arithmetic automorphy -> actual fixed residual determinant.
The exact good-prime determinant of the constructed residual representation
is promoted to equality with the original cyclotomic power on the whole
arithmetic group, using the proved finite-factor character comparison. -/
namespace Dubon2026
noncomputable section
open Matrix
open scoped NumberField
attribute [local instance] rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric algebraicLocalIntegerAction
attribute [local instance 1100] rationalPrimeOriginalNormedField

theorem sourceArithmetic_determinant_eq_cyclotomic_of_frobenius
    (p : ℕ) [NeZero p] (hp : p.Prime)
    (K : Type) [Field K] [TopologicalSpace K] [DiscreteTopology K] [CharP K p]
    (a : 𝓞 ℚ) (hpa : (p : 𝓞 ℚ) ∣ a) (j : ℕ)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin 2) K)
    (hρ : Continuous ρ) (S : Finset ℕ) (hSp : p ∈ S)
    (hdet : ∀ (q : ℕ) (hq : q.Prime), q ∉ S →
      ∀ g : Gal(rationalPrimeLocalClosure q hq/rationalPrimeLocalField q hq),
        (∀ z : IsLocalRing.ResidueField (algebraicLocalIntegerRing
          (rationalPrimeLocalClosure q hq)), g • z = z ^ q) →
        (ρ (rationalPrimeArithmeticRestriction a q hq g)).val.det = (q : K) ^ j) :
    GeneralLinearGroup.det.comp ρ =
      (sourceArithmeticCyclotomicUnitCharacter (F := K) p a hpa).toMonoidHom ^ j := by
  let χdet : rationalArithmeticGaloisGroup a →ₜ* Kˣ :=
    ⟨GeneralLinearGroup.det.comp ρ,
      (show Continuous (GeneralLinearGroup.det (n := Fin 2) (R := K)) from
        continuous_of_discreteTopology).comp hρ⟩
  let χcyc : rationalArithmeticGaloisGroup a →ₜ* Kˣ :=
    ⟨(sourceArithmeticCyclotomicUnitCharacter (F := K) p a hpa).toMonoidHom ^ j,
      (sourceArithmeticCyclotomicUnitCharacter (F := K) p a hpa).continuous.pow j⟩
  have he : χdet = χcyc := by
    apply sourceArithmeticCharacters_eq_of_frobenius a χdet χcyc S
    intro q hq hqS g hg
    apply Units.ext
    change (ρ (rationalPrimeArithmeticRestriction a q hq g)).val.det =
      (((sourceArithmeticCyclotomicUnitCharacter (F := K) p a hpa).toMonoidHom ^ j)
        (rationalPrimeArithmeticRestriction a q hq g) : K)
    rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val]
    change (ρ (rationalPrimeArithmeticRestriction a q hq g)).val.det =
      ((sourceArithmeticCyclotomicUnitCharacter (F := K) p a hpa)
        (rationalPrimeArithmeticRestriction a q hq g) : K) ^ j
    rw [hdet q hq hqS g hg,
      sourceArithmeticCyclotomicUnitCharacter_frobenius p a hpa hp q hq
        (fun h => hqS (h.symm ▸ hSp)) g hg]
  exact congrArg ContinuousMonoidHom.toMonoidHom he

end
end Dubon2026
