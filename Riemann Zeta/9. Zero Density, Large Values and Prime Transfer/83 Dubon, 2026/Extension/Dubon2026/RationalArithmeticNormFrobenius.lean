import Dubon2026.RationalNormFrobeniusClass
import Dubon2026.RationalArithmeticFiniteInertiaTrivial

/-! # The same arithmetic restriction preserves actual residue Frobenius

This is the entry bridge from selected finite Frobenius classes to the
original local tame deformation classification needed for Dubon Theorem 2.6.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField

attribute [local instance] rationalPrimeLocalField_charZero rationalArithmeticOriginalFiniteGalois
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric algebraicLocalIntegerAction
attribute [local instance 1100] rationalPrimeOriginalNormedField

/-- Every actual arithmetic residue Frobenius has the finite conjugacy class
used to select the original auxiliary prime, for the same retained finite field. -/
theorem rationalArithmetic_original_residue_frobenius_class
    (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
    (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    (hunr : Chebotarev.UnramifiedIn ℚ F (Ideal.span {(p : 𝓞 ℚ)}))
    (φ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp))
    (hφ : ∀ x : IsLocalRing.ResidueField (algebraicLocalIntegerRing
      (rationalPrimeLocalClosure p hp)), φ • x = x ^ p) :
    Chebotarev.frobeniusClass ℚ F (Ideal.span {(p : 𝓞 ℚ)}) =
      ConjClasses.mk (AlgEquiv.restrictNormalHom F
        (rationalPrimeArithmeticRestriction a p hp φ)) := by
  let U := rationalUnramifiedExtension a
  letI : NumberField F := NumberField.of_module_finite ℚ F
  let f := rationalPrimeArithmeticOriginalEmbedding a p hp
  let e : F →+* rationalPrimeLocalClosure p hp := f.comp (algebraMap F U)
  let σ : Gal(F/ℚ) := AlgEquiv.restrictNormalHom F (rationalPrimeArithmeticRestriction a p hp φ)
  have he (x : F) : e (σ x) = φ (e x) := by
    let g : Gal(U/ℚ) := rationalPrimeArithmeticRestriction a p hp φ
    have hr := g.restrictNormal_commutes F x
    have hmap := congrArg f hr
    have hlocal := rationalPrimeArithmeticRestriction_commutes a p hp φ (algebraMap F U x)
    exact hmap.trans hlocal
  exact algebraicLocal_frobenius_class_of_original_residue e p hp
    (rationalPrimeOriginalClosureNorm_prime_lt_one p hp) hunr σ φ he hφ

end
end Dubon2026
