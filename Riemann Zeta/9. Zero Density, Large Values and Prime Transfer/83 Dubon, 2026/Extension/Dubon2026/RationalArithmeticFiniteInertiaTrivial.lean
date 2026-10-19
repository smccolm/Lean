import Dubon2026.LocalIntegralUnramifiedInertia
import Dubon2026.RationalPrimeOriginalNormPrime

/-! The same original norm inertia has trivial image in the selected
unramified finite factor of the arithmetic representation. The original
embedding square, contracted prime, its rational prime below, and its
norm are all supplied by existing proved constructions. This removes
the residual inertia-triviality input for DUB-17's actual auxiliary local
deformation conditions. -/

namespace Dubon2026
noncomputable section
open scoped NumberField

/-- The literal field embedding used in the original prime restriction,
retained before equipping that same closure with its compatible norm. -/
def rationalPrimeArithmeticOriginalEmbedding
    (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime) :
    rationalUnramifiedExtension a →+* rationalPrimeLocalClosure p hp :=
  (rationalArithmeticLocalEmbedding (K := rationalPrimeLocalClosure p hp) a).toRingHom
attribute [local instance] rationalPrimeLocalField_charZero rationalArithmeticOriginalFiniteGalois
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric
attribute [local instance 1100] rationalPrimeOriginalNormedField

/-- Original prime-local inertia restricts to the identity in the very
same finite number field unramified at the selected rational prime. -/
theorem rationalArithmetic_finite_factor_inertia_eq_one
    (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
    (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    (hunr : Chebotarev.UnramifiedIn ℚ F (Ideal.span {(p : 𝓞 ℚ)}))
    (δ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp))
    (hδ : δ ∈ rationalPrimeNormInertia p hp) :
    AlgEquiv.restrictNormalHom F (rationalPrimeArithmeticRestriction a p hp δ) = 1 := by
  let U := rationalUnramifiedExtension a
  letI : NumberField F := NumberField.of_module_finite ℚ F
  let f := rationalPrimeArithmeticOriginalEmbedding a p hp
  let e : F →+* rationalPrimeLocalClosure p hp := f.comp (algebraMap F U)
  let σ : Gal(F/ℚ) :=
    AlgEquiv.restrictNormalHom F (rationalPrimeArithmeticRestriction a p hp δ)
  have he (x : F) : e (σ x) = δ (e x) := by
    let g : Gal(U/ℚ) := rationalPrimeArithmeticRestriction a p hp δ
    have hr := g.restrictNormal_commutes F x
    have hmap := congrArg f hr
    have hlocal := rationalPrimeArithmeticRestriction_commutes a p hp δ (algebraMap F U x)
    exact hmap.trans hlocal
  exact algebraicLocal_unramified_finite_inertia_eq_one e p hp
    (rationalPrimeOriginalClosureNorm_prime_lt_one p hp) hunr σ δ hδ he

/-- The original residual representation is trivial on the actual local
inertia whenever its original finite factor is unramified at that prime. -/
theorem rationalArithmetic_finite_representation_inertia_eq_one
    (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
    {T : Type} [Group T] (ρ : rationalArithmeticGaloisGroup a →* T)
    (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    (ψ : Gal(F/ℚ) →* T)
    (hψ : ∀ w : rationalArithmeticGaloisGroup a,
      ψ (AlgEquiv.restrictNormalHom F w) = ρ w)
    (hunr : Chebotarev.UnramifiedIn ℚ F (Ideal.span {(p : 𝓞 ℚ)}))
    (δ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp))
    (hδ : δ ∈ rationalPrimeNormInertia p hp) :
    ρ (rationalPrimeArithmeticRestriction a p hp δ) = 1 := by
  have hfinite := rationalArithmetic_finite_factor_inertia_eq_one a p hp F hunr δ hδ
  exact (hψ (rationalPrimeArithmeticRestriction a p hp δ)).symm.trans
    ((congrArg ψ hfinite).trans (map_one ψ))

end
end Dubon2026
