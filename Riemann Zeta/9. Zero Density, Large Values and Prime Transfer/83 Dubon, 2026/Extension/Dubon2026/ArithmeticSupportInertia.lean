import Dubon2026.ArithmeticSupportRestriction
import Dubon2026.RationalArithmeticOutsideInertia

/-! The actual restriction to the original support kills the original
norm inertia at each new auxiliary prime. Characters pulled back from
that support therefore satisfy the determinant-unramifiedness premise
of the universal auxiliary augmentation comparison, on the dependency
chain of Dubon Theorem 2.6. -/

namespace Dubon2026
noncomputable section
open scoped NumberField

attribute [local instance] rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric
attribute [local instance 1100] rationalPrimeOriginalNormedField

/-- The enlarged original arithmetic extension restricts its actual
local inertia to the identity on the original support. No compatibility
between separately chosen local embeddings is assumed. -/
theorem rationalArithmeticSupportRestriction_inertia_eq_one
    (a b : 𝓞 ℚ) (hab : a ∣ b) (p : ℕ) (hp : p.Prime)
    (hpa : ¬ (p : 𝓞 ℚ) ∣ a)
    (g : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp))
    (hg : g ∈ rationalPrimeNormInertia p hp) :
    rationalArithmeticSupportRestriction a b hab
      (rationalPrimeArithmeticRestriction b p hp g) = 1 := by
  let e := rationalPrimeArithmeticOriginalEmbedding b p hp
  let i := rationalArithmeticSupportInclusion a b hab
  apply rationalArithmetic_embedded_inertia_eq_one_of_away a p hp hpa
    (e.comp i.toRingHom) _ g hg
  intro x
  exact (congrArg e (rationalArithmeticSupportRestriction_commutes a b hab
    (rationalPrimeArithmeticRestriction b p hp g) x)).trans
    (rationalPrimeArithmeticRestriction_commutes b p hp g (i x))

/-- Every character on the original support is unramified at the new
primes after pullback along the constructed arithmetic restriction. -/
theorem rationalArithmeticSupportCharacter_inertia_eq_one
    {H : Type*} [Monoid H] (a b : 𝓞 ℚ) (hab : a ∣ b)
    (δ : rationalArithmeticGaloisGroup a →* H)
    (p : ℕ) (hp : p.Prime) (hpa : ¬ (p : 𝓞 ℚ) ∣ a)
    (g : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp))
    (hg : g ∈ rationalPrimeNormInertia p hp) :
    (δ.comp (rationalArithmeticSupportRestriction a b hab).toMonoidHom)
      (rationalPrimeArithmeticRestriction b p hp g) = 1 := by
  exact (congrArg δ (rationalArithmeticSupportRestriction_inertia_eq_one a b hab p hp hpa g hg)).trans
    δ.map_one

end
end Dubon2026
