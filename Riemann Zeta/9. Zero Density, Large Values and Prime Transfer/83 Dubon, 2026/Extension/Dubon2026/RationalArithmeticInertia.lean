import Dubon2026.RationalArithmeticGaloisGroup
import Dubon2026.UnramifiedUnionInfiniteInertia
import Dubon2026.IntegralInertiaClosed

/-! # Original inertia inside the actual rational arithmetic Galois group -/

namespace Dubon2026

noncomputable section
open scoped NumberField

/-- The actual inertia subgroup of the original integer-ring ideal, in the original rational arithmetic Galois group. -/
def rationalArithmeticInertia (a : 𝓞 ℚ)
    (P : Ideal (𝓞 (rationalUnramifiedExtension a))) :
    Subgroup (rationalArithmeticGaloisGroup a) := by
  let U := rationalUnramifiedExtension a
  letI : Algebra ℚ U := U.algebra'
  exact P.inertia Gal(U/ℚ)

/-- The original rational arithmetic inertia subgroup is closed in the actual arithmetic group's Krull topology. -/
theorem rationalArithmeticInertia_isClosed (a : 𝓞 ℚ)
    (P : Ideal (𝓞 (rationalUnramifiedExtension a))) :
    IsClosed (rationalArithmeticInertia a P : Set (rationalArithmeticGaloisGroup a)) := by
  let U := rationalUnramifiedExtension a
  letI : Algebra ℚ U := U.algebra'
  letI : IsGalois ℚ U := originalUnramifiedGaloisUnion_isGalois a
  exact integral_inertia_isClosed (K := ℚ) P

/-- Every actual nonzero prime outside the original exceptional integer has trivial inertia in the same rational arithmetic group used by the deformation constructions. The original rational scalar structure is explicit. -/
theorem rationalArithmeticInertia_eq_bot (a : 𝓞 ℚ) (ha : a ≠ 0) :
    (let U := rationalUnramifiedExtension a
     letI : Algebra ℚ U := U.algebra'
     ∀ (P : Ideal (𝓞 U)), P.IsPrime → P ≠ ⊥ →
       algebraMap (𝓞 ℚ) (𝓞 U) a ∉ P → rationalArithmeticInertia a P = ⊥) := by
  dsimp only
  intro P hprime hP haP
  letI := hprime
  exact originalUnramifiedUnion_inertia_eq_bot a ha P hP haP

end
end Dubon2026
