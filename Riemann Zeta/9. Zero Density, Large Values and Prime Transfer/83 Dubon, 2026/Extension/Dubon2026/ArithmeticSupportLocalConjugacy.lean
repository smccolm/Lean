import Dubon2026.ArithmeticSupportRestriction
import Dubon2026.NormalEmbeddingRestrictionConjugacy
import Dubon2026.RationalPrimeArithmeticRestriction

/-! The original auxiliary-support restriction and the original
base-support local restriction agree up to a constructed global
conjugacy. This removes an embedding-choice compatibility assumption
from the Dubon Theorem 2.6 auxiliary local deformation route. -/

namespace Dubon2026
noncomputable section
open scoped NumberField

/-- Separately chosen actual local embeddings give conjugate arithmetic
restriction maps, with one global conjugator for the whole local group. -/
theorem rationalArithmeticSupportRestriction_local_conjugacy
    (a b : 𝓞 ℚ) (hab : a ∣ b) (p : ℕ) (hp : p.Prime) :
    ∃ u : rationalArithmeticGaloisGroup a,
      ∀ g : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp),
        rationalArithmeticSupportRestriction a b hab (rationalPrimeArithmeticRestriction b p hp g) =
          u⁻¹ * rationalPrimeArithmeticRestriction a p hp g * u := by
  let E := rationalUnramifiedExtension a
  let K := rationalUnramifiedExtension b
  letI : Algebra ℚ E := E.algebra'
  letI : Algebra ℚ K := K.algebra'
  letI : IsGalois ℚ E := originalUnramifiedGaloisUnion_isGalois a
  let e := rationalArithmeticLocalEmbedding (K := rationalPrimeLocalClosure p hp) a
  let eb := rationalArithmeticLocalEmbedding (K := rationalPrimeLocalClosure p hp) b
  let i := rationalArithmeticSupportInclusion a b hab
  let f := eb.comp i
  obtain ⟨u, hu⟩ := embeddedNormalGaloisRestriction_exists_conjugacy
    (F := rationalPrimeLocalField p hp) e f
  refine ⟨u, ?_⟩
  intro g
  have hr : embeddedNormalGaloisRestriction f g =
      (show Gal(E/ℚ) from rationalArithmeticSupportRestriction a b hab
        (rationalPrimeArithmeticRestriction b p hp g)) := by
    apply AlgEquiv.ext
    intro x
    apply f.injective
    change f (embeddedNormalGaloisRestriction f g x) =
      f ((show Gal(E/ℚ) from rationalArithmeticSupportRestriction a b hab
        (rationalPrimeArithmeticRestriction b p hp g)) x)
    rw [embeddedNormalGaloisRestriction_commutes]
    change g (eb (i x)) = eb (i
      ((show Gal(E/ℚ) from rationalArithmeticSupportRestriction a b hab
        (rationalPrimeArithmeticRestriction b p hp g)) x))
    exact ((congrArg eb (rationalArithmeticSupportRestriction_commutes a b hab
      (rationalPrimeArithmeticRestriction b p hp g) x)).trans
      (rationalPrimeArithmeticRestriction_commutes b p hp g (i x))).symm
  exact hr.symm.trans (hu g)

end
end Dubon2026
