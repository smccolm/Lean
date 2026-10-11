import Dubon2026.RationalArithmeticLocalRestriction
import Dubon2026.EmbeddedNormalGaloisRestrictionContinuity

/-! # The original continuous local-to-arithmetic Galois restriction -/

namespace Dubon2026
noncomputable section
open scoped NumberField

variable {F K : Type} [Field F] [Field K] [Algebra ℚ F]
  [Algebra F K] [Algebra ℚ K] [IsScalarTower ℚ F K] [IsAlgClosed K]
  [Algebra.IsAlgebraic F K]

/-- The actual constructed restriction to the original arithmetic Galois group
is continuous for its existing Krull topology. This consumes the genuine
embedding and the finite-subextension neighborhood comparison. -/
theorem rationalArithmeticLocalRestriction_continuous (a : 𝓞 ℚ) :
    Continuous (rationalArithmeticLocalRestriction (F := F) (K := K) a) := by
  let U := rationalUnramifiedExtension a
  letI : Algebra ℚ U := U.algebra'
  letI : IsGalois ℚ U := originalUnramifiedGaloisUnion_isGalois a
  exact embeddedNormalGaloisRestriction_continuous
    (F := F) (rationalArithmeticLocalEmbedding (K := K) a)

/-- Bundle the proved continuous original restriction, with its original
homomorphism and topology. It is not an independently chosen restriction map. -/
def rationalArithmeticLocalRestrictionContinuous (a : 𝓞 ℚ) :
    (K ≃ₐ[F] K) →ₜ* rationalArithmeticGaloisGroup a where
  toMonoidHom := rationalArithmeticLocalRestriction a
  continuous_toFun := rationalArithmeticLocalRestriction_continuous a

/-- The continuous restriction retains exactly the already constructed original
field-element action through the same actual rational embedding. -/
theorem rationalArithmeticLocalRestrictionContinuous_commutes
    (a : 𝓞 ℚ) (g : K ≃ₐ[F] K) (x : rationalUnramifiedExtension a) :
    let U := rationalUnramifiedExtension a
    letI : Algebra ℚ U := U.algebra'
    rationalArithmeticLocalEmbedding (K := K) a
        ((show U ≃ₐ[ℚ] U from rationalArithmeticLocalRestrictionContinuous a g) x) =
      g (rationalArithmeticLocalEmbedding (K := K) a x) := by
  exact rationalArithmeticLocalRestriction_commutes a g x

end
end Dubon2026
