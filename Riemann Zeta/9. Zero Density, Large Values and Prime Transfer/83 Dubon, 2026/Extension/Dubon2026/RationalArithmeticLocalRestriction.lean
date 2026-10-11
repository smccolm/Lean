import Dubon2026.RationalArithmeticGaloisGroup
import Dubon2026.EmbeddedNormalGaloisRestriction

/-! # An actual restriction to the constructed rational arithmetic Galois group

Choose an algebra embedding of the original rational unramified extension into
the algebraically closed local overfield. This constructs a restriction map with
its exact field-element action. Continuity and place identification are separate.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField

variable {F K : Type} [Field F] [Field K] [Algebra ℚ F]
  [Algebra F K] [Algebra ℚ K] [IsScalarTower ℚ F K] [IsAlgClosed K]

/-- A genuine rational embedding of the existing arithmetic extension into the
original algebraically closed overfield. Its existence follows from the actual
algebraicity of that extension, rather than an assumed restriction map. -/
def rationalArithmeticLocalEmbedding (a : 𝓞 ℚ) :
    let U := rationalUnramifiedExtension a
    letI : Algebra ℚ U := U.algebra'
    U →ₐ[ℚ] K := by
  let U := rationalUnramifiedExtension a
  letI : Algebra ℚ U := U.algebra'
  letI : IsGalois ℚ U := originalUnramifiedGaloisUnion_isGalois a
  exact IsAlgClosed.lift

/-- Restrict actual local-field automorphisms to the original rational arithmetic
Galois group through the constructed original embedding. The map is constructed
using the normality of the existing unramified extension. -/
def rationalArithmeticLocalRestriction (a : 𝓞 ℚ) :
    (K ≃ₐ[F] K) →* rationalArithmeticGaloisGroup a := by
  let U := rationalUnramifiedExtension a
  letI : Algebra ℚ U := U.algebra'
  letI : IsGalois ℚ U := originalUnramifiedGaloisUnion_isGalois a
  change (K ≃ₐ[F] K) →* (U ≃ₐ[ℚ] U)
  exact embeddedNormalGaloisRestriction (rationalArithmeticLocalEmbedding (K := K) a)

/-- The constructed arithmetic restriction acts on every element of the actual
unramified extension by the original local automorphism through the same chosen
embedding. This is the field-level identification, not a continuity assertion. -/
theorem rationalArithmeticLocalRestriction_commutes
    (a : 𝓞 ℚ) (g : K ≃ₐ[F] K) (x : rationalUnramifiedExtension a) :
    let U := rationalUnramifiedExtension a
    letI : Algebra ℚ U := U.algebra'
    rationalArithmeticLocalEmbedding (K := K) a
        ((show U ≃ₐ[ℚ] U from rationalArithmeticLocalRestriction a g) x) =
      g (rationalArithmeticLocalEmbedding (K := K) a x) := by
  let U := rationalUnramifiedExtension a
  letI : Algebra ℚ U := U.algebra'
  letI : IsGalois ℚ U := originalUnramifiedGaloisUnion_isGalois a
  exact embeddedNormalGaloisRestriction_commutes
    (rationalArithmeticLocalEmbedding (K := K) a) g x

end
end Dubon2026
