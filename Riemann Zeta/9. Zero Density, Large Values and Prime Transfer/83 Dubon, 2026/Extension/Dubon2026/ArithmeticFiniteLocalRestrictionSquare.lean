import Dubon2026.ArithmeticFiniteLocalStage
import Dubon2026.EmbeddedNormalGaloisRestriction

/-! # The exact arithmetic finite-stage restriction square

The finite local compositum uses the original arithmetic embedding. Its finite
restriction therefore factors the original global-to-local restriction, on
the same field elements. This is the comparison needed to transfer proved
local H2 vanishing to the original arithmetic H2 for DUB-17 finite support.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField

attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois arithmeticFiniteLocalStageRationalAlgebra

variable (a : 𝓞 ℚ) (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (p : ℕ) (hp : p.Prime)

/-- Restriction from the actual finite local compositum to the original finite
arithmetic field through the same original embedding. -/
def rationalArithmeticFiniteLocalRestriction :
    Gal(rationalArithmeticFiniteLocalStage a F p hp / rationalPrimeLocalField p hp) →*
      Gal(F/ℚ) :=
  embeddedNormalGaloisRestriction (rationalArithmeticFiniteLocalStageInclusion a F p hp)

/-- The original arithmetic restriction and the constructed local-stage
restriction give exactly the same automorphism of the original finite field. -/
theorem rationalArithmeticFiniteLocalRestriction_square :
    (AlgEquiv.restrictNormalHom F).comp (rationalPrimeArithmeticRestriction a p hp).toMonoidHom =
      (rationalArithmeticFiniteLocalRestriction a F p hp).comp
        (AlgEquiv.restrictNormalHom (rationalArithmeticFiniteLocalStage a F p hp) :
          Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) →*
            Gal(rationalArithmeticFiniteLocalStage a F p hp / rationalPrimeLocalField p hp)) := by
  apply MonoidHom.ext
  intro g
  apply AlgEquiv.ext
  intro x
  apply (rationalArithmeticFiniteLocalEmbedding a F p hp).injective
  change rationalArithmeticLocalEmbedding a
      (((rationalPrimeArithmeticRestriction a p hp g).restrictNormal F x : F) :
        rationalUnramifiedExtension a) = _
  have hg := (rationalPrimeArithmeticRestriction a p hp g).restrictNormal_commutes F x
  change (((rationalPrimeArithmeticRestriction a p hp g).restrictNormal F x : F) :
    rationalUnramifiedExtension a) =
      (show Gal(rationalUnramifiedExtension a / ℚ) from rationalPrimeArithmeticRestriction a p hp g) x at hg
  rw [hg, rationalPrimeArithmeticRestriction_commutes a p hp g x]
  have he := embeddedNormalGaloisRestriction_commutes
    (rationalArithmeticFiniteLocalStageInclusion a F p hp)
    (g.restrictNormal (rationalArithmeticFiniteLocalStage a F p hp)) x
  have hc := congrArg (fun z : rationalArithmeticFiniteLocalStage a F p hp =>
    (z : rationalPrimeLocalClosure p hp)) he
  exact ((g.restrictNormal_commutes (rationalArithmeticFiniteLocalStage a F p hp)
    (rationalArithmeticFiniteLocalStageInclusion a F p hp x)).symm.trans hc.symm)

end
end Dubon2026
