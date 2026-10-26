import Dubon2026.SourceRationalLocalValuation
import Dubon2026.RationalArithmeticGaloisGroup
import Dubon2026.EmbeddedNormalGaloisRestrictionContinuity

/-! DUB-17/18 -> arithmetic descent of the actual residual representation.
The absolute-to-arithmetic map is literal restriction in the chosen
algebraic closure, with its original Krull topology. -/
namespace Dubon2026
noncomputable section
open scoped NumberField
local notation "Qbar" => AlgebraicClosure ℚ
private local instance : IsGalois ℚ Qbar := sourceRationalAlgebraicClosure_isGalois

/-- Literal continuous restriction from the chosen absolute Galois group
to the prescribed original arithmetic extension. -/
def sourceAbsoluteArithmeticRestriction (a : 𝓞 ℚ) :
    Gal(Qbar/ℚ) →ₜ* rationalArithmeticGaloisGroup a := by
  let U := rationalUnramifiedExtension a
  letI : Algebra ℚ U := U.algebra'
  letI : IsGalois ℚ U := originalUnramifiedGaloisUnion_isGalois a
  exact ⟨AlgEquiv.restrictNormalHom U,
    InfiniteGalois.restrictNormalHom_continuous U⟩

theorem sourceAbsoluteArithmeticRestriction_commutes
    (a : 𝓞 ℚ) (g : Gal(Qbar/ℚ)) (x : rationalUnramifiedExtension a) :
    let U := rationalUnramifiedExtension a
    letI : Algebra ℚ U := U.algebra'
    ((show Gal(U/ℚ) from sourceAbsoluteArithmeticRestriction a g) x : Qbar) = g x := by
  exact g.restrictNormal_commutes (rationalUnramifiedExtension a) x

end
end Dubon2026
