import Dubon2026.AdelicPrimitiveQuadraticClassification
import Dubon2026.AdelicNonCMDirichletTwist

/-! # Actual non-CM cusp forms exclude all nontrivial continuous quadratic original idele-class self-twists -/

namespace Dubon2026

noncomputable section
open NumberField Matrix

/-- The original classical non-CM condition excludes an injective intertwiner into the actual determinant twist by every nontrivial continuous quadratic character of the original rational idele class group. -/
theorem nonCM_no_adelicQuadraticSelfTwist {N : ℕ} [NeZero N] {k : ℤ}
    (F : NonCMPrimitiveCuspForm N k) (ψ : (AdeleRing ℤ ℚ)ˣ →* ℂ)
    (hc : Continuous ψ) (hq : ∀ a, ψ a ^ 2 = 1)
    (hp : ∀ q : ℚˣ, ψ (Units.map (algebraMap ℚ (AdeleRing ℤ ℚ)).toMonoidHom q) = 1)
    (hne : ψ ≠ 1)
    (T : Representation.IntertwiningMap (adelicCyclicHilbertRepresentation F.toCuspForm)
      (scalarTwistRepresentation (adelicCyclicHilbertRepresentation F.toCuspForm)
        (ψ.comp GeneralLinearGroup.det))) : ¬ Function.Injective T := by
  obtain ⟨D, χ, hχp, hχne, hχq, rfl⟩ :=
    adelicQuadraticCharacter_primitive_exists ψ hc hq hp hne
  exact nonCM_no_adelicDirichletSelfTwist F D χ hχp hχne hχq T

end
end Dubon2026
