import Dubon2026.AdelicSelfTwistQuadratic
import Dubon2026.AdelicNonCMQuadraticTwist

/-! # Original non-CM primitive forms exclude every nontrivial continuous idele-class determinant self-twist -/

namespace Dubon2026

noncomputable section
open NumberField Matrix

/-- The actual non-CM primitive adelic representation has no injective self-twist by any nontrivial continuous rational idele-class character. Quadraticity is derived from its actual central action, rather than assumed. -/
theorem nonCM_no_adelicSelfTwist {N : ℕ} [NeZero N] {k : ℤ}
    (F : NonCMPrimitiveCuspForm N k) (ψ : (AdeleRing ℤ ℚ)ˣ →* ℂ)
    (hc : Continuous ψ)
    (hp : ∀ q : ℚˣ, ψ (Units.map (algebraMap ℚ (AdeleRing ℤ ℚ)).toMonoidHom q) = 1)
    (hne : ψ ≠ 1)
    (T : Representation.IntertwiningMap (adelicCyclicHilbertRepresentation F.toCuspForm)
      (scalarTwistRepresentation (adelicCyclicHilbertRepresentation F.toCuspForm)
        (ψ.comp GeneralLinearGroup.det))) : ¬ Function.Injective T := by
  intro hT
  exact nonCM_no_adelicQuadraticSelfTwist F ψ hc
    (adelicSelfTwist_quadratic F.toPrimitiveCuspForm ψ T hT) hp hne T hT

end
end Dubon2026
