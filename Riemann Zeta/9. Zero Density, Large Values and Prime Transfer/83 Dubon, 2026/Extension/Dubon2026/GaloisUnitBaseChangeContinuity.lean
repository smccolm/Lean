import Dubon2026.GaloisUnitBaseChange
import Dubon2026.EmbeddedNormalGaloisRestrictionContinuity

/-! # Continuity of actual Galois base change for original infinite extensions -/

namespace Dubon2026
noncomputable section

variable (K E L M : Type) [Field K] [Field E] [Field L] [Field M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M] [Normal K L]

/-- Literal Galois base change is continuous for the original Krull
topologies. The existing finite-basis neighborhood proof applies through
the original field embedding; no discrete Galois topology is substituted. -/
theorem galoisBaseChangeRestriction_continuous [Algebra.IsAlgebraic E M] :
    Continuous (galoisBaseChangeRestriction K E L M) := by
  let e : L →ₐ[K] M := IsScalarTower.toAlgHom K L M
  have heq : galoisBaseChangeRestriction K E L M =
      embeddedNormalGaloisRestriction (F := E) e :=
    embeddedNormalGaloisRestriction_unique e (galoisBaseChangeRestriction K E L M)
      (galoisBaseChangeRestriction_commutes K E L M)
  rw [heq]
  exact embeddedNormalGaloisRestriction_continuous e

end
end Dubon2026
