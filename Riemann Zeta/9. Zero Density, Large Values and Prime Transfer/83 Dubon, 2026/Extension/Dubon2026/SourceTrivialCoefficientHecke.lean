import Dubon2026.SourcePrimeCoefficientHeckeH1
import Dubon2026.SourceBinaryH1HeckeAlgebra

/-! Original full Hecke actions on native trivial-coefficient cohomology.
DUB-17/18 -> residual modular Galois association -> character-to-weight-two
reduction -> the actual trivial-coefficient eigensystem at the raised level.
The coefficient morphism is the genuine identity and the existing native
full finite correspondence supplies every operator.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup

variable (F : Type) [Field F] (Q : ℕ)

/-- The actual trivial coefficient action intertwines every original prime conjugation. -/
theorem sourceTrivialCoefficient_intertwine {ell : ℕ} [NeZero ell] (hell : ell.Prime)
    (u : heckeUpperSubgroup Q ell) :
    (LinearMap.id : Module.End F (Rep.trivial F (Gamma0 Q) F)).comp
        ((Rep.trivial F (Gamma0 Q) F).ρ (sourceHeckeConjugation hell u)) =
      ((Rep.trivial F (Gamma0 Q) F).ρ u.val).comp LinearMap.id := rfl

private local instance trivialCoefficientPrimeNeZero (ell : sourceBinaryHeckePrime Q) : NeZero ell.val :=
  ⟨ell.property.1.ne_zero⟩

/-- Every original good-prime Hecke correspondence on full native trivial-coefficient H1. -/
def sourceTrivialCoefficientHeckeOperators :
    sourceBinaryHeckePrime Q → Module.End F
      (groupCohomology.H1 (Rep.trivial F (Gamma0 Q) F)) :=
  fun ell => sourcePrimeHeckeH1 ell.property.1 (Rep.trivial F (Gamma0 Q) F) LinearMap.id
    (sourceTrivialCoefficient_intertwine F Q ell.property.1)

end
end Dubon2026
