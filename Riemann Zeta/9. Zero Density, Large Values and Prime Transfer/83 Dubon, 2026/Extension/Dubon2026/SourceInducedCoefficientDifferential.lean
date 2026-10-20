import Dubon2026.SourceCoefficientDifferential
import Dubon2026.SourceInducedDifferential

/-! The original induced differential under coefficient change.
This retains the actual induced-module elements in the previously proved
regular-function compatibility, for the source generic-fibre image.
-/

namespace Dubon2026
noncomputable section

universe u
variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
variable (n : ℕ) (lam : Fin n → ℤ)

/-- Coefficient change intertwines the actual integral induced differential with the original changed-coefficient differential. -/
theorem sourceInducedCoefficientMap_differential
    (X : Matrix (Fin n) (Fin n) R) (p : generalLinearIntegralInducedSubmodule R n lam) :
    sourceInducedCoefficientMap R B n lam (sourceInducedDifferential R n lam X p) =
      sourceInducedDifferential B n lam (X.map (algebraMap R B))
        (sourceInducedCoefficientMap R B n lam p) :=
  Subtype.ext (sourceRegularCoefficientMap_differential R B X p.val)

end
end Dubon2026
