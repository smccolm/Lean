import Dubon2026.SourceInducedDifferential
import Dubon2026.SourceSpecialLinearComplements
import Dubon2026.IntegralInducedFiniteFree

/-! Invariant complements for the actual differentiated source coefficient module.
The source all-algebra covariance supplies its actual Lie action, while
the proved denominator and numerator bounds supply finite dimension.
The actual trace-zero matrices supply semisimplicity. Weyl's theorem
therefore has no remaining Lie-action, finite-dimension or semisimplicity
certificate here. Recovery of group-stability remains necessary.
-/

namespace Dubon2026
noncomputable section

universe u
variable (K : Type u) [Field K] [CharZero K] (n : ℕ) (lam : Fin n → ℤ)

/-- The actual special-linear infinitesimal action on the original induced module. -/
def sourceInducedSpecialLinearLieHom :
    LieAlgebra.SpecialLinear.sl (Fin n) K →ₗ⁅K⁆
      Module.End K (generalLinearIntegralInducedSubmodule K n lam) :=
  (sourceInducedDifferentialLieHom K n lam).comp
    (LieAlgebra.SpecialLinear.sl (Fin n) K).incl

/-- The original source-induced functions carry their actual differentiated special-linear action. -/
instance sourceInducedSpecialLinearLieRingModule :
    LieRingModule (LieAlgebra.SpecialLinear.sl (Fin n) K)
      (generalLinearIntegralInducedSubmodule K n lam) :=
  LieRingModule.compLieHom _ (sourceInducedSpecialLinearLieHom K n lam)

/-- The differentiated source action is linear over the original coefficient field. -/
instance sourceInducedSpecialLinearLieModule :
    LieModule K (LieAlgebra.SpecialLinear.sl (Fin n) K)
      (generalLinearIntegralInducedSubmodule K n lam) :=
  LieModule.compLieHom _ (sourceInducedSpecialLinearLieHom K n lam)

/-- Every Lie submodule of the original source-induced coefficient module in positive rank has an invariant Lie complement. Its action, finite dimension and semisimple acting Lie algebra are all proved from the original source objects. -/
theorem sourceInducedSpecialLinear_exists_complement {m : ℕ} (weight : Fin (m + 1) → ℤ)
    (W : LieSubmodule K (LieAlgebra.SpecialLinear.sl (Fin (m + 1)) K)
      (generalLinearIntegralInducedSubmodule K (m + 1) weight)) :
    ∃ U : LieSubmodule K (LieAlgebra.SpecialLinear.sl (Fin (m + 1)) K)
      (generalLinearIntegralInducedSubmodule K (m + 1) weight), IsCompl W U :=
  sourceSpecialLinearModule_exists_complement K (m + 1) _ W

end
end Dubon2026
