import Dubon2026.SourceLieCompleteReducibility
import Dubon2026.SourceSpecialLinearRadical

/-! Actual special-linear complements on the source irreducibility chain.
The semisimple-Lie-algebra premise of the adapted Weyl theorem is now
discharged for the original trace-zero matrix Lie algebra over every
characteristic-zero coefficient field, in every finite rank.
The original induced Lie action and recovery of group-stability remain
the exact next obligations before this proves source irreducibility.
-/

namespace Dubon2026
noncomputable section

variable (K : Type*) [Field K] [CharZero K] (n : ℕ)

/-- The actual original trace-zero matrix Lie algebra is semisimple in characteristic zero. -/
theorem sourceSpecialLinear_isSemisimple :
    LieAlgebra.IsSemisimple K (LieAlgebra.SpecialLinear.sl (Fin n) K) := inferInstance

/-- Every submodule of a finite-dimensional module over the actual original special-linear Lie algebra has an invariant complement; semisimplicity is proved from its original matrices. -/
theorem sourceSpecialLinearModule_exists_complement
    (M : Type*) [AddCommGroup M] [Module K M]
    [LieRingModule (LieAlgebra.SpecialLinear.sl (Fin n) K) M]
    [LieModule K (LieAlgebra.SpecialLinear.sl (Fin n) K) M] [Module.Finite K M]
    (W : LieSubmodule K (LieAlgebra.SpecialLinear.sl (Fin n) K) M) :
    ∃ U : LieSubmodule K (LieAlgebra.SpecialLinear.sl (Fin n) K) M, IsCompl W U := by
  letI := sourceSpecialLinear_isSemisimple K n
  exact sourceLieModule_exists_complement W

end
end Dubon2026
