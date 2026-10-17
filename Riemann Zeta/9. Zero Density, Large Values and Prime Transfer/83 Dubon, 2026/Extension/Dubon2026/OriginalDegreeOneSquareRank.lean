import Mathlib.FieldTheory.Finite.Basic

/-! # Degree preservation through the actual two degree-one realizations

This is the finite tower calculation used to realize DUB-17's Sylow
normalization field without changing its extension degree.
-/
namespace Dubon2026

/-- Degree-one realization of the lower and upper fields preserves the
degree between them, by the two original tower rank identities. -/
theorem originalDegreeOneSquare_finrank
    (K F L M : Type) [Field K] [Field F] [Field L] [Field M]
    [Algebra K F] [Algebra K L] [Algebra K M] [Algebra F M] [Algebra L M]
    [IsScalarTower K F M] [IsScalarTower K L M] [FiniteDimensional K M]
    (hKF : Module.finrank K F = 1) (hLM : Module.finrank L M = 1) :
    Module.finrank F M = Module.finrank K L := by
  have h₁ := Module.finrank_mul_finrank K F M
  have h₂ := Module.finrank_mul_finrank K L M
  rw [hKF, one_mul] at h₁
  rw [hLM, mul_one] at h₂
  exact h₁.trans h₂.symm

end Dubon2026
