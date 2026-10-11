import Dubon2026.MatrixTwoDeterminantComplement

/-! # A genuine nonzero residual relation operator supplies a primitive invariant column -/

namespace Dubon2026
open Matrix

variable {G ι R K : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [Field K]

/-- The actual columns of an original operator annihilated by every matrix-minus-identity are invariant. If that operator is nonzero in the genuine residue, one column is primitive over the original local coefficients. -/
theorem matrix_exists_primitive_fixed_column (r : R →+* K) [IsLocalHom r]
    (A : G → Matrix ι ι R) (B : Matrix ι ι R) (hB : B.map r ≠ 0)
    (hrel : ∀ g, (A g - 1) * B = 0) :
    ∃ v : ι → R, (∃ i, IsUnit (v i)) ∧ ∀ g, A g *ᵥ v = v := by
  obtain ⟨i, j, hij⟩ := matrix_exists_unit_entry_of_residue r B hB
  refine ⟨fun k => B k j, ⟨i, hij⟩, ?_⟩
  intro g
  have hmul : A g * B = B := by
    simpa only [sub_mul, one_mul, sub_eq_zero] using hrel g
  funext k
  exact congrArg (fun C : Matrix ι ι R => C k j) hmul

end Dubon2026
