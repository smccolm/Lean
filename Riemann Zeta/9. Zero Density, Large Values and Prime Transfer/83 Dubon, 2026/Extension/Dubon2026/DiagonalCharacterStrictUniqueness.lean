import Dubon2026.RegularResidueStrictIntertwiner
import Dubon2026.MatrixRepresentationStrictConjugacy
import Mathlib.LinearAlgebra.Matrix.Diagonal

/-! Injectivity of the actual character parameters modulo the existing
strict-conjugacy relation. This is the uniqueness half of the auxiliary
deformation classification serving Dubon Theorem 2.6. -/

namespace Dubon2026
open Matrix IsLocalRing

/-- Two diagonal character families are strictly conjugate exactly when
they are equal, in the original representation equivalence relation. -/
theorem diagonal_characters_strictlyConjugate_iff
    {G A ι : Type} [Group G] [CommRing A] [IsLocalRing A]
    [Fintype ι] [DecidableEq ι]
    (χ ψ : G →* (ι → A)ˣ) :
    MatrixStrictlyConjugate (residue A)
      ((Units.map (diagonalRingHom ι A).toMonoidHom).comp χ)
      ((Units.map (diagonalRingHom ι A).toMonoidHom).comp ψ) ↔ χ = ψ := by
  constructor
  · rintro ⟨U, hU, h⟩
    apply MonoidHom.ext
    intro g
    apply Units.ext
    have hg := congrArg (fun M : GeneralLinearGroup ι A => (M * U).val) (h g)
    simp only [mul_assoc, inv_mul_cancel, mul_one] at hg
    have hmul : diagonal (ψ g).val * U.val = U.val * diagonal (χ g).val := hg
    exact (regularResidue_diagonal_eq_of_strict_intertwiner _ _ U hU hmul).symm
  · rintro rfl
    exact matrixStrictlyConjugate_refl _ _

end Dubon2026
