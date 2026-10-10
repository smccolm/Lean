import Dubon2026.OriginalClosedTraceMatrixAlgebra
import Dubon2026.CoefficientMatrixAlgebraResidue
import Dubon2026.AdicMatrixIdempotentLifting

/-! # A genuine lifted matrix-unit idempotent inside the original closed trace matrix algebra -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι O R : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R]
  [Algebra O R] [WithIdeal R] [IsAdicComplete (WithIdeal.i : Ideal R) R]

/-- In the actual original representation matrix algebra over its actual closed trace coefficients, lift any original diagonal residual matrix unit to a genuine idempotent, deriving the seed from the original residual representation and the limit from actual completeness and closedness. -/
theorem originalTraceMatrixIdempotent_exists
    {L : Type} [Field L] [Algebra (IsLocalRing.ResidueField R) L] [IsAlgClosed L]
    (hR : (WithIdeal.i : Ideal R) = IsLocalRing.maximalIdeal R)
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : G →* GeneralLinearGroup ι R)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L)
        ((GeneralLinearGroup.map (IsLocalRing.residue R)).comp ρ)))] (i₀ : ι) :
    ∃ e : coefficientRepresentationMatrixAlgebra (closedMatrixTraceAlgebra (O := O) ρ) ρ,
      e ^ 2 = e ∧ (RingHom.mapMatrix (IsLocalRing.residue R)) e.val =
        Matrix.single i₀ i₀ 1 := by
  let S := closedMatrixTraceAlgebra (O := O) ρ
  let A := coefficientRepresentationMatrixAlgebra S ρ
  obtain ⟨X, hX⟩ := coefficientRepresentationMatrixAlgebra_residue_surjective
    (L := L) eR S ρ (Matrix.single i₀ i₀ 1)
  have hbar : (Matrix.single i₀ i₀ (1 : IsLocalRing.ResidueField R)) ^ 2 =
      Matrix.single i₀ i₀ 1 := by
    simp [pow_two, Matrix.single_mul_single_same]
  have herror : ∀ i j, (X.val ^ 2 - X.val) i j ∈ (WithIdeal.i : Ideal R) := by
    intro i j
    rw [hR]
    apply (IsLocalRing.residue_eq_zero_iff (R := R) _).mp
    have hz : (RingHom.mapMatrix (IsLocalRing.residue R)) (X.val ^ 2 - X.val) = 0 := by
      rw [map_sub, map_pow]
      change ((RingHom.mapMatrix (IsLocalRing.residue R)) X.val) ^ 2 -
        (RingHom.mapMatrix (IsLocalRing.residue R)) X.val = 0
      rw [show (RingHom.mapMatrix (IsLocalRing.residue R)) X.val =
        Matrix.single i₀ i₀ 1 from hX, hbar, sub_self]
    exact congrArg (fun Z : Matrix ι ι (IsLocalRing.ResidueField R) => Z i j) hz
  have hA : IsClosed (A : Set (Matrix ι ι R)) :=
    (originalClosedTraceMatrixAlgebra_finite_free_closed (L := L) hR eR ρ).2.2
  obtain ⟨E, hES, hE, hEX⟩ := adicMatrixIdempotent_exists_mem_closedSubalgebra A hA X.val X.property herror
  refine ⟨⟨E, hES⟩, Subtype.ext hE, ?_⟩
  have hsame : (RingHom.mapMatrix (IsLocalRing.residue R)) E =
      (RingHom.mapMatrix (IsLocalRing.residue R)) X.val := by
    ext i j
    apply sub_eq_zero.mp
    change IsLocalRing.residue R (E i j) - IsLocalRing.residue R (X.val i j) = 0
    rw [← map_sub]
    apply (IsLocalRing.residue_eq_zero_iff (R := R) _).mpr
    rw [← hR]
    exact hEX i j
  exact hsame.trans hX

end
end Dubon2026
