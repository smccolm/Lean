import Dubon2026.FiniteSymmetricAbsoluteIrreducible
import Dubon2026.FixedResidualAbsoluteIrreducibility
import Dubon2026.TraceZeroAdjointInvariants
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! Actual native deformation and invariant consumers of the proved
finite symmetric residual image. These discharge absolute-irreducibility
and trace-zero invariant premises on DUB-17's arithmetic lifting chain;
modular association, image containment and finite-image H1 remain open. -/

namespace Dubon2026
noncomputable section
open Matrix

/-- The existing fixed-residual quotient inherits proved absolute
irreducibility from the actual finite symmetric image, without an
independent irreducibility hypothesis on the original representation. -/
theorem fixedResidual_symmetricImage_absoluteIrreducible
    {O L : Type} [CommRing O] [IsLocalRing O]
    [Finite (IsLocalRing.ResidueField O)]
    [TopologicalSpace (IsLocalRing.ResidueField O)] [T2Space (IsLocalRing.ResidueField O)]
    [Field L] [Algebra (IsLocalRing.ResidueField O) L]
    (q n : ℕ) [Fact q.Prime] [CharP (IsLocalRing.ResidueField O) q]
    (hsize : 2 * n < Nat.card (IsLocalRing.ResidueField O) - 1) (hchar : n < q)
    (H : ProfiniteGrp.{0})
    (σ : H →* GeneralLinearGroup (Fin (n + 1)) (IsLocalRing.ResidueField O))
    (hσ : Continuous σ)
    (himage : ((homogeneousSymmetricGL (R := IsLocalRing.ResidueField O) n).comp
      Matrix.SpecialLinearGroup.toGL).range ≤ σ.range) :
    Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L)
        (fixedResidualOriginalRepresentation q H σ hσ).toMonoidHom)) := by
  letI : Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) σ)) :=
    finiteField_matrixRepresentation_absoluteIrreducible_of_symmetricSL2_image q n hsize hchar σ himage
  exact fixedResidualOriginalRepresentation_absoluteIrreducible q H σ hσ

/-- The original trace-zero adjoint invariant submodule actually vanishes
under the finite symmetric image and characteristic bounds. The proof
constructs scalar-extension irreducibility before invoking native Schur
descent and the exact original trace-zero invariant consumer. -/
theorem symmetricResidual_traceZeroAdjointInvariants_eq_bot
    {G K : Type} [Group G] [Field K] [Finite K]
    (q n : ℕ) [Fact q.Prime] [CharP K q]
    (hsize : 2 * n < Nat.card K - 1) (hchar : n + 1 < q)
    (ρ : G →* GeneralLinearGroup (Fin (n + 1)) K)
    (himage : ((homogeneousSymmetricGL (R := K) n).comp
      Matrix.SpecialLinearGroup.toGL).range ≤ ρ.range) :
    (matrixTraceZeroAdjointRepresentation ρ).invariants = ⊥ := by
  letI : Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := AlgebraicClosure K) ρ)) :=
    finiteField_matrixRepresentation_absoluteIrreducible_of_symmetricSL2_image q n hsize
      (by omega) ρ himage
  apply matrixTraceZeroAdjointInvariants_eq_bot (L := AlgebraicClosure K) _ ρ
  rw [Fintype.card_fin]
  intro hz
  exact (Nat.not_dvd_of_pos_of_lt (Nat.succ_pos n) hchar)
    ((CharP.cast_eq_zero_iff K q (n + 1)).mp hz)

end
end Dubon2026
