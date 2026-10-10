import Dubon2026.MatrixRepresentationBurnside
import Dubon2026.MatrixAdjointScalarDescent
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Descent of original representation matrix spanning along a coefficient field extension -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι K L : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [Field K] [Field L] [Algebra K L]

/-- If the actual extended column representation is irreducible over an algebraically closed field, every original matrix is a finite linear combination over the original field of the same original representation matrices. -/
theorem matrixRepresentation_exists_sum_of_extension [IsAlgClosed L]
    (ρ : G →* GeneralLinearGroup ι K)
    [Representation.IsIrreducible (matrixStandardRepresentation (matrixCoefficientExtension (L := L) ρ))]
    (X : Matrix ι ι K) :
    ∃ s : Finset G, ∃ a : G → K, X = ∑ g ∈ s, a g • (ρ g).val := by
  classical
  obtain ⟨π, hπ⟩ := (Algebra.linearMap K L).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap K L).injective)
  have hπ' (x : K) : π (algebraMap K L x) = x :=
    congrArg (fun f : K →ₗ[K] K => f x) hπ
  have hs (c : L) (x : K) : π (c * algebraMap K L x) = π c * x := by
    rw [mul_comm, ← Algebra.smul_def, π.map_smul, smul_eq_mul, mul_comm]
  obtain ⟨c, hc⟩ := irreducibleMatrixRepresentation_exists_sum
    (matrixCoefficientExtension (L := L) ρ) (X.map (algebraMap K L))
  refine ⟨c.support, fun g => π (c g), ?_⟩
  ext i j
  have h := congrArg (fun Y : Matrix ι ι L => π (Y i j)) hc
  simp only [Matrix.map_apply, Finsupp.sum, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, map_sum] at h
  change π (algebraMap K L (X i j)) =
    ∑ g ∈ c.support, π (c g * algebraMap K L ((ρ g).val i j)) at h
  simpa only [hπ', hs, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using h

/-- Absolute irreducibility of the actual extended column representation makes the original representation matrices span the full matrix algebra over the original coefficient field. -/
theorem matrixRepresentation_span_eq_top_of_extension [IsAlgClosed L]
    (ρ : G →* GeneralLinearGroup ι K)
    [Representation.IsIrreducible (matrixStandardRepresentation (matrixCoefficientExtension (L := L) ρ))] :
    Submodule.span K (Set.range (fun g => (ρ g).val)) = ⊤ := by
  apply top_unique
  intro X _
  obtain ⟨s, a, h⟩ := matrixRepresentation_exists_sum_of_extension (L := L) ρ X
  rw [h]
  apply Submodule.sum_mem
  intro g _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)

end
end Dubon2026
