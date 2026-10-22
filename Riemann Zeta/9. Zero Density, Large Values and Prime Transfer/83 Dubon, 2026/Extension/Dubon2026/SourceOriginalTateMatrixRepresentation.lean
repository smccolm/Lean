import Dubon2026.SourceOriginalTatePadicContinuity
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Topology.Algebra.Group.Units

/-! DUB-17/18 -> actual modular Galois realization -> a genuine continuous
p-adic matrix representation on the original Tate module. Native units lift
the already constructed group action; the inverse coordinate is the action
of the inverse Galois element. The proved rank supplies a basis of size 2g.
This does not yet split off the rank-two Hecke eigensystem or identify Frobenius.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open scoped Matrix
variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
local notation "Qbar" => AlgebraicClosure ℚ
local notation "T" => TateModule p (originalJZero N)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual original Tate action expressed as invertible p-adic matrices. -/
def originalTateMatrixRep (b : Module.Basis ι ℤ_[p] T) :
    (Qbar ≃ₐ[ℚ] Qbar) →* Matrix.GeneralLinearGroup ι ℤ_[p] :=
  (((LinearMap.toMatrixAlgEquiv b).toRingHom.toMonoidHom).comp
    (originalTateGaloisRep N p)).toHomUnits

theorem originalTateMatrixRep_val (b : Module.Basis ι ℤ_[p] T) (σ : Qbar ≃ₐ[ℚ] Qbar) :
    (originalTateMatrixRep N p b σ).val = LinearMap.toMatrix b b (originalTateGaloisRep N p σ) := rfl

theorem originalTateMatrixRep_continuous (b : Module.Basis ι ℤ_[p] T) :
    Continuous (originalTateMatrixRep N p b) := by
  apply Units.continuous_iff.mpr
  constructor
  · exact originalTateGaloisRep_matrix_continuous N p b
  · have h := (originalTateGaloisRep_matrix_continuous N p b).comp continuous_inv
    convert h using 1

theorem exists_original_tate_matrix_realization :
    ∃ b : Module.Basis (Fin (2 * originalGenus N ℂ)) ℤ_[p] T,
      Continuous (originalTateMatrixRep N p b) ∧
      ∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (x : T),
        (originalTateMatrixRep N p b σ).val *ᵥ (b.repr x) =
          b.repr (originalTateGaloisRep N p σ x) := by
  obtain ⟨hfree, hfinite, hrank⟩ := OriginalChart.original_tate_free_finite_rank N p
  letI : Module.Free ℤ_[p] T := hfree
  letI : Module.Finite ℤ_[p] T := hfinite
  let b := (Module.finBasis ℤ_[p] T).reindex (finCongr hrank)
  refine ⟨b, originalTateMatrixRep_continuous N p b, ?_⟩
  intro σ x
  rw [originalTateMatrixRep_val]
  exact LinearMap.toMatrix_mulVec_repr b b (originalTateGaloisRep N p σ) x

end
end Dubon2026.SourceFunctionField
