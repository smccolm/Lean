import Dubon2026.AdelicRaisingRotation
import Dubon2026.FiniteOrbitOfEigenSpan

/-! # Genuine compact finiteness of the original raising module -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The literal compact orbit span in the original adelic Hilbert space. -/
def adelicCompactOrbitSpan (v : AdelicCyclicHilbert f) : Submodule ℂ (AdelicCyclicHilbert f) :=
  Submodule.span ℂ (Set.range (fun g : realCompactSubgroup =>
    adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding g.val) v))

/-- Every genuine compact stabilizer element acts by a scalar on each original raising line. -/
theorem adelicRaisingJet_compact_scalar (hf : f ≠ 0) (g : realCompactSubgroup) (n : ℕ) :
    ∃ a : ℂ, adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding g.val)
      (adelicRaisingJet f n).val = a • (adelicRaisingJet f n).val := by
  obtain ⟨t, ht⟩ := realCompactSubgroup_eq_rotation g
  refine ⟨Complex.exp ((t : ℂ) * (Complex.I * ((k : ℂ) + 2 * n))), ?_⟩
  rw [ht]
  exact adelicRaisingJet_rotation f hf n t

/-- Every actual vector in the original Hilbert raising span is K-finite for the full genuine compact stabilizer. -/
theorem adelicRaisingSpan_compact_finite (hf : f ≠ 0) (v : AdelicCyclicHilbert f)
    (hv : v ∈ Submodule.span ℂ (Set.range (fun n : ℕ => (adelicRaisingJet f n).val))) :
    FiniteDimensional ℂ (adelicCompactOrbitSpan f v) :=
  @finiteOrbitSpan_of_eigen_span realCompactSubgroup ℂ (AdelicCyclicHilbert f) ℕ
    inferInstance inferInstance inferInstance inferInstance
    ((adelicCyclicHilbertRepresentation f).comp (adelicRealSL2Embedding.comp realCompactSubgroup.subtype))
    (fun n => (adelicRaisingJet f n).val) (adelicRaisingJet_compact_scalar f hf) v hv

end
end Dubon2026
