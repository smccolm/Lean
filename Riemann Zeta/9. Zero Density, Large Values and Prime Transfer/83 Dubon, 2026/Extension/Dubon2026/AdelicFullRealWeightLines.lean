import Dubon2026.AdelicFullRealHilbertBasis

/-! # Exact one-dimensional rotation eigenlines in the original full real Hilbert factor -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The actual integer-character eigenspace inside the original full real factor at the fixed separating irrational angle. -/
def adelicFullRealRotationEigenspace (m : ℤ) : Submodule ℂ (AdelicCyclicHilbert f) :=
  (adelicFullRealUnitCore f).topologicalClosure ⊓
    Module.End.eigenspace (adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (realRotationCurve (Real.pi * Real.sqrt 2)))) (integerIrrationalCharacter m)

/-- An actual full-real eigenvector of a signed raising weight lies on precisely the corresponding original raising line. -/
theorem adelicFullRealRotationEigenspace_scalar (hf : f ≠ 0) (hk : 0 < k)
    (i : ℕ ⊕ ℕ) (x : AdelicCyclicHilbert f)
    (hx : x ∈ adelicFullRealRotationEigenspace f (adelicSignedRaisingWeight k i)) :
    ∃ c : ℂ, x = c • adelicSignedRaisingJet f i := by
  apply @closureSpan_eq_smul_of_inner (AdelicCyclicHilbert f) (ℕ ⊕ ℕ) inferInstance inferInstance
    (adelicSignedRaisingJet f) (adelicSignedRaisingJet_orthogonal f hf hk)
    i (adelicSignedRaisingJet_ne_zero f hf hk i) x
  · change x ∈ adelicSignedRaisingClosedSpan f
    rw [adelicSignedRaisingClosedSpan_eq_fullRealClosure f hf]
    exact hx.1
  · intro j hji
    exact @unitary_distinct_eigen_inner_zero (AdelicCyclicHilbert f) inferInstance inferInstance
      (adelicCyclicHilbertRepresentation f
        (adelicRealSL2Embedding (realRotationCurve (Real.pi * Real.sqrt 2))))
      (adelicCyclicHilbertRepresentation_inner f _) _ _ _ _
      (integerIrrationalCharacter_norm _)
      (integerIrrationalCharacter_injective.ne ((adelicSignedRaisingWeight_injective k hk).ne hji))
      (adelicSignedRaisingJet_rotation f hf j) ((Module.End.mem_eigenspace_iff).mp hx.2)

/-- The exact original full-real signed-weight eigenspace equals its actual original raising line. -/
theorem adelicFullRealRotationEigenspace_eq_line (hf : f ≠ 0) (hk : 0 < k) (i : ℕ ⊕ ℕ) :
    adelicFullRealRotationEigenspace f (adelicSignedRaisingWeight k i) =
      Submodule.span ℂ {adelicSignedRaisingJet f i} := by
  apply le_antisymm
  · intro x hx
    obtain ⟨c, rfl⟩ := adelicFullRealRotationEigenspace_scalar f hf hk i x hx
    exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton _))
  · apply Submodule.span_le.mpr
    rintro x (rfl : x = _)
    constructor
    · rw [← adelicSignedRaisingClosedSpan_eq_fullRealClosure f hf]
      exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i, rfl⟩)
    · exact (Module.End.mem_eigenspace_iff).mpr (adelicSignedRaisingJet_rotation f hf i)

/-- Every integer rotation weight outside the genuine signed spectrum has zero space in the actual full real factor. -/
theorem adelicFullRealRotationEigenspace_eq_bot (hf : f ≠ 0) (m : ℤ)
    (hm : ∀ i, adelicSignedRaisingWeight k i ≠ m) :
    adelicFullRealRotationEigenspace f m = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  apply @closureSpan_eq_zero_of_inner (AdelicCyclicHilbert f) (ℕ ⊕ ℕ) inferInstance inferInstance
    (adelicSignedRaisingJet f) x
  · change x ∈ adelicSignedRaisingClosedSpan f
    rw [adelicSignedRaisingClosedSpan_eq_fullRealClosure f hf]
    exact hx.1
  · intro i
    exact @unitary_distinct_eigen_inner_zero (AdelicCyclicHilbert f) inferInstance inferInstance
      (adelicCyclicHilbertRepresentation f
        (adelicRealSL2Embedding (realRotationCurve (Real.pi * Real.sqrt 2))))
      (adelicCyclicHilbertRepresentation_inner f _) _ _ _ _
      (integerIrrationalCharacter_norm _) (integerIrrationalCharacter_injective.ne (hm i))
      (adelicSignedRaisingJet_rotation f hf i) ((Module.End.mem_eigenspace_iff).mp hx.2)

/-- Each genuine integer rotation eigenspace in the original full real Hilbert factor is finite-dimensional. -/
theorem adelicFullRealRotationEigenspace_finiteDimensional (hf : f ≠ 0) (hk : 0 < k) (m : ℤ) :
    FiniteDimensional ℂ (adelicFullRealRotationEigenspace f m) := by
  by_cases hm : ∃ i, adelicSignedRaisingWeight k i = m
  · obtain ⟨i, rfl⟩ := hm
    rw [adelicFullRealRotationEigenspace_eq_line f hf hk i]
    infer_instance
  · rw [adelicFullRealRotationEigenspace_eq_bot f hf m (fun i hi => hm ⟨i, hi⟩)]
    infer_instance

end
end Dubon2026
