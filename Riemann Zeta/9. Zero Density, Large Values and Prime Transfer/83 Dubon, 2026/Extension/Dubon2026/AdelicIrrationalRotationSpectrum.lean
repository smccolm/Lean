import Dubon2026.AdelicSignedFiniteFamilyDensity
import Dubon2026.DenseEigenfamilyEigenspace
import Dubon2026.AdelicIntegerWeightAdmissible

/-! # Exact spectrum of the separating original rotation on the full adelic Hilbert space -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup IsDedekindDomain CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The original full adelic action of the fixed irrational real rotation. -/
def adelicIrrationalRotation : Module.End ℂ (AdelicCyclicHilbert f) :=
  adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding (realRotationCurve (Real.pi * Real.sqrt 2)))

/-- On the full original adelic Hilbert space, a matching separating-rotation eigenspace is the exact all-angle integer-character space. -/
theorem adelicIrrationalRotation_eigenspace (hf : f ≠ 0) (i : ℕ ⊕ ℕ) :
    Module.End.eigenspace (adelicIrrationalRotation f) (integerIrrationalCharacter (adelicSignedRaisingWeight k i)) =
      adelicIntegerRotationWeightSpace f (adelicSignedRaisingWeight k i) := by
  refine @eigenspace_eq_of_dense_eigenfamily (AdelicCyclicHilbert f)
    ((ℕ ⊕ ℕ) × GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) inferInstance inferInstance
    (adelicIrrationalRotation f) (adelicCyclicHilbertRepresentation_inner f _)
    (adelicSignedFiniteFamily f) (fun q => integerIrrationalCharacter (adelicSignedRaisingWeight k q.1))
    (fun q => integerIrrationalCharacter_norm _) ?_ (adelicSignedFiniteFamily_dense f hf)
    _ _ inferInstance ?_ ?_
  · intro q
    exact (mem_adelicIntegerRotationWeightSpace f _ _).mp
      (adelicSignedFiniteFamily_mem_weight f hf q) (Real.pi * Real.sqrt 2)
  · intro x hx
    exact Module.End.mem_eigenspace_iff.mpr
      ((mem_adelicIntegerRotationWeightSpace f _ x).mp hx (Real.pi * Real.sqrt 2))
  · intro q hq
    have he := integerIrrationalCharacter_injective hq
    exact he ▸ adelicSignedFiniteFamily_mem_weight f hf q

/-- There are no additional eigenvalues of the original separating rotation in the full original adelic Hilbert space. -/
theorem adelicIrrationalRotation_eigenspace_eq_bot (hf : f ≠ 0) (c : ℂ)
    (hc : ∀ i, integerIrrationalCharacter (adelicSignedRaisingWeight k i) ≠ c) :
    Module.End.eigenspace (adelicIrrationalRotation f) c = ⊥ := by
  refine @eigenspace_eq_of_dense_eigenfamily (AdelicCyclicHilbert f)
    ((ℕ ⊕ ℕ) × GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) inferInstance inferInstance
    (adelicIrrationalRotation f) (adelicCyclicHilbertRepresentation_inner f _)
    (adelicSignedFiniteFamily f) (fun q => integerIrrationalCharacter (adelicSignedRaisingWeight k q.1))
    (fun q => integerIrrationalCharacter_norm _) ?_ (adelicSignedFiniteFamily_dense f hf)
    _ _ inferInstance ?_ ?_
  · intro q
    exact (mem_adelicIntegerRotationWeightSpace f _ _).mp
      (adelicSignedFiniteFamily_mem_weight f hf q) (Real.pi * Real.sqrt 2)
  · exact bot_le
  · intro q hq
    exact (hc q.1 hq).elim

/-- Every complex eigenspace of the original separating rotation has finite-dimensional fixed part under every open finite adelic subgroup. -/
theorem adelicIrrationalRotation_fixed_eigenspace_finiteDimensional (hf : f ≠ 0) (hk : 0 < k)
    (J : Subgroup (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)))
    (hJ : IsOpen (J : Set (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)))) (c : ℂ) :
    FiniteDimensional ℂ (Module.End.eigenspace (adelicIrrationalRotation f) c ⊓
      adelicFiniteSubgroupFixedSpace f J : Submodule ℂ (AdelicCyclicHilbert f)) := by
  by_cases hc : ∃ i, integerIrrationalCharacter (adelicSignedRaisingWeight k i) = c
  · obtain ⟨i, rfl⟩ := hc
    rw [adelicIrrationalRotation_eigenspace f hf i]
    exact adelicIntegerWeight_finiteDimensional f hf hk _ J hJ
  · rw [adelicIrrationalRotation_eigenspace_eq_bot f hf c (fun i hi => hc ⟨i, hi⟩), bot_inf_eq]
    infer_instance

end
end Dubon2026
