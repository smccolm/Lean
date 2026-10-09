import Dubon2026.AdelicSignedWeightAdmissible
import Dubon2026.AdelicMissingIntegerWeight

/-! # Finite-dimensional fixed vectors at every original integer rotation character and every open finite adelic subgroup -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- Every actual integer rotation character has finite-dimensional fixed vectors under any original open finite adelic subgroup. -/
theorem adelicIntegerWeight_finiteDimensional (hf : f ≠ 0) (hk : 0 < k) (m : ℤ)
    (J : Subgroup (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)))
    (hJ : IsOpen (J : Set (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)))) :
    FiniteDimensional ℂ (adelicIntegerRotationWeightSpace f m ⊓ adelicFiniteSubgroupFixedSpace f J :
      Submodule ℂ (AdelicCyclicHilbert f)) := by
  by_cases hm : ∃ i, adelicSignedRaisingWeight k i = m
  · obtain ⟨i, rfl⟩ := hm
    exact adelicSignedWeight_finiteDimensional f hf hk i J hJ
  · rw [adelicIntegerRotationWeightSpace_eq_bot f hf m (fun i hi => hm ⟨i, hi.symm⟩), bot_inf_eq]
    infer_instance

end
end Dubon2026
