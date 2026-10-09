import Dubon2026.MatrixCongruenceKernelPGroup
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Algebra.CharP.Defs

/-! # The actual residual matrix kernel over an original Artinian local coefficient ring -/

namespace Dubon2026

open Matrix

variable {A ι : Type*} [CommRing A] [IsLocalRing A] [IsArtinianRing A]
  [Fintype ι] [DecidableEq ι]

/-- The literal residual kernel of the original Artinian local coefficient matrix group is a p-group for its genuine residue characteristic. -/
theorem artinianResidualMatrixKernel_isPGroup (p : ℕ) (hp : p.Prime)
    [CharP (IsLocalRing.ResidueField A) p] :
    IsPGroup p ((GeneralLinearGroup.map (n := ι) (R := A)
      (S := IsLocalRing.ResidueField A) (IsLocalRing.residue A)).ker) := by
  have hpI : (p : A) ∈ IsLocalRing.maximalIdeal A := by
    apply (IsLocalRing.residue_eq_zero_iff _).mp
    rw [map_natCast, CharP.cast_eq_zero]
  obtain ⟨N, hN⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal A).mp inferInstance
  exact matrixCongruenceKernel_isPGroup (ι := ι) (IsLocalRing.maximalIdeal A) hp hpI hN

end Dubon2026
