import Dubon2026.ParabolicResidueAmbientQuotient
import Dubon2026.CompactLocalMatrixCongruenceTopology
import Mathlib.Topology.Algebra.OpenSubgroup

/-! # Openness of the source residue parabolic levels

The existing principal congruence kernel is contained in the source U1.
Its openness therefore proves openness of both source levels. This is
the topological input for their pullbacks to the actual unitary group
on DUB-17's integral auxiliary module chain.
-/

namespace Dubon2026
noncomputable section
open IsLocalRing Matrix

variable (R : Type*) [CommRing R] [IsLocalRing R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every original principal congruence matrix satisfies the exact source U1 row condition. -/
theorem matrixCongruenceKernel_le_parabolicResidueLevelOne (a : ι) :
    MatrixCongruenceKernel (ι := ι) (maximalIdeal R) ≤ parabolicResidueLevelOneAmbient R a := by
  intro M hM
  rw [parabolicResidueLevelOneAmbient_mem_iff]
  have he (i j : ι) := congrArg (fun u : (Matrix ι ι (ResidueField R))ˣ => u.val i j) hM
  constructor
  · intro j hj
    have h := he a j
    change residue R (M.val a j) = (1 : Matrix ι ι (ResidueField R)) a j at h
    simpa only [Matrix.one_apply_ne (Ne.symm hj)] using h
  · have h := he a a
    change residue R (M.val a a) = (1 : Matrix ι ι (ResidueField R)) a a at h
    simpa only [Matrix.one_apply_eq] using h

variable [IsNoetherianRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable [CompactSpace R] [T2Space R]

/-- The original source lower parabolic level is open in the original local matrix group. -/
theorem parabolicResidueLevelOneAmbient_isOpen (a : ι) :
    IsOpen (parabolicResidueLevelOneAmbient R a : Set (Matrix ι ι R)ˣ) :=
  Subgroup.isOpen_mono (matrixCongruenceKernel_le_parabolicResidueLevelOne R a)
    (compactLocalMatrixCongruenceKernel_isOpen R ι)

/-- The original source upper parabolic level is open in the original local matrix group. -/
theorem parabolicResidueLevelZero_isOpen (a : ι) :
    IsOpen (parabolicResidueLevelZero R a : Set (Matrix ι ι R)ˣ) :=
  Subgroup.isOpen_mono (parabolicResidueLevelOneAmbient_le R a)
    (parabolicResidueLevelOneAmbient_isOpen R a)

end
end Dubon2026
