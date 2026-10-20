import Dubon2026.CMHermitianUnitaryGroup
import Mathlib.RingTheory.Trace.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! # The rational trace form of the original CM Hermitian matrix

This retains the specified source Hermitian form and takes its actual
field trace to the rationals. It supplies the positive rational form
whose integral restrictions to the attached lattices are needed by
DUB-17's finite arithmetic double-coset argument. Integrality, the uniform
Gram determinant and compatible CM action classes remain to be proved.
-/

namespace Dubon2026

noncomputable section

open NumberField Matrix

variable (K : Type*) [Field K] [NumberField K] [IsCMField K]

/-- The original CM involution preserves the actual rational field trace. -/
theorem cmField_trace_star (x : K) : Algebra.trace ℚ K (star x) = Algebra.trace ℚ K x :=
  Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj K).restrictScalars ℚ) x

variable {ι : Type*} [Fintype ι]

/-- The rational bilinear form obtained by taking the actual trace of the specified Hermitian pairing. -/
def cmHermitianRationalTraceForm (H : Matrix ι ι K) : LinearMap.BilinForm ℚ (ι → K) :=
  LinearMap.mk₂ ℚ (fun x y => Algebra.trace ℚ K (dotProduct (star x) (H.mulVec y)))
    (by intros; simp only [star_add, add_dotProduct, map_add])
    (by intros; simp only [star_smul, star_trivial, smul_dotProduct, map_smul])
    (by intros; simp only [mulVec_add, dotProduct_add, map_add])
    (by intros; simp only [mulVec_smul, dotProduct_smul, map_smul])

/-- Taking the CM conjugate of the original Hermitian pairing exchanges its arguments. -/
theorem cmHermitianPairing_star (H : Matrix ι ι K) (hH : H.IsHermitian) (x y : ι → K) :
    star (dotProduct (star x) (H.mulVec y)) = dotProduct (star y) (H.mulVec x) := by
  rw [star_dotProduct, star_star, star_mulVec, hH.eq, ← dotProduct_mulVec]

/-- The actual rational trace form is symmetric when the source matrix is Hermitian. -/
theorem cmHermitianRationalTraceForm_isSymm (H : Matrix ι ι K) (hH : H.IsHermitian) :
    (cmHermitianRationalTraceForm K H).IsSymm := by
  apply LinearMap.BilinForm.isSymm_def.mpr
  intro x y
  change Algebra.trace ℚ K (dotProduct (star x) (H.mulVec y)) =
    Algebra.trace ℚ K (dotProduct (star y) (H.mulVec x))
  rw [← cmField_trace_star K (dotProduct (star x) (H.mulVec y)),
    cmHermitianPairing_star K H hH x y]

end
end Dubon2026
