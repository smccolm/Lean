import Dubon2026.CMHermitianTracePositive

/-! # Original Hermitian and invertibility properties from source positivity

Positivity at the original complex embeddings already implies that the
specified CM matrix is Hermitian and invertible. These properties need
not be additional assumptions in DUB-17's actual trace-lattice bounds.
-/

namespace Dubon2026

noncomputable section

open NumberField Matrix
open scoped ComplexOrder

variable (K : Type*) [Field K] [NumberField K] [IsCMField K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Source positivity at the original complex embeddings implies the original matrix is Hermitian. -/
theorem cmHermitianPositiveMatrix_isHermitian (H : Matrix ι ι K)
    (hH : ∀ φ : K →+* ℂ, (φ.mapMatrix H).PosDef) : H.IsHermitian := by
  let φ := Classical.arbitrary (K →+* ℂ)
  exact (Matrix.isHermitian_map_iff
    (IsCMField.complexEmbedding_complexConj K φ) φ.injective).mp (hH φ).isHermitian

omit [IsCMField K] in
/-- Source positivity at the original complex embeddings implies the original matrix is invertible. -/
theorem cmHermitianPositiveMatrix_isUnit (H : Matrix ι ι K)
    (hH : ∀ φ : K →+* ℂ, (φ.mapMatrix H).PosDef) : IsUnit H := by
  let φ := Classical.arbitrary (K →+* ℂ)
  apply (Matrix.isUnit_iff_isUnit_det H).mpr
  apply isUnit_iff_ne_zero.mpr
  intro hz
  have hn := isUnit_iff_ne_zero.mp
    ((Matrix.isUnit_iff_isUnit_det (φ.mapMatrix H)).mp (hH φ).isUnit)
  apply hn
  rw [← φ.map_det, hz, map_zero]

end
end Dubon2026
