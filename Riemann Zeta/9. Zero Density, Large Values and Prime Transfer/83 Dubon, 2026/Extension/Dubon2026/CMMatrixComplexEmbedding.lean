import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.LinearAlgebra.UnitaryGroup

/-! # Compatibility of the original CM matrix involution with complex embeddings

This supplies the arithmetic-to-archimedean bridge for DUB-17's definite
Hermitian unitary stabilizers, using the native CM conjugation theorem.
-/

namespace Dubon2026

noncomputable section

open NumberField

variable {K ι : Type*} [Field K] [NumberField K] [IsCMField K]
variable [Fintype ι] [DecidableEq ι]

/-- A complex embedding of the CM field preserves the actual matrix involution. -/
def cmMatrixComplexEmbedding (φ : K →+* ℂ) : Matrix ι ι K →⋆* Matrix ι ι ℂ where
  __ := φ.mapMatrix.toMonoidHom
  map_star' M := by
    ext i j
    exact IsCMField.complexEmbedding_complexConj K φ (M j i)

end
end Dubon2026
