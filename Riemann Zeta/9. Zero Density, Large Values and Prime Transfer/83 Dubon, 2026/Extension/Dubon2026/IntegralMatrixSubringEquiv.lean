import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Ring.Equiv

/-! # Original integral matrix coefficients

This identifies the native matrix subring with matrices over that same
subring. It is the coefficient bridge needed to apply native unit and
residue maps to the actual integral finite-adelic level in DUB-17.
-/

namespace Dubon2026

noncomputable section

/-- The original matrix subring is the matrix ring over the same coefficient subring. -/
def integralMatrixSubringEquiv {R ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι]
    (S : Subring R) : S.matrix (n := ι) ≃+* Matrix ι ι S where
  toFun M i j := ⟨M.val i j, M.property i j⟩
  invFun M := ⟨fun i j => (M i j).val, fun i j => (M i j).property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' M N := by
    apply Matrix.ext
    intro i j
    apply Subtype.ext
    change (∑ k, M.val i k * N.val k j) =
      S.subtype (∑ k, (⟨M.val i k, M.property i k⟩ : S) * ⟨N.val k j, N.property k j⟩)
    rw [map_sum]
    rfl

end
end Dubon2026
