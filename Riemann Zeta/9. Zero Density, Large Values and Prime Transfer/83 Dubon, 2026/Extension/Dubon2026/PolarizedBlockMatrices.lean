import Dubon2026.PolarizedCoefficientMap
import Mathlib.Data.Matrix.Block

/-! The block matrices used to realize the source polarized target inside
GL_(2n). This realization allows the existing all-relation framed-ring
construction to be reused, with the polarized block equations imposed, in
the CM deformation branch of DUB-17. No deformation representability or
arithmetic representation is asserted by these matrix identities. -/

namespace Dubon2026
open Matrix

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- The actual invertible block diagonal matrix. -/
def polarizedBlockDiagonal (g h : GeneralLinearGroup ι R) :
    GeneralLinearGroup (ι ⊕ ι) R where
  val := fromBlocks g.val 0 0 h.val
  inv := fromBlocks g.inv 0 0 h.inv
  val_inv := by simp only [fromBlocks_multiply, mul_zero, zero_mul, add_zero,
    zero_add, g.val_inv, h.val_inv, fromBlocks_one]
  inv_val := by simp only [fromBlocks_multiply, mul_zero, zero_mul, add_zero,
    zero_add, g.inv_val, h.inv_val, fromBlocks_one]

/-- Block diagonal formation preserves the original matrix products. -/
theorem polarizedBlockDiagonal_mul (g h g' h' : GeneralLinearGroup ι R) :
    polarizedBlockDiagonal (g * g') (h * h') =
      polarizedBlockDiagonal g h * polarizedBlockDiagonal g' h' := by
  apply Units.ext
  change fromBlocks (g.val * g'.val) 0 0 (h.val * h'.val) =
    fromBlocks g.val 0 0 h.val * fromBlocks g'.val 0 0 h'.val
  simp only [fromBlocks_multiply, mul_zero, zero_mul, add_zero, zero_add]

/-- The original block diagonal identity is the identity matrix. -/
theorem polarizedBlockDiagonal_one :
    polarizedBlockDiagonal (1 : GeneralLinearGroup ι R) 1 = 1 := by
  apply Units.ext
  exact fromBlocks_one

/-- The matrix interchanging the two original coordinate blocks. -/
def polarizedBlockSwap : GeneralLinearGroup (ι ⊕ ι) R where
  val := fromBlocks 0 1 1 0
  inv := fromBlocks 0 1 1 0
  val_inv := by simp only [fromBlocks_multiply, zero_mul, mul_zero,
    one_mul, zero_add, add_zero, fromBlocks_one]
  inv_val := by simp only [fromBlocks_multiply, zero_mul, mul_zero,
    one_mul, zero_add, add_zero, fromBlocks_one]

/-- Block exchange has square one over the original coefficient ring. -/
theorem polarizedBlockSwap_sq :
    (polarizedBlockSwap (R := R) (ι := ι)) ^ 2 = 1 := by
  rw [pow_two]
  apply Units.ext
  exact (polarizedBlockSwap (R := R) (ι := ι)).val_inv

/-- Conjugation by the actual exchange matrix interchanges the diagonal blocks. -/
theorem polarizedBlockSwap_conjugate (g h : GeneralLinearGroup ι R) :
    polarizedBlockSwap * polarizedBlockDiagonal g h * polarizedBlockSwap⁻¹ =
      polarizedBlockDiagonal h g := by
  apply Units.ext
  change fromBlocks 0 1 1 0 * fromBlocks g.val 0 0 h.val * fromBlocks 0 1 1 0 =
    fromBlocks h.val 0 0 g.val
  simp only [fromBlocks_multiply, zero_mul, mul_zero, one_mul, mul_one,
    zero_add, add_zero]

/-- The source identity component acts on a space and its multiplier-twisted dual. -/
def polarizedIdentityBlockRepresentation :
    GeneralLinearGroup ι R × Rˣ →* GeneralLinearGroup (ι ⊕ ι) R where
  toFun x := polarizedBlockDiagonal x.1 (polarizedSwitch x).1
  map_one' := by
    change polarizedBlockDiagonal 1 (polarizedSwitchAut (1 : GeneralLinearGroup ι R × Rˣ)).1 = 1
    rw [map_one]
    exact polarizedBlockDiagonal_one
  map_mul' x y := by
    rw [polarizedSwitch_mul]
    exact polarizedBlockDiagonal_mul _ _ _ _

/-- The source switching involution is implemented by exchange of these blocks. -/
theorem polarizedIdentityBlockRepresentation_switch (x : GeneralLinearGroup ι R × Rˣ) :
    polarizedIdentityBlockRepresentation (polarizedSwitch x) =
      polarizedBlockSwap * polarizedIdentityBlockRepresentation x * polarizedBlockSwap⁻¹ := by
  change polarizedBlockDiagonal (polarizedSwitch x).1 (polarizedSwitch (polarizedSwitch x)).1 = _
  rw [polarizedSwitch_involutive]
  exact (polarizedBlockSwap_conjugate x.1 (polarizedSwitch x).1).symm

end Dubon2026
