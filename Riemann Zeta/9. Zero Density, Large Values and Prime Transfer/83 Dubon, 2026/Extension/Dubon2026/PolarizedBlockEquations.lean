import Dubon2026.PolarizedBlockNaturality
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! Exact polynomial equations for the identity component of the source
polarized target, with its original multiplier. These equations, rather
than an assumed polarized lift, are the intended quotient conditions on
the reusable framed matrix ring in DUB-17's CM deformation construction. -/

namespace Dubon2026
open Matrix

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- The source matrix and its multiplier-twisted dual satisfy the exact pairing equation. -/
theorem polarizedSwitch_pairing (g : GeneralLinearGroup ι R) (u : Rˣ) :
    g.val.transpose * (polarizedSwitch (g, u)).1.val = Matrix.scalar ι (u : R) := by
  change g.val.transpose * (Matrix.scalar ι (u : R) * g.inv.transpose) = _
  have hc := Matrix.scalar_commute (u : R) (Commute.all _) g.val.transpose
  rw [← mul_assoc, ← hc.eq, mul_assoc, ← transpose_mul, g.inv_val,
    transpose_one, mul_one]

/-- The pairing equation uniquely determines the original twisted-dual block. -/
theorem polarizedSwitch_eq_of_pairing (g : GeneralLinearGroup ι R) (u : Rˣ)
    (D : Matrix ι ι R) (h : g.val.transpose * D = Matrix.scalar ι (u : R)) :
    D = (polarizedSwitch (g, u)).1.val := by
  calc
    D = (g.inv.transpose * g.val.transpose) * D := by
      rw [← transpose_mul, g.val_inv, transpose_one, one_mul]
    _ = g.inv.transpose * (g.val.transpose * D) := mul_assoc _ _ _
    _ = g.inv.transpose * Matrix.scalar ι (u : R) := by rw [h]
    _ = Matrix.scalar ι (u : R) * g.inv.transpose :=
      (Matrix.scalar_commute (u : R) (Commute.all _) g.inv.transpose).eq.symm
    _ = (polarizedSwitch (g, u)).1.val := rfl

/-- The source identity-component image is exactly the original block and pairing equations.
Invertibility of its first block is derived using Mathlib's block-triangular criterion. -/
theorem polarizedIdentityBlockRepresentation_image_iff
    (M : GeneralLinearGroup (ι ⊕ ι) R) (u : Rˣ) :
    (∃ g : GeneralLinearGroup ι R, polarizedIdentityBlockRepresentation (g, u) = M) ↔
      M.val.toBlocks₁₂ = 0 ∧ M.val.toBlocks₂₁ = 0 ∧
        M.val.toBlocks₁₁.transpose * M.val.toBlocks₂₂ = Matrix.scalar ι (u : R) := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨rfl, rfl, polarizedSwitch_pairing g u⟩
  · rintro ⟨h12, h21, hp⟩
    have he : fromBlocks M.val.toBlocks₁₁ 0 0 M.val.toBlocks₂₂ = M.val := by
      simpa only [h12, h21] using fromBlocks_toBlocks M.val
    have hi : IsUnit (fromBlocks M.val.toBlocks₁₁ 0 0 M.val.toBlocks₂₂) := by
      rw [he]
      exact M.isUnit
    obtain ⟨g, hg⟩ := (isUnit_fromBlocks_zero₂₁.mp hi).1
    have hd : M.val.toBlocks₂₂ = (polarizedSwitch (g, u)).1.val := by
      apply polarizedSwitch_eq_of_pairing
      simpa only [hg] using hp
    refine ⟨g, ?_⟩
    apply Units.ext
    change fromBlocks g.val 0 0 (polarizedSwitch (g, u)).1.val = M.val
    rw [← hd, hg]
    exact he

end Dubon2026
