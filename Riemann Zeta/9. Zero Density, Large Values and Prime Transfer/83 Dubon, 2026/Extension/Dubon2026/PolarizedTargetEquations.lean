import Dubon2026.PolarizedBlockEquations

/-! Exact coefficient-ring equations for both components and a fixed source
similitude. They are the defining quotient relations needed to specialize
the existing framed matrix construction to the actual polarized target in
DUB-17's CM deformation problem. -/

namespace Dubon2026
open Matrix

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- Remove the specified component matrix from the original doubled matrix. -/
def polarizedComponentNormalization (M : GeneralLinearGroup (ι ⊕ ι) R)
    (z : Multiplicative (ZMod 2)) : GeneralLinearGroup (ι ⊕ ι) R :=
  M * (polarizedComponentBlockRepresentation z)⁻¹

/-- Normalization of an actual source point recovers its original identity component. -/
theorem polarizedComponentNormalization_block (x : PolarizedGaloisGroup ι R) :
    polarizedComponentNormalization (polarizedBlockRepresentation x) (polarizedComponent x) =
      polarizedIdentityBlockRepresentation x.left := by
  change (polarizedIdentityBlockRepresentation x.left *
    polarizedComponentBlockRepresentation x.right) *
      (polarizedComponentBlockRepresentation x.right)⁻¹ = _
  exact mul_inv_cancel_right _ _

/-- The exact polarized target with specified component and similitude is cut out by
block vanishing and the original twisted-dual pairing equation. -/
theorem polarizedBlockRepresentation_image_iff
    (M : GeneralLinearGroup (ι ⊕ ι) R) (z : Multiplicative (ZMod 2)) (u : Rˣ) :
    (∃ x : PolarizedGaloisGroup ι R, polarizedComponent x = z ∧
      polarizedSimilitude x = u ∧ polarizedBlockRepresentation x = M) ↔
      (polarizedComponentNormalization M z).val.toBlocks₁₂ = 0 ∧
      (polarizedComponentNormalization M z).val.toBlocks₂₁ = 0 ∧
      (polarizedComponentNormalization M z).val.toBlocks₁₁.transpose *
        (polarizedComponentNormalization M z).val.toBlocks₂₂ =
          Matrix.scalar ι (↑(u * (polarizedComponentSign (R := R) z)⁻¹) : R) := by
  rw [← polarizedIdentityBlockRepresentation_image_iff]
  constructor
  · rintro ⟨x, hz, hu, rfl⟩
    have hmu : x.left.2 = u * (polarizedComponentSign (R := R) z)⁻¹ := by
      apply eq_mul_inv_iff_mul_eq.mpr
      change x.left.2 * polarizedComponentSign x.right = u at hu
      change x.right = z at hz
      rwa [hz] at hu
    refine ⟨x.left.1, ?_⟩
    rw [← hmu, ← hz, polarizedComponentNormalization_block]
  · rintro ⟨g, hg⟩
    let x : PolarizedGaloisGroup ι R := ⟨(g, u * (polarizedComponentSign (R := R) z)⁻¹), z⟩
    refine ⟨x, rfl, ?_, ?_⟩
    · change (u * (polarizedComponentSign (R := R) z)⁻¹) * polarizedComponentSign (R := R) z = u
      exact inv_mul_cancel_right _ _
    · change polarizedIdentityBlockRepresentation (g, u * (polarizedComponentSign (R := R) z)⁻¹) *
        polarizedComponentBlockRepresentation z = M
      exact eq_mul_inv_iff_mul_eq.mp hg

end Dubon2026
