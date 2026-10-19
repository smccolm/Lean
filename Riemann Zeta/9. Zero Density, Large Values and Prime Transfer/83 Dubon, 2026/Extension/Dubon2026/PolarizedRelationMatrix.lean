import Dubon2026.PolarizedRepresentationFromEquations

/-! The literal coefficient relations for the source polarized target.
The vanishing criterion is proved from the actual block equations; it
will define the quotient of the reusable framed ring in DUB-17. -/

namespace Dubon2026
open Matrix

variable {R A ι : Type*} [CommRing R] [CommRing A] [Fintype ι] [DecidableEq ι]

/-- The source component matrices commute with original coefficient change. -/
theorem polarizedComponentBlockRepresentation_map (f : R →+* A)
    (z : Multiplicative (ZMod 2)) :
    GeneralLinearGroup.map f (polarizedComponentBlockRepresentation (ι := ι) z) =
      polarizedComponentBlockRepresentation z := by
  change GeneralLinearGroup.map f (if z.toAdd = 0 then 1 else polarizedBlockSwap) =
    (if z.toAdd = 0 then 1 else polarizedBlockSwap)
  split_ifs
  · exact map_one _
  · exact polarizedBlockSwap_map f

/-- Removing the original component is compatible with coefficient reduction. -/
theorem polarizedComponentNormalization_map (f : R →+* A)
    (M : GeneralLinearGroup (ι ⊕ ι) R) (z : Multiplicative (ZMod 2)) :
    GeneralLinearGroup.map f (polarizedComponentNormalization M z) =
      polarizedComponentNormalization (GeneralLinearGroup.map f M) z := by
  unfold polarizedComponentNormalization
  rw [map_mul, map_inv, polarizedComponentBlockRepresentation_map]

/-- The three exact polarized relations packaged as entries of one original matrix. -/
def polarizedRelationMatrix (M : GeneralLinearGroup (ι ⊕ ι) R)
    (z : Multiplicative (ZMod 2)) (u : Rˣ) : Matrix (ι ⊕ ι) (ι ⊕ ι) R :=
  let N := (polarizedComponentNormalization M z).val
  fromBlocks
    (N.toBlocks₁₁.transpose * N.toBlocks₂₂ -
      Matrix.scalar ι (↑(u * (polarizedComponentSign (R := R) z)⁻¹) : R))
    N.toBlocks₁₂ N.toBlocks₂₁ 0

/-- Vanishing of the literal relation matrix is exactly the source target condition. -/
theorem polarizedRelationMatrix_eq_zero_iff
    (M : GeneralLinearGroup (ι ⊕ ι) R) (z : Multiplicative (ZMod 2)) (u : Rˣ) :
    polarizedRelationMatrix M z u = 0 ↔
      ∃ x : PolarizedGaloisGroup ι R, polarizedComponent x = z ∧
        polarizedSimilitude x = u ∧ polarizedBlockRepresentation x = M := by
  rw [polarizedBlockRepresentation_image_iff]
  constructor
  · intro h
    have h11 := congrArg Matrix.toBlocks₁₁ h
    have h12 := congrArg Matrix.toBlocks₁₂ h
    have h21 := congrArg Matrix.toBlocks₂₁ h
    exact ⟨h12, h21, sub_eq_zero.mp h11⟩
  · rintro ⟨h12, h21, hp⟩
    simp [polarizedRelationMatrix, h12, h21, hp]

end Dubon2026
