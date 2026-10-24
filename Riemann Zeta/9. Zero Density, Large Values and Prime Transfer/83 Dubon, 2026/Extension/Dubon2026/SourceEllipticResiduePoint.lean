import Dubon2026.SourceEllipticResidueArithmetic

/-! Actual reduction of the original elliptic point coordinates. Adapted from
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, ReductionMap. The original monic
equation supplies integral y; good reduction supplies nonsingularity.
Additivity will be proved only on the required prime-to-residue torsion. -/

namespace Dubon2026.SourceEllipticReduction
open WeierstrassCurve IsLocalRing
variable {L : Type*} [Field L] {A : ValuationSubring L} (W : WeierstrassCurve A)

/-- Actual point reduction identity: map_residue_Δ_ne_zero_iff. -/
theorem map_residue_Δ_ne_zero_iff : (W.map (residue A)).Δ ≠ 0 ↔ IsUnit W.Δ := by
  rw [map_Δ]
  exact residue_ne_zero_iff_isUnit W.Δ

/-- Actual point reduction identity: equation_residue. -/
theorem equation_residue {x y : A}
    (h : (W.map A.subtype).toAffine.Equation (x : L) (y : L)) :
    (W.map (residue A)).toAffine.Equation (residue A x) (residue A y) := by
  have hA : W.toAffine.Equation x y := (W.toAffine.map_equation A.subtype_injective x y).mp h
  exact hA.map (residue A)

/-- Actual point reduction identity: nonsingular_residue. -/
theorem nonsingular_residue (hΔ : (W.map (residue A)).Δ ≠ 0) {x y : A}
    (h : (W.map A.subtype).toAffine.Equation (x : L) (y : L)) :
    (W.map (residue A)).toAffine.Nonsingular (residue A x) (residue A y) :=
  (Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp (equation_residue W h)

variable {W}

open Classical in

/-- Actual point reduction identity: reducePoint. -/
noncomputable def reducePoint (hΔ : (W.map (residue A)).Δ ≠ 0) :
    (W.map A.subtype).toAffine.Point → (W.map (residue A)).toAffine.Point
  | .zero => .zero
  | .some x y h =>
    if hx : x ∈ A then
      .some (residue A ⟨x, hx⟩) (residue A ⟨y, SourceEllipticFunctionField.equation_y_mem_valuationSubring A W h.1 hx⟩)
        (nonsingular_residue W hΔ h.1)
    else
      .zero

variable (hΔ : (W.map (residue A)).Δ ≠ 0)

/-- Actual point reduction identity: reducePoint_zero. -/
@[simp]
lemma reducePoint_zero : reducePoint hΔ (0 : (W.map A.subtype).toAffine.Point) = 0 :=
  rfl

/-- Actual point reduction identity: reducePoint_some_of_mem. -/
lemma reducePoint_some_of_mem {x y : L} (h : (W.map A.subtype).toAffine.Nonsingular x y)
    (hx : x ∈ A) :
    reducePoint hΔ (.some x y h) =
      .some (residue A ⟨x, hx⟩) (residue A ⟨y, SourceEllipticFunctionField.equation_y_mem_valuationSubring A W h.1 hx⟩)
        (nonsingular_residue W hΔ h.1) := by
  simp only [reducePoint]
  exact dif_pos hx

/-- Actual point reduction identity: reducePoint_some_of_notMem. -/
lemma reducePoint_some_of_notMem {x y : L} (h : (W.map A.subtype).toAffine.Nonsingular x y)
    (hx : x ∉ A) : reducePoint hΔ (.some x y h) = 0 := by
  simp only [reducePoint]
  exact dif_neg hx

end Dubon2026.SourceEllipticReduction
