import Dubon2026.SourceEllipticExceptionalCoordinates

/-! Actual j=1728 model and its quartic coordinate automorphism, needed
to discharge the quadratic-action assumption in the exceptional census.
The existing stabilizer point equivalence is used directly.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, the corresponding quartic
variable-change and exceptional fixed-subgroup source solutions. -/
namespace Dubon2026.SourceEllipticExceptional
open WeierstrassCurve WeierstrassCurve.Affine SourceEllipticVariableChange
open SourceEllipticStabilizer
noncomputable section
variable {L : Type*} [Field L]

/-- The actual short Weierstrass model with exceptional j-invariant 1728. -/
abbrev EA (A : L) : WeierstrassCurve L := ⟨0, 0, 0, A, 0⟩

theorem EA_Δ (A : L) : (EA A).Δ = -64 * A ^ 3 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]; ring

theorem isElliptic_EA (A : L) (hA : A ≠ 0) (h2 : (2 : L) ≠ 0) : (EA A).IsElliptic := by
  refine ⟨?_⟩
  rw [EA_Δ, isUnit_iff_ne_zero]
  have h64 : (64 : L) ≠ 0 := by
    rw [show (64 : L) = 2 ^ 6 by norm_num]
    exact pow_ne_zero _ h2
  exact mul_ne_zero (neg_ne_zero.mpr h64) (pow_ne_zero 3 hA)

theorem quartic_change_fixes
    {R : Type*} [CommRing R] (u : Rˣ) (hu : (u : R) ^ 2 = -1) (A : R) :
    (⟨u, 0, 0, 0⟩ : WeierstrassCurve.VariableChange R) • (⟨0, 0, 0, A, 0⟩ : WeierstrassCurve R) =
      ⟨0, 0, 0, A, 0⟩ := by
  have h1 : ((u⁻¹ : Rˣ) : R) * (u : R) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hu4 : (u : R) ^ 4 = 1 := by
    calc (u : R) ^ 4 = ((u : R) ^ 2) ^ 2 := by ring
      _ = 1 := by rw [hu]; ring
  have h4 : ((u⁻¹ : Rˣ) : R) ^ 4 = 1 := by
    calc ((u⁻¹ : Rˣ) : R) ^ 4 = ((u⁻¹ : Rˣ) : R) ^ 4 * (u : R) ^ 4 := by rw [hu4, mul_one]
      _ = (((u⁻¹ : Rˣ) : R) * (u : R)) ^ 4 := by ring
      _ = 1 := by rw [h1, one_pow]
  refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_ <;>
    simp only [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆]
  · ring
  · ring
  · ring
  · linear_combination A * h4
  · ring

theorem quartic_action_square [DecidableEq L] (A : L) (u : Lˣ) (hu : (u : L) ^ 2 = -1)
    (P : (EA A).toAffine.Point) :
    let σ := stabilizerPointEquiv (EA A) ⟨u, 0, 0, 0⟩ (quartic_change_fixes u hu A)
    σ (σ P) = -P := by
  dsimp only
  have hi2 : ((u⁻¹ : Lˣ) : L) ^ 2 = -1 := by
    rw [Units.val_inv_eq_inv_val, inv_pow, hu, inv_neg, inv_one]
  apply xy_injective
  rw [xy_stabilizerPointEquiv, xy_stabilizerPointEquiv, xy_neg]
  rcases xy P with _ | ⟨x, y⟩
  · rfl
  · simp only [Option.map_some, vcXInv, vcYInv, Affine.negY, sub_zero, zero_mul,
      Option.some.injEq, Prod.mk.injEq]
    constructor
    · linear_combination (((u⁻¹ : Lˣ) : L) ^ 2 * x - x) * hi2
    · linear_combination (((u⁻¹ : Lˣ) : L) ^ 4 * y - ((u⁻¹ : Lˣ) : L) ^ 2 * y + y) * hi2

theorem quartic_action_x [DecidableEq L] (A : L) (u : Lˣ) (hu : (u : L) ^ 2 = -1)
    (x y : L) (h : (EA A).toAffine.Nonsingular x y) :
    xco (stabilizerPointEquiv (EA A) ⟨u, 0, 0, 0⟩ (quartic_change_fixes u hu A)
      (Point.some x y h)) = some (-x) := by
  have hi2 : ((u⁻¹ : Lˣ) : L) ^ 2 = -1 := by
    rw [Units.val_inv_eq_inv_val, inv_pow, hu, inv_neg, inv_one]
  rw [xco_eq_map_xy, xy_stabilizerPointEquiv]
  simp only [xy, Option.map_some, vcXInv, sub_zero, hi2, Option.some.injEq]
  ring

end
end Dubon2026.SourceEllipticExceptional
