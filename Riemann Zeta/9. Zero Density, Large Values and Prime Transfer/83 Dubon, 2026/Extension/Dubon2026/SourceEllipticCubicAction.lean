import Dubon2026.SourceEllipticCubicAddition

/-! DUB-17/18 -> reverse genus -> exceptional j=0 census.
The actual cubic coordinate automorphism and the native addition law
discharge its quadratic action identity. Reuse the existing stabilizer
point equivalence and optional-coordinate identities.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, the corresponding cubic
variable-change, addition and exceptional fixed-subgroup source solutions. -/
namespace Dubon2026.SourceEllipticExceptional
open WeierstrassCurve WeierstrassCurve.Affine SourceEllipticVariableChange
open SourceEllipticStabilizer Polynomial
noncomputable section
variable {L : Type*} [Field L]

variable [DecidableEq L]

theorem cubic_action_some (B : L) (u : Lˣ) (hu : (u : L) ^ 3 = 1)
    (x y : L) (h : (EB B).toAffine.Nonsingular x y) :
    ∃ h', stabilizerPointEquiv (EB B) ⟨u, 0, 0, 0⟩ (cubic_change_fixes u hu B)
      (Point.some x y h) = Point.some ((u : L) * x) y h' := by
  have hi3 : ((u⁻¹ : Lˣ) : L) ^ 3 = 1 := by
    rw [Units.val_inv_eq_inv_val, inv_pow, hu, inv_one]
  have hi2 : ((u⁻¹ : Lˣ) : L) ^ 2 = u := by
    rw [Units.val_inv_eq_inv_val, inv_pow]
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_succ, hu])
  apply exists_eq_some_of_xy_eq
  rw [xy_stabilizerPointEquiv]
  simp only [xy, Option.map_some, vcXInv, vcYInv, sub_zero, zero_mul, hi2, hi3, one_mul]

theorem cubic_action_x (B : L) (u : Lˣ) (hu : (u : L) ^ 3 = 1)
    (x y : L) (h : (EB B).toAffine.Nonsingular x y) :
    xco (stabilizerPointEquiv (EB B) ⟨u, 0, 0, 0⟩ (cubic_change_fixes u hu B)
      (Point.some x y h)) = some ((u : L) * x) := by
  obtain ⟨h', he⟩ := cubic_action_some B u hu x y h
  rw [he, xco_some]

theorem cubic_action_relation (B : L) (hB : B ≠ 0)
    (u : Lˣ) (hu : (u : L) ^ 3 = 1) (hu1 : (u : L) ≠ 1)
    (h2 : (2 : L) ≠ 0) (P : (EB B).toAffine.Point) :
    let σ := stabilizerPointEquiv (EB B) ⟨u, 0, 0, 0⟩ (cubic_change_fixes u hu B)
    σ (σ P) + σ P + P = 0 := by
  let σ := stabilizerPointEquiv (EB B) ⟨u, 0, 0, 0⟩ (cubic_change_fixes u hu B)
  change σ (σ P) + σ P + P = 0
  have σ_some := cubic_action_some B u hu
  rcases P with _ | ⟨x, y, h⟩
  · simp only [← WeierstrassCurve.Affine.Point.zero_def, map_zero, add_zero]
  · obtain ⟨h1, e1⟩ := σ_some x y h
    obtain ⟨h2', e2⟩ := σ_some ((u : L) * x) y h1
    rw [e1, e2]
    by_cases hx : x = 0
    · subst hx
      have hy0 : y ≠ 0 := by
        have heq := h.left
        rw [WeierstrassCurve.Affine.equation_iff] at heq
        simp only [zero_mul, mul_zero, add_zero] at heq
        rintro rfl
        apply hB
        simpa using heq.symm
      have e0 : ∀ (h' : (EB B).toAffine.Nonsingular ((u : L) * 0) y),
          Point.some ((u : L) * 0) y h' = Point.some 0 y h := by
        intro h'; apply xy_injective; simp [xy]
      have e00 : ∀ (h' : (EB B).toAffine.Nonsingular ((u : L) * ((u : L) * 0)) y),
          Point.some ((u : L) * ((u : L) * 0)) y h' = Point.some 0 y h := by
        intro h'; apply xy_injective; simp [xy]
      rw [e0, e00, cubic_some_zero_add_self B h2 hy0 h,
        neg_add_cancel]
    · have hw2x : (EB B).toAffine.Nonsingular ((u : L) ^ 2 * x) y := by
        have : (u : L) ^ 2 * x = (u : L) * ((u : L) * x) := by ring
        rw [this]; exact h2'
      have e3 : Point.some ((u : L) * ((u : L) * x)) y h2' = Point.some ((u : L) ^ 2 * x) y hw2x := by
        apply xy_injective; simp only [xy, Option.some.injEq, Prod.mk.injEq, and_true]; ring
      rw [e3, add_assoc, add_comm (Point.some ((u : L) * x) y h1),
        cubic_some_add_some B (u : L) hu hu1 h h1 hw2x hx,
        add_neg_cancel]


end
end Dubon2026.SourceEllipticExceptional
