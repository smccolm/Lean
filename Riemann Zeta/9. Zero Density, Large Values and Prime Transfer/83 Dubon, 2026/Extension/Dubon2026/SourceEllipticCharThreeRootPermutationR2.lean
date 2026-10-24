import Dubon2026.SourceEllipticCharThreeStabilizerBound
import Dubon2026.SourceEllipticNegationVariableChange

/-! The literal action on the three roots of x^3=x controls the wild
characteristic-three inertia quotient in the DUB-17/18 good-reduction chain.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_exists_isGalois_ord_jqModC_dvd_six_of_char_three, AutHom.
The existing actual curve, stabilizer equations and negation are reused. -/
namespace Dubon2026.SourceEllipticExceptional
open WeierstrassCurve SourceEllipticStabilizer
noncomputable section

variable (K : Type*) [Field K]

/-- The actual three x-coordinates of the characteristic-three exceptional curve. -/
abbrev charThreeRoots : Type _ := {x : K // x ^ 3 = x}

instance charThreeRootsFintype [DecidableEq K] : Fintype (charThreeRoots K) :=
  Fintype.subtype ({0, 1, -1} : Finset K)
    (fun x => by simp [cube_eq_self_iff_three_values])

variable [CharP K 3]

theorem charThreeRoots_card : Nat.card (charThreeRoots K) = 3 := by
  classical
  have h01 : (0 : K) ≠ 1 := zero_ne_one
  have h0m : (0 : K) ≠ -1 := (neg_ne_zero.mpr (one_ne_zero (α := K))).symm
  have h1m : (1 : K) ≠ -1 := by
    intro h
    apply two_ne_zero_of_char_three (K := K)
    linear_combination h
  rw [Nat.card_eq_fintype_card,
    Fintype.card_of_subtype ({0, 1, -1} : Finset K)
      (fun x => by simp [cube_eq_self_iff_three_values]),
    Finset.card_insert_of_notMem (by simp [h01, h0m]),
    Finset.card_insert_of_notMem (by simp [h1m]), Finset.card_singleton]

theorem charThreeRoots_perm_card : Nat.card (Equiv.Perm (charThreeRoots K)) = 6 := by
  classical
  have h := charThreeRoots_card K
  rw [Nat.card_eq_fintype_card] at h
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, h]
  rfl

variable {K}

private theorem cube_sub {a b : K} : (a - b) ^ 3 = a ^ 3 - b ^ 3 := by
  linear_combination (-(a ^ 2 * b) + a * b ^ 2) * CharP.cast_eq_zero K 3

private theorem cube_add {a b : K} : (a + b) ^ 3 = a ^ 3 + b ^ 3 := by
  linear_combination (a ^ 2 * b + a * b ^ 2) * CharP.cast_eq_zero K 3

private theorem cube_affine {v r x : K} (hv : v ^ 4 = 1) (hr : r ^ 3 = r) (hx : x ^ 3 = x) :
    (v ^ 2 * (x - r)) ^ 3 = v ^ 2 * (x - r) := by
  rw [mul_pow, cube_sub, hx, hr]
  linear_combination (v ^ 2 * (x - r)) * hv

private theorem cube_affine' {u r x : K} (hu : u ^ 4 = 1) (hr : r ^ 3 = r) (hx : x ^ 3 = x) :
    (u ^ 2 * x + r) ^ 3 = u ^ 2 * x + r := by
  rw [cube_add, mul_pow, hx, hr]
  linear_combination (u ^ 2 * x) * hu

/-- The actual exceptional coordinate change permutes the three roots of x^3=x. -/
def charThreeRootPerm (γ : VariableChange K) (h : γ • EA (-1 : K) = EA (-1 : K)) : Equiv.Perm (charThreeRoots K) where
  toFun x := ⟨((γ.u⁻¹ : Kˣ) : K) ^ 2 * (x.1 - γ.r),
    cube_affine (by
      have hu := (char_three_stabilizer_coordinates h).2.2.1
      simpa only [Units.val_inv_eq_inv_val, inv_pow, inv_eq_one] using hu)
      (char_three_stabilizer_coordinates h).2.2.2 x.2⟩
  invFun x := ⟨((γ.u : Kˣ) : K) ^ 2 * x.1 + γ.r,
    cube_affine' (char_three_stabilizer_coordinates h).2.2.1
      (char_three_stabilizer_coordinates h).2.2.2 x.2⟩
  left_inv x := by
    apply Subtype.ext
    have hu : ((γ.u : Kˣ) : K) ≠ 0 := γ.u.ne_zero
    simp only [Units.val_inv_eq_inv_val]
    field_simp
    ring
  right_inv x := by
    apply Subtype.ext
    have hu : ((γ.u : Kˣ) : K) ≠ 0 := γ.u.ne_zero
    simp only [Units.val_inv_eq_inv_val]
    field_simp
    ring

theorem charThreeRootPerm_apply_val (γ : VariableChange K) (h : γ • EA (-1 : K) = EA (-1 : K)) (x : charThreeRoots K) :
    (charThreeRootPerm γ h x).1 = ((γ.u⁻¹ : Kˣ) : K) ^ 2 * (x.1 - γ.r) := rfl

variable (K) in

/-- The exceptional stabilizer acts on its actual three-root set. -/
def charThreeRootPermHom : MulAction.stabilizer (VariableChange K) (EA (-1 : K)) →* Equiv.Perm (charThreeRoots K) where
  toFun γ := charThreeRootPerm γ.1 γ.2
  map_one' := by
    ext x
    rw [charThreeRootPerm_apply_val]
    simp [VariableChange.one_def]
  map_mul' γ γ' := by
    ext x
    rw [Equiv.Perm.mul_apply, charThreeRootPerm_apply_val, charThreeRootPerm_apply_val, charThreeRootPerm_apply_val]
    have hu : ((γ.1.u : Kˣ) : K) ≠ 0 := γ.1.u.ne_zero
    have hu' : ((γ'.1.u : Kˣ) : K) ≠ 0 := γ'.1.u.ne_zero
    simp only [Subgroup.coe_mul, VariableChange.mul_def, mul_inv, Units.val_mul,
      Units.val_inv_eq_inv_val]
    field_simp
    ring

end
end Dubon2026.SourceEllipticExceptional
