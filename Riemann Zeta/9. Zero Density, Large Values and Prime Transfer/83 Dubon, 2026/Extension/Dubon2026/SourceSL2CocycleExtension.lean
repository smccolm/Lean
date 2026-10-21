import Dubon2026.SourceSL2CocycleMatrices
import Dubon2026.RepresentationUnderlyingGroupAction
import Mathlib.GroupTheory.SemidirectProduct

/-!
DUB-17/18 -> residual modular Galois association -> character-to-weight-two
reduction -> removal of the Eisenstein exception -> actual cusp-evaluation
functional -> a native SL2(Z) cocycle with prescribed S and S*T values.
Adapted from anthropics/fermats-last-theorem,
revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_HeckeEis_existsUnique_coeffCocycles_sl2z_apply_S_ST_eq.lean.txt
(Apache-2.0; retained LICENSE and NOTICE).
The existing underlying group action replaces the external action
construction. Only the required existence statement is developed.
-/

namespace Dubon2026.SourceSL2Cocycle
noncomputable section
open scoped MatrixGroups
open Matrix.SpecialLinearGroup ModularGroup

variable {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
/-- The actual semidirect product for the original coefficient representation. -/
abbrev Ext (ρ : Representation K SL(2, ℤ) V) : Type _ :=
  Multiplicative V ⋊[representationUnderlyingGroupAction ρ] SL(2, ℤ)

variable (ρ : Representation K SL(2, ℤ) V) (x y : V)

/-- The lift of S with its prescribed original coefficient value. -/
noncomputable def sig : Ext ρ := ⟨Multiplicative.ofAdd x, S⟩

/-- The lift of S*T with its prescribed original coefficient value. -/
noncomputable def ups : Ext ρ := ⟨Multiplicative.ofAdd y, U⟩

/-- The lift of the actual central matrix minus one with zero coefficient. -/
noncomputable def cc : Ext ρ := SemidirectProduct.inr (-1)

variable {ρ x y}

/-- The prescribed S relation makes its actual lift square to the central lift. -/
theorem sig_sq (hx : x + ρ S x = 0) : sig ρ x * sig ρ x = cc ρ := by
  refine SemidirectProduct.ext ?_ ?_
  · rw [SemidirectProduct.mul_left]
    simp only [sig, cc, SemidirectProduct.left_inr, representationUnderlyingGroupAction_apply, ← ofAdd_add, hx, ofAdd_zero]
  · simpa [sig, cc] using S_mul_S

/-- The prescribed S*T relation makes its actual lift cube to the central lift. -/
theorem ups_cube (hy : y + ρ U y + ρ U (ρ U y) = 0) :
    ups ρ y * ups ρ y * ups ρ y = cc ρ := by
  refine SemidirectProduct.ext ?_ ?_
  · rw [SemidirectProduct.mul_left, SemidirectProduct.mul_left]
    simp only [ups, cc, SemidirectProduct.left_inr, SemidirectProduct.mul_right, map_mul,
      MulAut.mul_apply, representationUnderlyingGroupAction_apply]
    change Multiplicative.ofAdd (y + ρ U y + ρ U (ρ U y)) = 1
    rw [hy, ofAdd_zero]
  · simp only [ups, cc, SemidirectProduct.mul_right, SemidirectProduct.right_inr]
    rw [← U_pow_three, pow_succ, pow_two]

/-- The actual central lift has square one. -/
theorem cc_sq : cc ρ * cc ρ = 1 := by
  rw [cc, ← map_mul, neg_mul_neg, one_mul, map_one]

/-- The actual lifted S projects to S. -/
theorem rightHom_sig : SemidirectProduct.rightHom (sig ρ x) = S := rfl

/-- The actual lifted S*T projects to S*T. -/
theorem rightHom_ups : SemidirectProduct.rightHom (ups ρ y) = U := rfl

/-- The actual central lift projects to minus one. -/
theorem rightHom_cc : SemidirectProduct.rightHom (cc ρ) = -1 := rfl

/-- The original alternating word evaluated in the actual semidirect product. -/
noncomputable def ev (ρ : Representation K SL(2, ℤ) V) (x y : V) (l : List (Fin 2)) : Ext ρ :=
  (l.map fun a => sig ρ x * ups ρ y ^ ((a : ℕ) + 1)).prod

/-- The empty original alternating word evaluates to one. -/
theorem ev_nil : ev ρ x y [] = 1 := rfl

/-- Evaluation retains the first original alternating block. -/
theorem ev_cons (a : Fin 2) (l : List (Fin 2)) :
    ev ρ x y (a :: l) = sig ρ x * ups ρ y ^ ((a : ℕ) + 1) * ev ρ x y l := by
  simp [ev]

/-- Evaluation retains the final original alternating block. -/
theorem ev_append_singleton (l : List (Fin 2)) (a : Fin 2) :
    ev ρ x y (l ++ [a]) = ev ρ x y l * (sig ρ x * ups ρ y ^ ((a : ℕ) + 1)) := by
  simp [ev]

/-- An original alternating word projects to the actual positive matrix product up to sign. -/
theorem coe_rightHom_ev (l : List (Fin 2)) :
    ((SemidirectProduct.rightHom (ev ρ x y l) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = xProd l ∨
      ((SemidirectProduct.rightHom (ev ρ x y l) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = -xProd l := by
  induction l with
  | nil => exact Or.inl (by simp [ev_nil, xProd])
  | cons a l ih =>
    have hcons : xProd (a :: l) = X a * xProd l := by
      simp [xProd, List.map_cons, List.prod_cons]
    rw [ev_cons, map_mul, Matrix.SpecialLinearGroup.coe_mul, map_mul, map_pow, rightHom_sig,
      rightHom_ups, coe_S_mul_U_pow, hcons]
    rcases ih with h | h
    · right
      rw [h, neg_mul]
    · left
      rw [h, neg_mul_neg]

/-- The actual central lift exponent reduces modulo two. -/
theorem cc_pow_mod (n : ℕ) : cc ρ ^ n = cc ρ ^ (n % 2) := by
  conv_lhs => rw [← Nat.div_add_mod n 2, pow_add, pow_mul, pow_two, cc_sq, one_pow, one_mul]

/-- The actual central lift commutes with the lift of S. -/
theorem commute_cc_sig (hx : x + ρ S x = 0) : Commute (cc ρ) (sig ρ x) := by
  rw [← sig_sq hx]
  exact (Commute.refl _).mul_left (Commute.refl _)

/-- The actual central lift commutes with the lift of S*T. -/
theorem commute_cc_ups (hy : y + ρ U y + ρ U (ρ U y) = 0) : Commute (cc ρ) (ups ρ y) := by
  rw [← ups_cube hy]
  exact ((Commute.refl _).mul_left (Commute.refl _)).mul_left (Commute.refl _)

/-- The actual central lift commutes with every original alternating word. -/
theorem commute_cc_ev (hx : x + ρ S x = 0) (hy : y + ρ U y + ρ U (ρ U y) = 0) (l : List (Fin 2)) :
    Commute (cc ρ) (ev ρ x y l) := by
  induction l with
  | nil => exact Commute.one_right _
  | cons a l ih =>
    rw [ev_cons]
    exact (((commute_cc_sig hx).mul_right ((commute_cc_ups hy).pow_right _))).mul_right ih


end
end Dubon2026.SourceSL2Cocycle
