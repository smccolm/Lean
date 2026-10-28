import Mathlib

/-! DUB-17/18 -> original Gamma1 Picard/H1 -> Abel-Jacobi -> unitary
multiplier logarithms -> integral parabolic-character lifting -> actual
permutation cocycles and factorwise potentials. Adapted from
anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_Period_exists_parabolicHoms_int_castAddHom_comp_eq_of_forall_isOfFinOrder.
These explicit upstream identities support the integer lift; no lift is assumed. -/
namespace Dubon2026.SourceIntegralCharacterLift
noncomputable section
open Subgroup
section Crossed

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω] {A B : Type*} [AddCommGroup A]
  [AddCommGroup B]

/-- Pullback translation on functions of the actual group action. -/
def tr (g : G) (F : Ω → A) : Ω → A := fun x => F (g⁻¹ • x)

omit [AddCommGroup A] in
@[scoped simp] theorem tr_apply (g : G) (F : Ω → A) (x : Ω) : tr g F x = F (g⁻¹ • x) := rfl

omit [AddCommGroup A] in
theorem tr_one (F : Ω → A) : tr (1 : G) F = F := by
  funext x; simp [tr]

omit [AddCommGroup A] in
theorem tr_mul (g h : G) (F : Ω → A) : tr (g * h) F = tr g (tr h F) := by
  funext x; simp [tr, mul_smul, mul_inv_rev]

theorem tr_add (g : G) (F F' : Ω → A) : tr g (F + F') = tr g F + tr g F' := rfl

theorem tr_sub (g : G) (F F' : Ω → A) : tr g (F - F') = tr g F - tr g F' := rfl

theorem tr_neg (g : G) (F : Ω → A) : tr g (-F) = -tr g F := rfl

theorem tr_zero (g : G) : tr g (0 : Ω → A) = 0 := rfl

theorem tr_zsmul (g : G) (n : ℤ) (F : Ω → A) : tr g (n • F) = n • tr g F := rfl

/-- The actual additive crossed-cocycle identity for pullback translation. -/
def IsCrossed (c : G → Ω → A) : Prop := ∀ g h : G, c (g * h) = c g + tr g (c h)

namespace IsCrossed

variable {c c' : G → Ω → A}

theorem map_one (hc : IsCrossed c) : c 1 = 0 := by
  have h := hc 1 1
  rw [mul_one, tr_one] at h
  have : c 1 + c 1 = c 1 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel this

theorem map_inv (hc : IsCrossed c) (g : G) : c g⁻¹ = -tr g⁻¹ (c g) := by
  have h := hc g⁻¹ g
  rw [inv_mul_cancel, hc.map_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem map_inv_apply (hc : IsCrossed c) (g : G) (x : Ω) : c g⁻¹ x = -c g (g • x) := by
  rw [hc.map_inv]; simp

theorem conj_apply (hc : IsCrossed c) (g γ : G) (y : Ω) (hy : γ • y = y) :
    c (g * γ * g⁻¹) (g • y) = c γ y := by
  have hy' : γ⁻¹ • y = y := by
    conv_lhs => rw [← hy]
    rw [inv_smul_smul]
  rw [hc, hc, hc.map_inv]
  simp only [Pi.add_apply, tr_apply, Pi.neg_apply, inv_smul_smul, mul_inv_rev, inv_inv, mul_smul,
    hy']
  abel

theorem add (hc : IsCrossed c) (hc' : IsCrossed c') : IsCrossed (c + c') := by
  intro g h
  simp only [Pi.add_apply, hc g h, hc' g h, tr_add]
  abel

theorem neg (hc : IsCrossed c) : IsCrossed (-c) := by
  intro g h
  simp only [Pi.neg_apply, hc g h, tr_neg]
  abel

theorem sub (hc : IsCrossed c) (hc' : IsCrossed c') : IsCrossed (c - c') := by
  rw [sub_eq_add_neg]; exact hc.add hc'.neg

theorem zsmul (hc : IsCrossed c) (n : ℤ) : IsCrossed (n • c) := by
  intro g h
  simp only [Pi.smul_apply, hc g h, smul_add, tr_zsmul]

theorem map (hc : IsCrossed c) (π : A →+ B) : IsCrossed (fun g x => π (c g x)) := by
  intro g h
  funext x
  simp only [hc g h, Pi.add_apply, map_add, tr_apply]

end IsCrossed

/-- The actual coboundary of a coefficient function. -/
def cob (F : Ω → A) : G → Ω → A := fun g => F - tr g F

theorem cob_apply (F : Ω → A) (g : G) (x : Ω) : cob F g x = F x - F (g⁻¹ • x) := rfl

theorem isCrossed_cob (F : Ω → A) : IsCrossed (cob (G := G) F) := by
  intro g h
  simp only [cob, tr_sub, tr_mul]
  abel

theorem cob_apply_of_smul_eq (F : Ω → A) {γ : G} {y : Ω} (hy : γ • y = y) : cob F γ y = 0 := by
  have hy' : γ⁻¹ • y = y := by
    conv_lhs => rw [← hy]
    rw [inv_smul_smul]
  rw [cob_apply, hy', sub_self]

theorem cob_map (F : Ω → A) (π : A →+ B) (g : G) (x : Ω) :
    π (cob F g x) = cob (G := G) (fun y => π (F y)) g x := by
  simp [cob_apply]


end Crossed
end
end Dubon2026.SourceIntegralCharacterLift
