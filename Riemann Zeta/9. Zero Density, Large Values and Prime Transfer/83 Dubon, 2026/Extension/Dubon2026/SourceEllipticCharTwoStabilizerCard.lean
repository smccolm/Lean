import Dubon2026.SourceEllipticCharTwoRootCounts

/-! Exact cardinality of the actual characteristic-two exceptional
stabilizer, needed by the DUB-17/18 order-twelve quotient and wild census.
Native dependent-sum cardinality avoids choosing Artin--Schreier roots.
The coordinate equations come from the attributed frozen source; the
curve itself is the existing Mathlib.ofJ0. -/
namespace Dubon2026.SourceEllipticCharTwo
open WeierstrassCurve
noncomputable section
variable {K : Type*} [Field K] [CharP K 2] [IsAlgClosed K]

theorem char_two_stabilizer_card :
    Nat.card (MulAction.stabilizer (VariableChange K) (ofJ0 K)) = 24 := by
  classical
  let U := {u : Kˣ // (u : K) ^ 3 = 1}
  let S := {s : K // s ^ 4 = s}
  let T (s : S) := {t : K // t ^ 2 + t = s.val ^ 6}
  haveI : Finite S := Nat.finite_of_card_ne_zero
    (show Nat.card S ≠ 0 by rw [natCard_pow_four_eq_self]; norm_num)
  letI : Fintype S := Fintype.ofFinite S
  haveI (s : S) : Finite (T s) := Nat.finite_of_card_ne_zero
    (show Nat.card (T s) ≠ 0 by rw [natCard_artinSchreier]; norm_num)
  let e : MulAction.stabilizer (VariableChange K) (ofJ0 K) ≃ U × (Σ s : S, T s) :=
    { toFun := fun γ =>
        have h := (stabilizer_coordinates_iff γ.val).mp (MulAction.mem_stabilizer_iff.mp γ.property)
        (⟨γ.val.u, h.1⟩, ⟨⟨γ.val.s, h.2.2.1⟩, ⟨γ.val.t, h.2.2.2⟩⟩)
      invFun := fun x => ⟨⟨x.1.val, x.2.1.val ^ 2, x.2.1.val, x.2.2.val⟩,
        MulAction.mem_stabilizer_iff.mpr ((stabilizer_coordinates_iff _).mpr
          ⟨x.1.property, rfl, x.2.1.property, x.2.2.property⟩)⟩
      left_inv := fun γ => by
        have h := (stabilizer_coordinates_iff γ.val).mp (MulAction.mem_stabilizer_iff.mp γ.property)
        exact Subtype.ext (VariableChange.ext rfl h.2.1.symm rfl rfl)
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_prod, natCard_units_cube_eq_one, Nat.card_sigma]
  simp only [T, S, natCard_artinSchreier, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card, natCard_pow_four_eq_self]
end
end Dubon2026.SourceEllipticCharTwo
