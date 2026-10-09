import Mathlib.RepresentationTheory.Invariants
import Mathlib.GroupTheory.Coset.Basic

/-! # Actual coset representatives act equally on genuine subgroup-fixed vectors -/

namespace Dubon2026

/-- The literal chosen representative of a genuine subgroup coset has the same action on every vector fixed by that subgroup. -/
theorem representation_fixed_coset_out {G K V : Type*} [Group G] [CommRing K]
    [AddCommGroup V] [Module K V] (ρ : Representation K G V) (L : Subgroup G)
    (x : V) (hx : ∀ l ∈ L, ρ l x = x) (a : G) :
    ρ (Quotient.out (QuotientGroup.mk a : G ⧸ L)) x = ρ a x := by
  let r := Quotient.out (QuotientGroup.mk a : G ⧸ L)
  have hr : r⁻¹ * a ∈ L :=
    QuotientGroup.leftRel_apply.mp (@Quotient.exact' _ (QuotientGroup.leftRel L) _ _
      (Quotient.out_eq' (QuotientGroup.mk a : G ⧸ L)))
  have he := congrArg (fun v => ρ r v) (hx (r⁻¹ * a) hr)
  change ρ r (ρ (r⁻¹ * a) x) = ρ r x at he
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] at he
  exact he.symm

end Dubon2026
