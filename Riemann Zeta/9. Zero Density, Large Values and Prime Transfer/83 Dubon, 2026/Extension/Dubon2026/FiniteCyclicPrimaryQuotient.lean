import Mathlib.RingTheory.IntegralDomain
import Dubon2026.FiniteCommutativePrimaryQuotient

/-! # The maximal coefficient-primary quotient of an original finite cyclic group

The source auxiliary parabolic quotient has one actual residue-unit group
per place. This adapts the repository's proved rational cyclotomic power-
image argument to those finite cyclic residue groups, preserving their
original elements. It supplies the Delta groups in DUB-17, not a replacement
abstract cyclic group or an assumed primary-quotient certificate.
-/

namespace Dubon2026

noncomputable section

variable (G : Type*) [CommGroup G] [Finite G]

variable [IsCyclic G]

omit [Finite G] in
/-- The power-image kernel has precisely the complementary group order. -/
theorem finiteCyclicPrimaryKernel_card (q : ℕ) [Fact q.Prime] :
    Nat.card (finiteCommutativePrimaryKernel G q) =
      Nat.card G / q ^ (Nat.card G).factorization q := by
  obtain ⟨g, hg⟩ := (isCyclic_iff_exists_zpowers_eq_top (α := G)).mp inferInstance
  have hord : orderOf g = Nat.card G := orderOf_eq_card_of_zpowers_eq_top hg
  have he : finiteCommutativePrimaryKernel G q =
      Subgroup.zpowers (g ^ (q ^ (Nat.card G).factorization q)) := by
    unfold finiteCommutativePrimaryKernel
    rw [MonoidHom.range_eq_map, ← hg, MonoidHom.map_zpowers]
    rfl
  rw [he, Nat.card_zpowers, orderOf_pow_of_dvd
    (pow_ne_zero _ (Fact.out : q.Prime).ne_zero) (by rw [hord]; exact Nat.ordProj_dvd _ _), hord]

/-- The actual kernel has order prime to the coefficient prime. -/
theorem finiteCyclicPrimaryKernel_coprime (q : ℕ) [Fact q.Prime] :
    q.Coprime (Nat.card (finiteCommutativePrimaryKernel G q)) := by
  rw [finiteCyclicPrimaryKernel_card]
  apply (Fact.out : q.Prime).coprime_iff_not_dvd.mpr
  intro h
  apply Nat.pow_succ_factorization_not_dvd (Nat.card_pos.ne' : Nat.card G ≠ 0)
    (Fact.out : q.Prime)
  rw [pow_succ]
  exact (Nat.mul_dvd_mul_left (q ^ (Nat.card G).factorization q) h).trans
    (dvd_of_eq (Nat.mul_div_cancel' (Nat.ordProj_dvd (Nat.card G) q)))

/-- The actual quotient has the full coefficient-primary part of the original group's order. -/
theorem finiteCyclicPrimaryQuotient_card (q : ℕ) [Fact q.Prime] :
    Nat.card (FiniteCommutativePrimaryQuotient G q) = q ^ (Nat.card G).factorization q := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (finiteCommutativePrimaryKernel G q)
  rw [finiteCyclicPrimaryKernel_card] at h
  have hpos : Nat.card G / q ^ (Nat.card G).factorization q ≠ 0 := by
    rw [← finiteCyclicPrimaryKernel_card G q]
    exact Nat.card_pos.ne'
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hpos)
  exact h.symm.trans (Nat.mul_div_cancel' (Nat.ordProj_dvd (Nat.card G) q)).symm

/-- Every required coefficient-prime power in the original order survives in the quotient. -/
theorem finiteCyclicPrimaryQuotient_card_dvd (q level : ℕ) [Fact q.Prime]
    (h : q ^ level ∣ Nat.card G) :
    q ^ level ∣ Nat.card (FiniteCommutativePrimaryQuotient G q) := by
  rw [finiteCyclicPrimaryQuotient_card]
  exact pow_dvd_pow q
    (((Fact.out : q.Prime).pow_dvd_iff_le_factorization Nat.card_pos.ne').mp h)

omit [Finite G] in
/-- Cyclicity descends along the actual quotient map. -/
theorem finiteCyclicPrimaryQuotient_isCyclic (q : ℕ) :
    IsCyclic (FiniteCommutativePrimaryQuotient G q) :=
  isCyclic_of_surjective (QuotientGroup.mk' (finiteCommutativePrimaryKernel G q))
    (QuotientGroup.mk'_surjective _)

end
end Dubon2026
