import Mathlib.RingTheory.IntegralDomain
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.GroupTheory.Coset.Card

/-! The fixed auxiliary quotient is the coefficient-prime quotient of
the actual cyclotomic group (Z/pZ)*. The subgroup and quotient are literal
power-image constructions, independent of the deformation. Their orders
prove the coprime-kernel input for descending the actual inertia action,
as needed for the local deformation rings serving Dubon Theorem 2.6. -/

namespace Dubon2026
noncomputable section

/-- The prime-to-coefficient part of the actual prime cyclotomic group,
defined as the image of its coefficient-primary power map. -/
def rationalPrimeTameCoefficientKernel (p q : ℕ) : Subgroup (ZMod p)ˣ :=
  (powMonoidHom (α := (ZMod p)ˣ) (q ^ (p - 1).factorization q)).range

/-- The actual fixed coefficient-prime tame quotient at the auxiliary prime. -/
abbrev RationalPrimeTameCoefficientQuotient (p q : ℕ) :=
  (ZMod p)ˣ ⧸ rationalPrimeTameCoefficientKernel p q

/-- The literal power-image subgroup has the complementary cyclotomic order. -/
theorem rationalPrimeTameCoefficientKernel_card (p q : ℕ) [Fact p.Prime] [Fact q.Prime] :
    Nat.card (rationalPrimeTameCoefficientKernel p q) =
      (p - 1) / q ^ (p - 1).factorization q := by
  obtain ⟨g, hg⟩ := (isCyclic_iff_exists_zpowers_eq_top (α := (ZMod p)ˣ)).mp inferInstance
  have hord : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_zpowers_eq_top hg, Nat.card_eq_fintype_card, ZMod.card_units]
  have he : rationalPrimeTameCoefficientKernel p q =
      Subgroup.zpowers (g ^ (q ^ (p - 1).factorization q)) := by
    unfold rationalPrimeTameCoefficientKernel
    rw [MonoidHom.range_eq_map, ← hg, MonoidHom.map_zpowers]
    rfl
  rw [he, Nat.card_zpowers, orderOf_pow_of_dvd
    (pow_ne_zero _ (Fact.out : q.Prime).ne_zero) (by rw [hord]; exact Nat.ordProj_dvd _ _), hord]

/-- The power-image kernel has order coprime to the coefficient prime. -/
theorem rationalPrimeTameCoefficientKernel_coprime (p q : ℕ) [Fact p.Prime] [Fact q.Prime] :
    q.Coprime (Nat.card (rationalPrimeTameCoefficientKernel p q)) := by
  rw [rationalPrimeTameCoefficientKernel_card]
  apply (Fact.out : q.Prime).coprime_iff_not_dvd.mpr
  intro h
  have hn : p - 1 ≠ 0 := Nat.sub_ne_zero_of_lt (Fact.out : p.Prime).one_lt
  apply Nat.pow_succ_factorization_not_dvd hn (Fact.out : q.Prime)
  rw [pow_succ]
  exact (Nat.mul_dvd_mul_left (q ^ (p - 1).factorization q) h).trans
    (dvd_of_eq (Nat.mul_div_cancel' (Nat.ordProj_dvd (p - 1) q)))

/-- The fixed quotient has exactly the full coefficient-primary part of
the actual cyclotomic group order. -/
theorem rationalPrimeTameCoefficientQuotient_card (p q : ℕ) [Fact p.Prime] [Fact q.Prime] :
    Nat.card (RationalPrimeTameCoefficientQuotient p q) = q ^ (p - 1).factorization q := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (rationalPrimeTameCoefficientKernel p q)
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by rw [Nat.card_eq_fintype_card, ZMod.card_units]
  rw [hcard, rationalPrimeTameCoefficientKernel_card] at h
  have hpos : (p - 1) / q ^ (p - 1).factorization q ≠ 0 := by
    rw [← rationalPrimeTameCoefficientKernel_card p q]
    exact Nat.card_pos.ne'
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hpos)
  exact h.symm.trans (Nat.mul_div_cancel' (Nat.ordProj_dvd (p - 1) q)).symm

/-- The selected congruence condition gives the required coefficient-power
divisibility of the order of the same fixed tame quotient. -/
theorem rationalPrimeTameCoefficientQuotient_card_dvd_of_congruence
    (p q level : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hmod : p ≡ 1 [MOD q ^ level]) :
    q ^ level ∣ Nat.card (RationalPrimeTameCoefficientQuotient p q) := by
  have hd : q ^ level ∣ p - 1 :=
    (Nat.modEq_iff_dvd' (Fact.out : p.Prime).one_lt.le).mp hmod.symm
  have hf := (Nat.factorization_le_iff_dvd (pow_ne_zero _ (Fact.out : q.Prime).ne_zero)
    (Nat.sub_ne_zero_of_lt (Fact.out : p.Prime).one_lt)).mpr hd
  have hle : level ≤ (p - 1).factorization q := by
    simpa only [(Fact.out : q.Prime).factorization_pow, Finsupp.single_eq_same] using hf q
  rw [rationalPrimeTameCoefficientQuotient_card]
  exact pow_dvd_pow q hle

end
end Dubon2026
