import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Tactic

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> higher symmetric-power
continuation -> residual modular Galois association -> parabolic Hecke
realization -> reverse period dimension bound -> finite Manin relations.
Selected from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_Period_six_mul_finrank_parabolicHoms_add_le_index.lean.
The pinned finite-action orbit count and dual annihilator dimension
theorems provide the required relation bound. External global options,
attribute removals and auxiliary framework commands are not imported.
-/
namespace Dubon2026.SourceManin
noncomputable section
open Module

section Orbits

variable {X : Type*} (σ : Equiv.Perm X)

/-- The actual orbits of the cyclic permutation used in the Manin relation. -/
abbrev Orb : Type _ := MulAction.orbitRel.Quotient (Subgroup.zpowers σ) X

/-- Send a point to its cyclic permutation orbit. -/
def orbQ (x : X) : Orb σ := Quotient.mk (MulAction.orbitRel (Subgroup.zpowers σ) X) x

theorem orbQ_surjective : Function.Surjective (orbQ σ) := by
  rintro ⟨x⟩; exact ⟨x, rfl⟩

theorem orbQ_apply_perm (x : X) : orbQ σ (σ x) = orbQ σ x := by
  apply Quotient.sound
  show σ x ∈ MulAction.orbit (Subgroup.zpowers σ) x
  exact ⟨⟨σ, Subgroup.mem_zpowers σ⟩, rfl⟩

theorem natCard_fixedBy_eq (τ : Equiv.Perm X) :
    Nat.card (MulAction.fixedBy X τ) = Nat.card {x // τ x = x} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp [MulAction.mem_fixedBy])

theorem natCard_fixedBy_one : Nat.card (MulAction.fixedBy X (1 : Equiv.Perm X)) = Nat.card X := by
  rw [natCard_fixedBy_eq]
  exact Nat.card_congr (Equiv.subtypeUnivEquiv fun x => by simp)

theorem sum_range_orderOf_natCard_fixedBy [Finite X] :
    ∑ i ∈ Finset.range (orderOf σ), Nat.card (MulAction.fixedBy X (σ ^ i)) =
      Nat.card (Orb σ) * orderOf σ := by
  classical
  letI := Fintype.ofFinite X
  have hfin : IsOfFinOrder σ := isOfFinOrder_of_finite σ
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group (Subgroup.zpowers σ) X
  rw [Fintype.card_zpowers] at hB
  rw [← Nat.card_eq_fintype_card] at hB
  rw [← Fin.sum_univ_eq_sum_range (fun i => Nat.card (MulAction.fixedBy X (σ ^ i))) (orderOf σ)]
  rw [← hB]
  rw [← Fintype.sum_equiv (finEquivZPowers hfin)
    (fun i : Fin (orderOf σ) => Nat.card (MulAction.fixedBy X (σ ^ (i : ℕ))))
    (fun a => Fintype.card (MulAction.fixedBy X a))]
  intro i
  rw [finEquivZPowers_apply, Nat.card_eq_fintype_card]
  rfl

theorem two_mul_natCard_orb [Finite X] (h2 : σ ^ 2 = 1) :
    2 * Nat.card (Orb σ) = Nat.card X + Nat.card {x // σ x = x} := by
  have hsum := sum_range_orderOf_natCard_fixedBy σ
  have hdvd : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2'
  ·
    have hσ : σ = 1 := orderOf_eq_one_iff.mp h1
    subst hσ
    rw [h1, Finset.sum_range_one, pow_zero, natCard_fixedBy_one, mul_one] at hsum
    rw [← natCard_fixedBy_eq, natCard_fixedBy_one, hsum]; ring
  · rw [h2', Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one, natCard_fixedBy_one,
      natCard_fixedBy_eq] at hsum
    omega

theorem three_mul_natCard_orb [Finite X] (h3 : σ ^ 3 = 1) :
    3 * Nat.card (Orb σ) = Nat.card X + 2 * Nat.card {x // σ x = x} := by
  have hsum := sum_range_orderOf_natCard_fixedBy σ
  have hdvd : orderOf σ ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3'
  · have hσ : σ = 1 := orderOf_eq_one_iff.mp h1
    subst hσ
    rw [h1, Finset.sum_range_one, pow_zero, natCard_fixedBy_one, mul_one] at hsum
    rw [← natCard_fixedBy_eq, natCard_fixedBy_one, hsum]; ring
  · have hsq : Nat.card (MulAction.fixedBy X (σ ^ 2)) = Nat.card {x // σ x = x} := by
      rw [natCard_fixedBy_eq]
      refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
      constructor
      · intro hx
        have h3x : (σ ^ 3) x = x := by rw [h3]; rfl
        calc σ x = σ ((σ ^ 2) x) := by rw [hx]
          _ = (σ ^ 3) x := by simp [pow_succ]
          _ = x := h3x
      · intro hx
        simp [sq, hx]
    rw [h3', Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one,
      natCard_fixedBy_one, natCard_fixedBy_eq, hsq] at hsum
    omega

end Orbits


end
end Dubon2026.SourceManin
