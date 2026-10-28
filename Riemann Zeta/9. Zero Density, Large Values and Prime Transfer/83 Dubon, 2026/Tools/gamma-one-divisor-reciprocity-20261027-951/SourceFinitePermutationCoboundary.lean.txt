import Mathlib

/-! DUB-17/18 -> original all-weight arithmetic association -> Gamma1 Picard/H1
-> Abel-Jacobi converse -> reciprocity -> integral-period membership of the
actual winding boundary sum. Finite permutation orbit sums construct the
integer potentials needed at the T, S and T-inverse-S coset transitions.
Adapted from the exact generic-subgroup Apache-2.0 primary proof recorded in
parabolic-integral-period-reuse-936. Native SameCycle and finite sums are
reused; no integer potential or coboundary solvability is assumed. -/
namespace Dubon2026.SourceParabolicEdgePeriod
noncomputable section
open scoped BigOperators

variable {α : Type*} [Fintype α]

theorem exists_eq_coboundary (f : Equiv.Perm α) (ψ : α → ℤ)
    (h : ∀ x n, 0 < n → (f ^ n) x = x → ∑ j ∈ Finset.range n, ψ ((f ^ j) x) = 0) :
    ∃ m : α → ℤ, ∀ x, ψ x = m (f x) - m x := by
  classical
  let S : Setoid α := Equiv.Perm.SameCycle.setoid f
  let rep : α → α := fun x => (Quotient.mk S x).out
  have hrep : ∀ x, f.SameCycle (rep x) x := fun x => Quotient.mk_out (s := S) x
  have hrepf : ∀ x, rep (f x) = rep x := by
    intro x
    simp only [rep]
    congr 1
    exact Quotient.sound (s := S) ((Equiv.Perm.sameCycle_apply_left).mpr (Equiv.Perm.SameCycle.refl f x))
  have hex : ∀ x, ∃ k : ℕ, (f ^ k) (rep x) = x := fun x => by
    obtain ⟨i, -, hi⟩ := (hrep x).exists_pow_eq'
    exact ⟨i, hi⟩
  let k : α → ℕ := fun x => Nat.find (hex x)
  have hk : ∀ x, (f ^ k x) (rep x) = x := fun x => Nat.find_spec (hex x)
  have hkmin : ∀ x j, j < k x → (f ^ j) (rep x) ≠ x := fun x j hj => Nat.find_min (hex x) hj
  refine ⟨fun x => ∑ j ∈ Finset.range (k x), ψ ((f ^ j) (rep x)), fun x => ?_⟩
  simp only [hrepf]

  have hle : k (f x) ≤ k x + 1 := by
    apply Nat.find_min'
    rw [pow_succ', Equiv.Perm.mul_apply, hrepf, hk]
  rcases Nat.lt_or_ge (k (f x)) (k x + 1) with hlt | hge
  ·

    have hk0 : k (f x) = 0 := by
      by_contra hne
      obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hne
      have h1 := hk (f x)
      rw [hrepf, hj, pow_succ', Equiv.Perm.mul_apply, f.injective.eq_iff] at h1
      exact hkmin x j (by omega) h1
    have hfx : f x = rep x := by simpa [hk0, hrepf] using (hk (f x)).symm

    have hper : (f ^ (k x + 1)) (rep x) = rep x := by
      rw [pow_succ', Equiv.Perm.mul_apply, hk, hfx]
    have hsum := h (rep x) (k x + 1) (Nat.succ_pos _) hper
    rw [Finset.sum_range_succ, hk] at hsum
    rw [hk0, Finset.sum_range_zero]
    linarith
  · have hkeq : k (f x) = k x + 1 := le_antisymm hle hge
    rw [hkeq, Finset.sum_range_succ, hk]
    ring

theorem sum_coboundary_mul (f : Equiv.Perm α) (a : α → ℂ) (m : α → ℤ)
    (ha : ∀ x, a x = m (f x) - m x)
    (X P : α → ℂ) (hX : ∀ x, X (f x) = X x + P x) :
    ∑ x, a x * X x = -∑ x, (m (f x) : ℂ) * P x := by
  have h1 : ∑ x, (m x : ℂ) * X x = ∑ x, (m (f x) : ℂ) * X (f x) :=
    (Equiv.sum_comp f (fun x => (m x : ℂ) * X x)).symm
  simp only [ha, sub_mul, Finset.sum_sub_distrib, h1, hX, mul_add, Finset.sum_add_distrib]
  ring


end
end Dubon2026.SourceParabolicEdgePeriod
