import Dubon2026.SourceConjugateSlotValues

/-! DUB-17/18 -> numerical modular genus -> composite field degree
-> indexed conjugate induction. Reduction of the phase modulo the smaller
diagonal entry preserves primitivity. The exact expansion and phase
identities identify the prime relation's finite branch with the requested
original conjugate. Existing gcd congruence avoids rebuilding CRT machinery.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_jqN_prime_not_mem_full.lean, rval_aux.
-/
namespace Dubon2026.SourceFunctionField.ConjugateSlots
noncomputable section
open PrimeDegreeAux

theorem index_prime_descent (a d p b : ℕ) [NeZero a] [NeZero d] [NeZero p]
    (hs : (⟨a, b⟩ : Σ _ : ℕ, ℕ) ∈ indices (a * d * p)) :
    (⟨a, b % d⟩ : Σ _ : ℕ, ℕ) ∈ indices (a * d) ∧ b / d < p := by
  have h := (mem_indices _ _ _).mp hs
  have hdiv : a * d * p / a = d * p := by
    rw [Nat.mul_assoc, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne a))]
  rw [hdiv] at h
  refine ⟨(mem_indices _ _ _).mpr ⟨dvd_mul_right a d, NeZero.ne _, ?_, ?_⟩,
    Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using h.2.2.1)⟩
  · rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne a))]
    exact Nat.mod_lt b (Nat.pos_of_ne_zero (NeZero.ne d))
  · rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne a)),
      slotCond_iff, slotCond_mod_iff, ← slotCond_iff]
    have hd : Nat.gcd (Nat.gcd a b) d ∣ Nat.gcd (Nat.gcd a b) (d * p) :=
      Nat.dvd_gcd (Nat.gcd_dvd_left _ _) ((Nat.gcd_dvd_right _ _).trans (dvd_mul_right d p))
    rw [h.2.2.2] at hd
    exact Nat.dvd_one.mp hd

variable {K : Type*} [Field K]

theorem slotValue_prime_seed (ζ : Kˣ) (a d p b : ℕ) [NeZero a] [NeZero p] :
    qExpand K p (slotValue (ζ ^ p) a (b % d)) =
      TS K (a * a * p) ((ζ ^ (b % d * a)) ^ p) := by
  rw [slotValue_eq, qExpand_TS, TS_congr (Nat.mul_comm p (a * a))]
  congr 1
  rw [← pow_mul, ← pow_mul, Nat.mul_comm p]

theorem slotValue_prime_branch (ζ : Kˣ) (a d b : ℕ) [NeZero a] :
    TS K (a * a) (ζ ^ (b % d * a) * (ζ ^ (a * d)) ^ (b / d)) =
      slotValue ζ a b := by
  rw [slotValue_eq, ← pow_mul, ← pow_add]
  congr 2
  calc
    b % d * a + a * d * (b / d) = (b % d + b / d * d) * a := by ring
    _ = b * a := by rw [Nat.mod_add_div']

end
end Dubon2026.SourceFunctionField.ConjugateSlots
