import Dubon2026.SourceConjugateSlotTotal

/-! DUB-17/18 -> numerical modular genus -> all-level degree ->
explicit minimal-polynomial roots. Index the primitive triangular
conjugates in the orientation used by the actual Laurent product.
Native divisor inversion transfers the established count to this list.
-/
namespace Dubon2026.SourceFunctionField.ConjugateSlots
noncomputable section

/-- Primitive triangular indices (a,b), with a dividing N and 0 <= b < N/a. -/
def indices (N : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  N.divisors.sigma fun a => (Finset.range (N / a)).filter
    (fun b => Nat.gcd (Nat.gcd a b) (N / a) = 1)

theorem mem_indices (N a b : ℕ) :
    (⟨a, b⟩ : Σ _ : ℕ, ℕ) ∈ indices N ↔
      a ∣ N ∧ N ≠ 0 ∧ b < N / a ∧ Nat.gcd (Nat.gcd a b) (N / a) = 1 := by
  simp only [indices, Finset.mem_sigma, Nat.mem_divisors, Finset.mem_filter, Finset.mem_range]
  tauto

theorem card_indices (N : ℕ) (hN : N ≠ 0) :
    (indices N).card = SourceLevelProjective.dedekindPsi N := by
  rw [indices, Finset.card_sigma]
  have he : ∑ a ∈ N.divisors,
      ((Finset.range (N / a)).filter (fun b => Nat.gcd (Nat.gcd a b) (N / a) = 1)).card =
      ∑ a ∈ N.divisors, slotAt N (N / a) := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [slotAt, Nat.div_div_self (Nat.dvd_of_mem_divisors ha) hN]
  rw [he, Nat.sum_div_divisors]
  exact slots_eq_dedekindPsi N hN

theorem index_fst_ne_zero {N : ℕ} {s : Σ _ : ℕ, ℕ} (hs : s ∈ indices N) : s.1 ≠ 0 := by
  have h := (mem_indices N s.1 s.2).mp hs
  intro he
  have hd := h.1
  rw [he] at hd
  exact h.2.1 (Nat.eq_zero_of_zero_dvd hd)

theorem index_phase_lt {N : ℕ} {s : Σ _ : ℕ, ℕ} (hs : s ∈ indices N) : s.2 * s.1 < N := by
  have h := (mem_indices N s.1 s.2).mp hs
  calc
    s.2 * s.1 < N / s.1 * s.1 := Nat.mul_lt_mul_of_pos_right h.2.2.1
      (Nat.pos_of_ne_zero (index_fst_ne_zero hs))
    _ = N := Nat.div_mul_cancel h.1

end
end Dubon2026.SourceFunctionField.ConjugateSlots
