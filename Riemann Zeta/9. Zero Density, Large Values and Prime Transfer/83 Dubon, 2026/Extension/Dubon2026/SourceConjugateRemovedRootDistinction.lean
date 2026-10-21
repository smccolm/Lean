import Dubon2026.SourceConjugateSlotPrimeDescent

/-! DUB-17/18 -> numerical modular genus -> composite degree -> reduced
prime-step root construction. A primitive level-N index cannot coincide
with a twice-expanded preceding-level conjugate: Laurent leading terms
force both its entries to be divisible by p, contradicting primitivity.
This discharges the arithmetic distinction needed when removing the old
root from the actual prime relation. No field degree is assumed here.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_jqN_prime_not_mem_full.lean, rval_aux.
-/
namespace Dubon2026.SourceFunctionField.ConjugateSlots
noncomputable section
open PrimeDegreeAux
variable {K : Type*} [Field K]

theorem slotValue_prime_square_expansion (ζ : Kˣ) (p a b : ℕ)
    [NeZero p] [NeZero a] :
    qExpand K (p * p) (slotValue (ζ ^ (p * p)) a b) =
      slotValue ζ (p * a) (p * b) := by
  rw [slotValue_eq, slotValue_eq, qExpand_TS,
    TS_congr (show p * p * (a * a) = p * a * (p * a) by ring), ← pow_mul]
  congr 2
  ring

theorem slotValue_ne_prime_square_expansion {N m p a b α β : ℕ}
    [NeZero p] (hp : p.Prime) (hN : N = p * p * m)
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) N)
    (hs : (⟨a, b⟩ : Σ _ : ℕ, ℕ) ∈ indices N)
    (ht : (⟨α, β⟩ : Σ _ : ℕ, ℕ) ∈ indices m)
    (hpa : p ∣ N / a) :
    slotValue ζ a b ≠ qExpand K (p * p) (slotValue (ζ ^ (p * p)) α β) := by
  have ha := index_fst_ne_zero hs
  have hα := index_fst_ne_zero ht
  haveI : NeZero α := ⟨hα⟩
  rw [slotValue_prime_square_expansion]
  intro he
  have hb : (p * β) * (p * α) < N := by
    calc
      (p * β) * (p * α) = p * p * (β * α) := by ring
      _ < p * p * m := Nat.mul_lt_mul_of_pos_left (index_phase_lt ht) (Nat.mul_pos hp.pos hp.pos)
      _ = N := hN.symm
  obtain ⟨he1, he2⟩ := slotValue_injective hζ ha (NeZero.ne (p * α))
    (index_phase_lt hs) hb he
  have hbad : p ∣ Nat.gcd (Nat.gcd a b) (N / a) :=
    Nat.dvd_gcd (Nat.dvd_gcd ⟨α, he1⟩ ⟨β, he2⟩) hpa
  rw [((mem_indices N a b).mp hs).2.2.2] at hbad
  exact hp.ne_one (Nat.dvd_one.mp hbad)

end
end Dubon2026.SourceFunctionField.ConjugateSlots
