import Dubon2026.SourceConjugateSlotCRT

/-! DUB-17/18 -> numerical modular genus -> general composite j-map
degree -> explicit minimal-polynomial conjugates. These counts identify
the primitive triangular conjugate list with the already proved level
factor dedekindPsi. The list is needed to prove the degree and divisor
generation by induction; no polynomial or geometric degree is assumed.
Selected from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_minpoly_jqNModC_map_eq_prod_slots.lean.
-/
namespace Dubon2026.SourceFunctionField.ConjugateSlots
noncomputable section
open SourceLevelProjective

theorem gcd_mul_left_of_dvd (M M' : ℕ) (hco : Nat.Coprime M M') {e₁ e₂ : ℕ}
    (he₁ : e₁ ∣ M) (he₂ : e₂ ∣ M') : Nat.gcd (e₁ * e₂) M = e₁ := by
  rw [Nat.mul_comm e₁ e₂]
  exact Nat.gcd_mul_of_coprime_of_dvd (hco.symm.coprime_dvd_left he₂) he₁

theorem gcd_mul_right_of_dvd (M M' : ℕ) (hco : Nat.Coprime M M') {e₁ e₂ : ℕ}
    (he₁ : e₁ ∣ M) (he₂ : e₂ ∣ M') : Nat.gcd (e₁ * e₂) M' = e₂ :=
  Nat.gcd_mul_of_coprime_of_dvd (hco.coprime_dvd_left he₁) he₂

theorem slots_mul (M M' : ℕ) (hM : M ≠ 0) (hM' : M' ≠ 0)
    (hco : Nat.Coprime M M') : slots (M * M') = slots M * slots M' := by
  unfold slots
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_bij' (fun d _ => (Nat.gcd d M, Nat.gcd d M')) (fun q _ => q.1 * q.2)
    ?_ ?_ ?_ ?_ ?_
  · intro d hd
    exact Finset.mem_product.mpr
      ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right d M, hM⟩,
        Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right d M', hM'⟩⟩
  · intro q hq
    obtain ⟨hq₁, hq₂⟩ := Finset.mem_product.mp hq
    exact Nat.mem_divisors.mpr
      ⟨Nat.mul_dvd_mul (Nat.mem_divisors.mp hq₁).1 (Nat.mem_divisors.mp hq₂).1,
        Nat.mul_ne_zero hM hM'⟩
  · intro d hd
    exact (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hco).mpr (Nat.mem_divisors.mp hd).1
  · intro q hq
    obtain ⟨hq₁, hq₂⟩ := Finset.mem_product.mp hq
    exact Prod.ext
      (gcd_mul_left_of_dvd M M' hco (Nat.mem_divisors.mp hq₁).1 (Nat.mem_divisors.mp hq₂).1)
      (gcd_mul_right_of_dvd M M' hco (Nat.mem_divisors.mp hq₁).1 (Nat.mem_divisors.mp hq₂).1)
  · intro d hd
    have hsplit : Nat.gcd d M * Nat.gcd d M' = d :=
      (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hco).mpr (Nat.mem_divisors.mp hd).1
    conv_lhs => rw [← hsplit]
    exact slotAt_mul M M' (Nat.gcd d M) (Nat.gcd d M') hM hM' hco
      (Nat.gcd_dvd_right d M) (Nat.gcd_dvd_right d M')

theorem slots_eq_dedekindPsi : ∀ n : ℕ, n ≠ 0 → slots n = SourceLevelProjective.dedekindPsi n := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    intro _
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [slots_prime_pow hp j, SourceLevelProjective.dedekindPsi_prime_pow p (j + 1) hp (by omega)]
    simp only [Nat.add_sub_cancel]
  | zero => exact fun h0 => absurd rfl h0
  | one =>
    intro _
    rw [SourceLevelProjective.dedekindPsi_one]
    unfold slots
    rw [Nat.divisors_one, Finset.sum_singleton]
    exact slotAt_one 1
  | coprime a b ha hb hab iha ihb =>
    intro _
    rw [slots_mul a b (by omega) (by omega) hab, iha (by omega), ihb (by omega),
      SourceLevelProjective.dedekindPsi_mul_of_coprime a b hab]


end
end Dubon2026.SourceFunctionField.ConjugateSlots
