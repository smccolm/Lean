import Tao2026.Intervals

/-!
# Multiples in a consecutive interval

The sharp elementary `H / p + 1` bound is the counting input used in Tao's
coefficient-product estimate in Lemma 3.2.
-/

namespace Tao2026

def intervalMultiples (N H p : ℕ) : Finset ℕ :=
  (consecutiveInterval N H).filter (p ∣ ·)

theorem mem_intervalMultiples {N H p k : ℕ} :
    k ∈ intervalMultiples N H p ↔
      N < k ∧ k ≤ N + H ∧ p ∣ k := by
  simp [intervalMultiples, consecutiveInterval, and_assoc]

theorem card_intervalMultiples_le (N H p : ℕ) (hp : 0 < p) :
    (intervalMultiples N H p).card ≤ H / p + 1 := by
  let quotientImage := (intervalMultiples N H p).image (· / p)
  have hinj : Set.InjOn (fun k : ℕ => k / p) (intervalMultiples N H p) := by
    intro a ha b hb hab
    have hpa : p ∣ a := (mem_intervalMultiples.mp ha).2.2
    have hpb : p ∣ b := (mem_intervalMultiples.mp hb).2.2
    change a / p = b / p at hab
    calc
      a = a / p * p := (Nat.div_mul_cancel hpa).symm
      _ = b / p * p := congrArg (· * p) hab
      _ = b := Nat.div_mul_cancel hpb
  have hcardImage : quotientImage.card = (intervalMultiples N H p).card := by
    exact Finset.card_image_iff.mpr hinj
  have hsubset : quotientImage ⊆ Finset.Ioc (N / p) ((N + H) / p) := by
    intro q hq
    change q ∈ (intervalMultiples N H p).image (· / p) at hq
    rw [Finset.mem_image] at hq
    rcases hq with ⟨k, hk, rfl⟩
    have hk' := mem_intervalMultiples.mp hk
    rw [Finset.mem_Ioc]
    constructor
    · apply (Nat.div_lt_iff_lt_mul hp).2
      rw [Nat.div_mul_cancel hk'.2.2]
      exact hk'.1
    · exact Nat.div_le_div_right hk'.2.1
  have hadd : (N + H) / p ≤ N / p + H / p + 1 := by
    rw [Nat.add_div hp]
    split <;> omega
  calc
    (intervalMultiples N H p).card = quotientImage.card := hcardImage.symm
    _ ≤ (Finset.Ioc (N / p) ((N + H) / p)).card :=
      Finset.card_le_card hsubset
    _ = (N + H) / p - N / p := by simp
    _ ≤ H / p + 1 := by
      rw [Nat.sub_le_iff_le_add]
      simpa [add_comm, add_left_comm, add_assoc] using hadd

/-- At start zero, the count is the exact quotient rather than merely the
general `H / p + 1` upper bound. -/
theorem card_intervalMultiples_zero (H p : ℕ) :
    (intervalMultiples 0 H p).card = H / p := by
  simpa [intervalMultiples, consecutiveInterval] using
    Nat.Ioc_filter_dvd_card_eq_div H p

end Tao2026
