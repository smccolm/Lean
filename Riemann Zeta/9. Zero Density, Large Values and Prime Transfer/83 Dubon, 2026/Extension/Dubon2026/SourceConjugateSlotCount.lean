import Dubon2026.SourceLevelPsi
import Mathlib.Data.Nat.Factorization.Induction

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

/-- Number of primitive conjugates with the specified lower diagonal entry. -/
def slotAt (n d : ℕ) : ℕ :=
  ((Finset.range d).filter fun b => Nat.gcd (Nat.gcd (n / d) b) d = 1).card

/-- Total number of primitive triangular conjugates at the original level. -/
def slots (n : ℕ) : ℕ := ∑ d ∈ n.divisors, slotAt n d

theorem slotCond_eq (x d b : ℕ) :
    Nat.gcd (Nat.gcd x b) d = Nat.gcd (Nat.gcd x d) b := by
  rw [Nat.gcd_assoc, Nat.gcd_comm b d, ← Nat.gcd_assoc]

theorem slotCond_iff (x d b : ℕ) :
    Nat.gcd (Nat.gcd x b) d = 1 ↔ Nat.Coprime (Nat.gcd x d) b := by
  rw [slotCond_eq]

theorem gcd_eq_of_modEq {a b n : ℕ} (h : a ≡ b [MOD n]) :
    Nat.gcd n a = Nat.gcd n b := by
  have h' : a % n = b % n := h
  rw [Nat.gcd_rec n a, Nat.gcd_rec n b, h']

theorem slotCond_mod_iff (x d b : ℕ) :
    Nat.Coprime (Nat.gcd x d) (b % d) ↔ Nat.Coprime (Nat.gcd x d) b := by
  unfold Nat.Coprime
  rw [gcd_eq_of_modEq ((Nat.mod_modEq b d).of_dvd (Nat.gcd_dvd_right x d))]

theorem slotAt_one (n : ℕ) : slotAt n 1 = 1 := by
  unfold slotAt
  simp [Nat.gcd_one_right]

theorem slotAt_self (n : ℕ) (hn : 0 < n) : slotAt n n = n := by
  unfold slotAt
  simp [Nat.div_self hn, Nat.gcd_one_left]

theorem slotAt_prime_pow_mid {p : ℕ} (hp : p.Prime) {i k : ℕ} (hi0 : 0 < i)
    (hik : i < k) : slotAt (p ^ k) (p ^ i) = Nat.totient (p ^ i) := by
  unfold slotAt
  rw [Nat.totient_eq_card_coprime]
  congr 1
  refine Finset.filter_congr fun b _ => ?_
  rw [slotCond_iff]
  constructor
  · intro h
    have hpg : p ∣ Nat.gcd (p ^ k / p ^ i) (p ^ i) := by
      refine Nat.dvd_gcd ?_ (dvd_pow_self p hi0.ne')
      rw [Nat.pow_div hik.le hp.pos]
      exact dvd_pow_self p (by omega)
    exact Nat.Coprime.pow_left i (Nat.Coprime.coprime_dvd_left hpg h)
  · intro h
    exact Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right _ _) h

theorem slots_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    slots (p ^ (k + 1)) = p ^ (k + 1) + p ^ k := by
  unfold slots
  rw [Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ]
  have hrest : ∀ x ∈ Finset.range (k + 1),
      slotAt (p ^ (k + 1)) (p ^ x) = Nat.totient (p ^ x) := by
    intro x hx
    rcases Nat.eq_zero_or_pos x with rfl | hx0
    · rw [pow_zero, slotAt_one, Nat.totient_one]
    · exact slotAt_prime_pow_mid hp hx0 (Finset.mem_range.mp hx)
  rw [Finset.sum_congr rfl hrest, slotAt_self _ (pow_pos hp.pos _),
    ← Nat.sum_divisors_prime_pow (f := Nat.totient) hp, Nat.sum_totient, Nat.add_comm]


end
end Dubon2026.SourceFunctionField.ConjugateSlots
