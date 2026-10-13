import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Tactic

/-! # Prime divisibility of actual cyclotomic residue orders

For DUB-17's odd-prime global H2 splitting step, a sufficiently large
prime-power conductor makes each prescribed away-prime residue degree
divisible by the auxiliary prime. This is the numerical input to the
actual cyclotomic extension construction, not a local-degree assumption.
-/
namespace Dubon2026
noncomputable section

/-- A sufficiently large prime-power modulus forces its prime to divide the actual multiplicative residue order. -/
theorem cyclotomicPrimePower_order_dvd_of_large
    (q p k : ℕ) (hq : q.Prime) (hp : 1 < p) (hqp : ¬ q ∣ p)
    (hlarge : p ^ (q - 1) - 1 < q ^ (k + 1)) :
    q ∣ orderOf (p : ZMod (q ^ (k + 1))) := by
  letI : NeZero q := ⟨hq.ne_zero⟩
  have hc : p.Coprime (q ^ (k + 1)) :=
    (hq.coprime_iff_not_dvd.mpr hqp).symm.pow_right _
  let u := ZMod.unitOfCoprime p hc
  have ho : orderOf u = orderOf (p : ZMod (q ^ (k + 1))) :=
    (orderOf_injective (Units.coeHom (ZMod (q ^ (k + 1)))) Units.coeHom_injective u).symm
  have hd : orderOf u ∣ q ^ k * (q - 1) := by
    simpa only [ZMod.card_units_eq_totient, Nat.totient_prime_pow_succ hq] using
      (orderOf_dvd_card (x := u))
  by_contra h
  have hqu : ¬ q ∣ orderOf u := by simpa only [ho] using h
  have hcop : (orderOf u).Coprime (q ^ k) :=
    (hq.coprime_iff_not_dvd.mpr hqu).symm.pow_right k
  have hd' : orderOf u ∣ q - 1 := hcop.dvd_of_dvd_mul_left hd
  have hu : u ^ (q - 1) = 1 := orderOf_dvd_iff_pow_eq_one.mp hd'
  have hz : (p : ZMod (q ^ (k + 1))) ^ (q - 1) = 1 := by
    exact congrArg Units.val hu
  have hpow : 1 < p ^ (q - 1) := one_lt_pow₀ hp (by have := hq.two_le; omega)
  have heq : 1 ≡ p ^ (q - 1) [MOD q ^ (k + 1)] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    simpa only [Nat.cast_one, Nat.cast_pow] using hz.symm
  have hdiv : q ^ (k + 1) ∣ p ^ (q - 1) - 1 :=
    (Nat.modEq_iff_dvd' hpow.le).mp heq
  exact (not_lt_of_ge (Nat.le_of_dvd (by omega) hdiv)) hlarge

/-- One conductor exponent works simultaneously for a prescribed finite family of away-primes. -/
theorem cyclotomicPrimePower_exists_residue_orders
    (q : ℕ) (hq : q.Prime) (S : Finset ℕ)
    (hS : ∀ p ∈ S, 1 < p ∧ ¬ q ∣ p) :
    ∃ k : ℕ, 1 ≤ k ∧ ∀ p ∈ S, q ∣ orderOf (p : ZMod (q ^ (k + 1))) := by
  let r := S.sup fun p => p ^ (q - 1) - 1
  have hr : r < q ^ r := Nat.lt_pow_self hq.one_lt
  refine ⟨r + 1, by omega, ?_⟩
  intro p hp
  apply cyclotomicPrimePower_order_dvd_of_large q p (r + 1) hq (hS p hp).1 (hS p hp).2
  exact lt_of_le_of_lt (Finset.le_sup (f := fun p => p ^ (q - 1) - 1) hp)
    (lt_of_lt_of_le hr (Nat.pow_le_pow_right hq.pos (by omega)))

end
end Dubon2026
