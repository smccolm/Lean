import Dubon2026.CyclotomicPrimePowerResidueOrder
import Mathlib.Algebra.GCDMonoid.Basic

/-! # Prescribed prime-power divisibility of original cyclotomic residue orders

The exact cyclic residue-order formula and a finite numerical bound provide
the local-degree input for killing odd-primary global unit cohomology. This
extends only the prime-power bound needed for DUB-17's full-order classes.
-/
namespace Dubon2026
noncomputable section

/-- A sufficiently large prime-power conductor forces any prescribed power
of its prime to divide the actual multiplicative residue order. -/
theorem cyclotomicPrimePower_higher_order_dvd_of_large
    (q p k r : ℕ) (hq : q.Prime) (hp : 1 < p) (hqp : ¬ q ∣ p)
    (hlarge : p ^ (q ^ r * (q - 1)) - 1 < q ^ (k + 1)) :
    q ^ (r + 1) ∣ orderOf (p : ZMod (q ^ (k + 1))) := by
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
  have hqu : ¬ q ^ (r + 1) ∣ orderOf u := by simpa only [ho] using h
  obtain ⟨i, _, hi⟩ := (Nat.dvd_prime_pow hq).mp (Nat.gcd_dvd_right (orderOf u) (q ^ k))
  have hir : i ≤ r := by
    by_contra hle
    apply hqu
    exact (pow_dvd_pow q (by omega : r + 1 ≤ i)).trans
      (hi ▸ Nat.gcd_dvd_left (orderOf u) (q ^ k))
  have hd' : orderOf u ∣ q ^ r * (q - 1) := by
    have h := dvd_gcd_mul_of_dvd_mul hd
    change orderOf u ∣ (orderOf u).gcd (q ^ k) * (q - 1) at h
    rw [hi] at h
    exact h.trans (mul_dvd_mul (pow_dvd_pow q hir) (dvd_refl (q - 1)))
  have hu : u ^ (q ^ r * (q - 1)) = 1 := orderOf_dvd_iff_pow_eq_one.mp hd'
  have hz : (p : ZMod (q ^ (k + 1))) ^ (q ^ r * (q - 1)) = 1 := congrArg Units.val hu
  have hpow : 1 < p ^ (q ^ r * (q - 1)) :=
    one_lt_pow₀ hp (mul_ne_zero (pow_ne_zero r hq.ne_zero) (by have := hq.two_le; omega))
  have heq : 1 ≡ p ^ (q ^ r * (q - 1)) [MOD q ^ (k + 1)] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    simpa only [Nat.cast_one, Nat.cast_pow] using hz.symm
  have hdiv : q ^ (k + 1) ∣ p ^ (q ^ r * (q - 1)) - 1 :=
    (Nat.modEq_iff_dvd' hpow.le).mp heq
  exact (not_lt_of_ge (Nat.le_of_dvd (by omega) hdiv)) hlarge

end
end Dubon2026
