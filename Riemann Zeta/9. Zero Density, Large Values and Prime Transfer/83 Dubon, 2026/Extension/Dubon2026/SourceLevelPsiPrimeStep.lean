import Dubon2026.SourceLevelPsi
import Mathlib.Data.Nat.Factorization.Induction

/-! DUB-17/18 -> numerical modular genus -> composite j-map degree
-> exact relative degree in the conjugate-root induction. The existing
prime-power and coprime level formulas give the required ratio p or p+1;
positivity justifies cancellation of the lower-level degree.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_minpoly_jqNModC_map_eq_prod_slots.lean.
-/
namespace Dubon2026.SourceLevelProjective
noncomputable section

theorem dedekindPsi_pos {n : ℕ} (hn : n ≠ 0) : 0 < dedekindPsi n := by
  have h1 : (1 : ℕ) ∈ n.divisors.filter (fun d => Squarefree d) :=
    Finset.mem_filter.mpr ⟨Nat.one_mem_divisors.mpr hn, squarefree_one⟩
  have h2 : n / 1 ≤ ∑ d ∈ n.divisors with Squarefree d, n / d :=
    Finset.single_le_sum (f := fun d => n / d) (fun i _ => Nat.zero_le _) h1
  rw [Nat.div_one] at h2
  exact lt_of_lt_of_le (Nat.pos_of_ne_zero hn) h2

theorem dedekindPsi_prime (p : ℕ) (hp : p.Prime) : dedekindPsi p = p + 1 := by
  simpa using dedekindPsi_prime_pow p 1 hp one_ne_zero

theorem dedekindPsi_mul_prime_not_dvd {m p : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) :
    dedekindPsi (m * p) = dedekindPsi m * (p + 1) := by
  have hco : Nat.Coprime m p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm).symm
  rw [dedekindPsi_mul_of_coprime m p hco, dedekindPsi_prime p hp]

theorem dedekindPsi_mul_prime_dvd {m p : ℕ} (hm : m ≠ 0) (hp : p.Prime)
    (hpm : p ∣ m) : dedekindPsi (m * p) = dedekindPsi m * p := by
  obtain ⟨k, u, hpu, hmu⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm p hp.ne_one
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := by
    rcases k with - | k'
    · exfalso
      rw [hmu, pow_zero, one_mul] at hpm
      exact hpu hpm
    · exact ⟨k', rfl⟩
  subst hmu
  have hcou : ∀ j : ℕ, Nat.Coprime (p ^ j) u :=
    fun j => Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpu)
  have h1 : p ^ (k' + 1) * u * p = p ^ (k' + 2) * u := by ring
  rw [h1, dedekindPsi_mul_of_coprime _ u (hcou _),
    dedekindPsi_mul_of_coprime _ u (hcou _),
    dedekindPsi_prime_pow p (k' + 2) hp (Nat.succ_ne_zero _),
    dedekindPsi_prime_pow p (k' + 1) hp (Nat.succ_ne_zero _)]
  simp only [Nat.add_sub_cancel, show k' + 2 - 1 = k' + 1 by omega]
  ring

end
end Dubon2026.SourceLevelProjective
