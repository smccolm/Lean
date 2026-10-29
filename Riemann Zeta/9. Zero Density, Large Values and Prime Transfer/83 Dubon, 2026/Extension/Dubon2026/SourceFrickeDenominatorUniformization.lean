import Dubon2026.SourceFrickeLevelIntegralRing
import Mathlib.Tactic

/-! DUB-17/18 -> original Gamma1 degree/genus -> uniform level-power
slash integrality. A nonzero common integer denominator, together with
coefficientwise level-power integrality, yields one level exponent for
all coefficients. Bezout and prime factorization discharge the arithmetic
uniformization step; existence of the common denominator is separate.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_exists_isIntegral_level_pow_mul_qExpansion_slash_fricke_coeff. -/
namespace Dubon2026.SourceFunctionField.IntegralFricke
noncomputable section

theorem dvd_pow_self_of_dvd_pow {g N b : ℕ} (hg : g ≠ 0) (hN : N ≠ 0) (h : g ∣ N ^ b) :
    g ∣ N ^ g := by
  rw [← Nat.factorization_le_iff_dvd hg (pow_ne_zero _ hN)]
  intro p
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  by_cases hp : p ∈ g.primeFactors
  · have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpg : p ∣ g := Nat.dvd_of_mem_primeFactors hp
    have hpN : p ∣ N := hpp.dvd_of_dvd_pow (hpg.trans h)
    have h1 : 1 ≤ N.factorization p := by
      rwa [Nat.Prime.dvd_iff_one_le_factorization hpp hN] at hpN
    calc g.factorization p ≤ g := (Nat.factorization_lt p hg).le
      _ ≤ g * N.factorization p := Nat.le_mul_of_pos_right _ h1
  · rw [Finsupp.notMem_support_iff.mp hp]
    exact Nat.zero_le _

theorem isIntegral_pow_mul_of_isIntegral_mul {N D b : ℕ} (hN : N ≠ 0) (hD : D ≠ 0) {x : ℂ}
    (h1 : IsIntegral ℤ ((N : ℂ) ^ b * x)) (h2 : IsIntegral ℤ ((D : ℂ) * x)) :
    IsIntegral ℤ ((N : ℂ) ^ D * x) := by
  set g : ℕ := Nat.gcd D (N ^ b) with hg
  have hg0 : g ≠ 0 := Nat.gcd_ne_zero_left hD

  have hbez : (g : ℤ) = (D : ℤ) * Nat.gcdA D (N ^ b) + ((N ^ b : ℕ) : ℤ) * Nat.gcdB D (N ^ b) :=
    Nat.gcd_eq_gcd_ab D (N ^ b)
  have hgx : IsIntegral ℤ ((g : ℂ) * x) := by
    have e : (g : ℂ) * x = (Nat.gcdA D (N ^ b) : ℂ) * ((D : ℂ) * x) +
        (Nat.gcdB D (N ^ b) : ℂ) * ((N : ℂ) ^ b * x) := by
      have := congr_arg (fun z : ℤ => (z : ℂ)) hbez
      push_cast at this
      rw [this]; ring
    rw [e]
    exact (((isIntegral_algebraMap : IsIntegral ℤ ((_ : ℤ) : ℂ))).mul h2).add (((isIntegral_algebraMap : IsIntegral ℤ ((_ : ℤ) : ℂ))).mul h1)

  have hgdvd : g ∣ N ^ D := by
    have h1' : g ∣ N ^ g := dvd_pow_self_of_dvd_pow hg0 hN (Nat.gcd_dvd_right _ _)
    have hle : g ≤ D := Nat.le_of_dvd (Nat.pos_of_ne_zero hD) (Nat.gcd_dvd_left _ _)
    exact h1'.trans (Nat.pow_dvd_pow N hle)
  obtain ⟨q, hq⟩ := hgdvd
  have e : (N : ℂ) ^ D * x = (q : ℂ) * ((g : ℂ) * x) := by
    rw [← mul_assoc, ← Nat.cast_mul, mul_comm q, ← hq]; push_cast; ring
  rw [e]
  exact (show IsIntegral ℤ (q : ℂ) from by exact_mod_cast (isIntegral_algebraMap : IsIntegral ℤ ((q : ℤ) : ℂ))).mul hgx

end
end Dubon2026.SourceFunctionField.IntegralFricke
