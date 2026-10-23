import Dubon2026.SourceEtaFirstCoefficient
import Dubon2026.SourceEtaFrobeniusPowers

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> exact
residue-field degree -> prime nonmembership. Removing the residue-prime
power from exponent 24 exposes a nonzero first eta coefficient, whereas
substitution by a different prime forces that coefficient to vanish.
This is the required eta/discriminant obstruction, including residue
characteristics two and three. It is not yet the full j nonmembership proof.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_StarBank_delta_pow_ne. The local power-series Frobenius
calculation and already proved eta truncation replace its general Laurent
Frobenius and repeated infinite-product foundations. -/
namespace Dubon2026.SourceFunctionField
noncomputable section

theorem etaProd_pow_ne (K : Type*) [CommRing K] {ℓ : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] (p : ℕ) [NeZero p] (hp : (p : K) ≠ 0) (hp1 : p ≠ 1) (γ : K) :
    HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ (24 * p) ≠
      HahnSeries.C γ * qExpand K p
        (HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) := by
  have hℓ : ℓ.Prime := Fact.out
  have hℓp : ¬ ℓ ∣ p := fun h => hp ((CharP.cast_eq_zero_iff K ℓ p).2 h)
  obtain ⟨c, m, hm, h24⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (show (24 : ℕ) ≠ 0 by decide) ℓ hℓ.one_lt.ne'
  intro h
  have key : (HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^
        (24 * p)).coeff ((ℓ ^ c : ℕ) : ℤ) =
      (HahnSeries.C γ * qExpand K p
        (HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24)).coeff
          ((ℓ ^ c : ℕ) : ℤ) := by
    rw [h]

  have hL : (HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^
        (24 * p)).coeff ((ℓ ^ c : ℕ) : ℤ) = -((m * p : ℕ) : K) := by
    have e1 : HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^
          (24 * p) =
        qExpand K (ℓ ^ c)
          (HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^
            (m * p)) := by
      rw [h24, show ℓ ^ c * m * p = ℓ ^ c * (m * p) by ring, pow_mul,
        integral_ofPowerSeries_pow_char_pow K ℓ etaProd c, map_pow]
    have e2 := qExpand_coeff_mul (R := K) (ℓ ^ c)
      (HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ (m * p)) 1
    rw [mul_one] at e2
    rw [e1, e2, coeff_one_eta_laurent_pow]

  have hR : (HahnSeries.C γ * qExpand K p
      (HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24)).coeff
        ((ℓ ^ c : ℕ) : ℤ) = 0 := by
    rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, qExpand_coeff_of_not_dvd, smul_zero]
    rw [Int.natCast_dvd_natCast]
    intro hd
    obtain ⟨k, -, hpk⟩ := (Nat.dvd_prime_pow hℓ).1 hd
    cases k with
    | zero => exact hp1 (by simpa using hpk)
    | succ k =>
      rw [hpk] at hℓp
      exact hℓp (dvd_pow_self ℓ (Nat.succ_ne_zero k))
  rw [hL, hR, neg_eq_zero] at key
  rcases (Nat.Prime.dvd_mul hℓ).1 ((CharP.cast_eq_zero_iff K ℓ (m * p)).1 key) with h1 | h2
  · exact hm h1
  · exact hℓp h2

end
end Dubon2026.SourceFunctionField
