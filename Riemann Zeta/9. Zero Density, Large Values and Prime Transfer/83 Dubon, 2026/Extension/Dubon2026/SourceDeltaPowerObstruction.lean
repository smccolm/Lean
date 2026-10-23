import Dubon2026.SourceEtaPowerObstruction

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

theorem delta_pow_ne (K : Type*) [CommRing K] {ℓ : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] {p : ℕ} [Fact p.Prime] (hpℓ : p ≠ ℓ) (γ : K) :
    (HahnSeries.single (1 : ℤ) (1 : K) *
        HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) ^ p ≠
      HahnSeries.C γ * qExpand K p (HahnSeries.single (1 : ℤ) (1 : K) *
        HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) := by
  have hp : p.Prime := Fact.out
  have hℓ : ℓ.Prime := Fact.out
  have hpK : (p : K) ≠ 0 := fun h0 =>
    hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hp).1 ((CharP.cast_eq_zero_iff K ℓ p).1 h0)).symm
  intro h
  apply etaProd_pow_ne K p hpK hp.ne_one γ
  have hu : HahnSeries.single (-(p : ℤ)) (1 : K) * HahnSeries.single (p : ℤ) (1 : K) = 1 := by
    rw [HahnSeries.single_mul_single, neg_add_cancel, mul_one, HahnSeries.single_zero_one]
  have hsp : HahnSeries.single (1 : ℤ) (1 : K) ^ p = HahnSeries.single (p : ℤ) (1 : K) := by
    rw [HahnSeries.single_pow, one_pow, nsmul_eq_mul, mul_one]
  calc HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ (24 * p)
      = HahnSeries.single (-(p : ℤ)) (1 : K) * (HahnSeries.single (1 : ℤ) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) ^ p := by
        rw [mul_pow, hsp, ← mul_assoc, hu, one_mul, pow_mul]
    _ = HahnSeries.single (-(p : ℤ)) (1 : K) * (HahnSeries.C γ * qExpand K p
          (HahnSeries.single (1 : ℤ) (1 : K) *
            HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24)) := by
        rw [h]
    _ = HahnSeries.C γ * qExpand K p
          (HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) := by
        rw [map_mul, qExpand_single, mul_one, mul_left_comm,
          ← mul_assoc (HahnSeries.single (-(p : ℤ)) (1 : K)), hu, one_mul]

end
end Dubon2026.SourceFunctionField
