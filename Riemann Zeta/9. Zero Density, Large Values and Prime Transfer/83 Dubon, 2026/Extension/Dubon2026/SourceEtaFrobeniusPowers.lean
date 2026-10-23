import Dubon2026.SourceIntegralPowerSeriesFrobenius

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> exact
residue-field degree -> eta-product obstruction. The actual integral eta
product satisfies Frobenius substitution at every power of the residue
characteristic. This removes the characteristic factor from exponent 24
in the coefficient contradiction, including characteristics two and three. -/
namespace Dubon2026.SourceFunctionField
noncomputable section

theorem integral_ofPowerSeries_pow_char_pow (K : Type*) [CommRing K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (u : PowerSeries ℤ) (c : ℕ) :
    (HahnSeries.ofPowerSeries ℤ K (u.map (Int.castRingHom K))) ^ (p ^ c) =
      qExpand K (p ^ c) (HahnSeries.ofPowerSeries ℤ K (u.map (Int.castRingHom K))) := by
  induction c with
  | zero =>
    rw [qExpand_congr (pow_zero p), qExpand_one_apply, pow_zero, pow_one]
  | succ c ih =>
    calc (HahnSeries.ofPowerSeries ℤ K (u.map (Int.castRingHom K))) ^ (p ^ (c + 1))
        = ((HahnSeries.ofPowerSeries ℤ K (u.map (Int.castRingHom K))) ^ p) ^ (p ^ c) := by
            rw [← pow_mul, ← pow_succ']
      _ = qExpand K p ((HahnSeries.ofPowerSeries ℤ K (u.map (Int.castRingHom K))) ^ (p ^ c)) := by
            rw [integral_ofPowerSeries_pow_char, ← map_pow]
      _ = qExpand K (p ^ (c + 1)) (HahnSeries.ofPowerSeries ℤ K (u.map (Int.castRingHom K))) := by
            rw [ih, qExpand_qExpand, qExpand_congr (pow_succ' p c).symm]

end
end Dubon2026.SourceFunctionField
