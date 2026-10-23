import Dubon2026.SourceJProductTruncation

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> exact
residue-field degree -> prime nonmembership -> eta-product obstruction.
The existing finite-truncation theorem evaluates the first eta coefficient;
no new infinite-product proof is needed. Its power coefficient survives
after the characteristic factor is removed from exponent 24 downstream. -/
namespace Dubon2026.SourceFunctionField
noncomputable section

theorem powerSeries_coeff_one_mul {R : Type*} [CommRing R] (φ ψ : PowerSeries R) :
    PowerSeries.coeff 1 (φ * ψ) =
      PowerSeries.coeff 0 φ * PowerSeries.coeff 1 ψ +
        PowerSeries.coeff 1 φ * PowerSeries.coeff 0 ψ := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_succ,
    Finset.Nat.antidiagonal_zero, Finset.sum_singleton]

theorem coeff_one_etaProd : PowerSeries.coeff 1 etaProd = -1 := by
  rw [PrimeDegreeAux.coeff_etaProd_eq_coeff_partialProd 1]
  norm_num [Finset.prod_range_succ, powerSeries_coeff_one_mul,
    PowerSeries.coeff_one, PowerSeries.coeff_X_pow]

theorem constantCoeff_etaProd_map (K : Type*) [CommRing K] :
    PowerSeries.constantCoeff (PowerSeries.map (Int.castRingHom K) etaProd) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_etaProd, map_one]

theorem coeff_one_etaProd_map (K : Type*) [CommRing K] :
    PowerSeries.coeff 1 (PowerSeries.map (Int.castRingHom K) etaProd) = -1 := by
  rw [PowerSeries.coeff_map, coeff_one_etaProd, map_neg, map_one]

theorem coeff_one_pow_of_shape {R : Type*} [CommRing R] (e : PowerSeries R)
    (h0 : PowerSeries.constantCoeff e = 1) (h1 : PowerSeries.coeff 1 e = -1) (N : ℕ) :
    PowerSeries.coeff 1 (e ^ N) = -(N : R) := by
  induction N with
  | zero => simp [PowerSeries.coeff_one]
  | succ N ih =>
    rw [pow_succ, powerSeries_coeff_one_mul, ih, h1,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, h0, one_pow,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h0]
    push_cast
    ring

theorem coeff_one_eta_laurent_pow (K : Type*) [CommRing K] (N : ℕ) :
    (HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ N).coeff 1 =
      -(N : K) := by
  rw [← map_pow]
  have h := HahnSeries.ofPowerSeries_apply_coeff (Γ := ℤ)
    (PowerSeries.map (Int.castRingHom K) etaProd ^ N) 1
  rw [Nat.cast_one] at h
  rw [h]
  exact coeff_one_pow_of_shape _ (constantCoeff_etaProd_map K) (coeff_one_etaProd_map K) N

end
end Dubon2026.SourceFunctionField
