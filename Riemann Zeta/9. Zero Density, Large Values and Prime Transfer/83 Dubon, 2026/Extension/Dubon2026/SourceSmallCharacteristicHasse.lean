import Dubon2026.SourceHasseCoefficientTransport

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> exact
residue-field degree -> prime j nonmembership. The literal integral Hasse
identity is transported to the residue field, and its proved nonzero leading
coefficient normalizes the identity to one. Characteristics two and three use
the actual E4 coefficient congruence. No Hasse polynomial input is assumed.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_StarBank_starK. The existing coefficient map replaces a new
Laurent ring homomorphism; the integral Hasse input is proved locally. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open HahnSeries PowerSeries

theorem eisenstein4_map_of_240 {K : Type*} [CommRing K] (h240 : (240 : K) = 0) :
    PowerSeries.map (Int.castRingHom K) eisenstein4 = 1 := by
  ext n
  rw [PowerSeries.coeff_map, eisenstein4, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [if_neg hn.ne', if_neg hn.ne']
    have h240Z : (Int.castRingHom K) (240 : ℤ) = 0 := by
      simp only [eq_intCast]; exact_mod_cast h240
    rw [map_mul, h240Z, zero_mul]

theorem jqModC_mul_etaBlock_of_240 {K : Type*} [CommRing K] (h240 : (240 : K) = 0) :
    jqModC K * (HahnSeries.single (1 : ℤ) (1 : K) * HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) = 1 := by
  have heis := eisenstein4_map_of_240 h240
  have hjnum : PowerSeries.map (Int.castRingHom K) jNum
      = PowerSeries.map (Int.castRingHom K) dedekindEtaUnitInv := by
    rw [jNum, map_mul, map_pow, heis, one_pow, one_mul]
  have heta : HahnSeries.ofPowerSeries ℤ K
        (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24
      = HahnSeries.ofPowerSeries ℤ K
        (PowerSeries.map (Int.castRingHom K) dedekindEtaUnit) := by
    rw [dedekindEtaUnit, map_pow, map_pow]
  rw [jqModC, hjnum, heta]
  have hinv : PowerSeries.map (Int.castRingHom K) dedekindEtaUnitInv
      * PowerSeries.map (Int.castRingHom K) dedekindEtaUnit = 1 := by
    rw [← map_mul, mul_comm, dedekindEtaUnit_mul_inv, map_one]
  calc HahnSeries.single (-1 : ℤ) (1 : K)
        * HahnSeries.ofPowerSeries ℤ K
            (PowerSeries.map (Int.castRingHom K) dedekindEtaUnitInv)
        * (HahnSeries.single (1 : ℤ) (1 : K)
            * HahnSeries.ofPowerSeries ℤ K
                (PowerSeries.map (Int.castRingHom K) dedekindEtaUnit))
      = (HahnSeries.single (-1 : ℤ) (1 : K) * HahnSeries.single (1 : ℤ) (1 : K))
        * (HahnSeries.ofPowerSeries ℤ K
              (PowerSeries.map (Int.castRingHom K) dedekindEtaUnitInv)
            * HahnSeries.ofPowerSeries ℤ K
              (PowerSeries.map (Int.castRingHom K) dedekindEtaUnit)) := by ring
    _ = HahnSeries.single (0 : ℤ) (1 : K)
        * HahnSeries.ofPowerSeries ℤ K (1 : PowerSeries K) := by
        rw [HahnSeries.single_mul_single, ← map_mul, hinv]; ring_nf
    _ = 1 := by rw [HahnSeries.single_zero_one, map_one, one_mul]


end
end Dubon2026.SourceFunctionField
