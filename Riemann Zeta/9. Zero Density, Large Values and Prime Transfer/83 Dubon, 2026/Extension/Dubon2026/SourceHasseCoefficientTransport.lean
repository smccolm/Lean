import Dubon2026.SourceModularJBaseChange

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

theorem coeffMap_ofPowerSeries {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (u : PowerSeries R) :
    coeffMap f (HahnSeries.ofPowerSeries ℤ R u) = HahnSeries.ofPowerSeries ℤ S (PowerSeries.map f u) := by
  ext k
  rw [coeffMap_coeff]
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_map]
  · rw [ofPowerSeries_coeff_of_neg _ hk,
      ofPowerSeries_coeff_of_neg _ hk, map_zero]

theorem coeffMap_etaBlock (K : Type*) [CommRing K] :
    coeffMap (Int.castRingHom K)
        (HahnSeries.single (1 : ℤ) (1 : ℤ)
          * HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 24)
      = HahnSeries.single (1 : ℤ) (1 : K)
          * HahnSeries.ofPowerSeries ℤ K
              (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24 := by
  rw [map_mul, map_pow, coeffMap_single, coeffMap_ofPowerSeries, map_one]

theorem coeffMap_int_aeval_jqModC (K : Type*) [CommRing K] (G : Polynomial ℤ) :
    coeffMap (Int.castRingHom K) (Polynomial.aeval (jqModC ℤ) G)
      = Polynomial.aeval (jqModC K) (G.map (Int.castRingHom K)) := by
  have h := Polynomial.map_aeval_eq_aeval_map
    (R := ℤ) (S := LaurentSeries ℤ) (T := K) (U := LaurentSeries K)
    (φ := Int.castRingHom K) (ψ := coeffMap (Int.castRingHom K))
    (RingHom.ext_int _ _) G (jqModC ℤ)
  rw [h]
  change Polynomial.aeval ((jqModC ℤ).map (Int.castRingHom K)) _ = _
  rw [map_jqModC]


end
end Dubon2026.SourceFunctionField
